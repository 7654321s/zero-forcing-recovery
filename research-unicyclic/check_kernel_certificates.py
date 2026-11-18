"""Generate and compile the finite certificate proofs with the Lean kernel."""

import argparse
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
import sys
import time

from check_cycle_modules import executable, read_axioms


HERE = Path(__file__).resolve().parent
REPO = HERE.parent
PYTHON = [sys.executable, '-X', 'utf8', '-B']
COMMON_MODULES = ('CertificateDeadline', 'MaskForcing', 'FiniteWitness', 'NumberedGraph',
                  'FiniteExtensions', 'FastMaskStep', 'ReplayForcing')
FAMILIES = {
    'fork': ('generate_fork_lean.py', 'ForkCertificates', 'Fork', ()),
    'padding': ('generate_padding_lean.py', 'PathPaddingCertificates', 'Padding', ('PaddingSpecial',)),
}


def compile_module(name, source_dir, base, lake, lean, output):
    started = time.monotonic()
    source = source_dir / f'{name}.lean'
    log = output / f'{name}.log'
    temporary = output / 'temp' / name
    temporary.mkdir(parents=True)
    env = os.environ.copy()
    env.update(TEMP=str(temporary), TMP=str(temporary), TMPDIR=str(temporary),
               PATH=str(lake.parent) + os.pathsep + env['PATH'], LEAN_PATH=str(output))
    command = [str(lake), 'env', str(lean), '-DwarningAsError=true', '-R', str(source_dir),
               '-o', str(output / f'{name}.olean'), str(source)]
    with log.open('xb') as stream:
        result = subprocess.run(command, cwd=base, env=env, stdout=stream,
                                stderr=subprocess.STDOUT)
    contents = log.read_text(encoding='utf-8', errors='replace')
    if result.returncode:
        raise RuntimeError(f'{name} failed. Full log at {log}\n{contents[:5000]}')
    return {'module': name, 'source_sha256': sha256(source.read_bytes()).hexdigest(),
            'axioms': read_axioms(contents), 'seconds': round(time.monotonic() - started, 3)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=REPO, help='built pinned checkout')
    parser.add_argument('--lean-bin', type=Path, help='directory containing lake and lean')
    parser.add_argument('--jobs', type=int, default=2)
    parser.add_argument('--batch-size', type=int, default=30)
    parser.add_argument('--family', choices=['both', *FAMILIES], default='both')
    args = parser.parse_args()
    if args.jobs <= 0 or args.batch_size <= 0:
        parser.error('jobs and batch size must be positive')
    base = args.base.resolve()
    lake = executable('lake', args.lean_bin)
    lean = executable('lean', args.lean_bin)
    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S_%fZ')
    session = REPO / 'build' / 'kernel-checks' / stamp
    subprocess.run([*PYTHON, str(HERE / 'prepare_reproduction.py'), '--output', str(session)],
                   check=True)
    work = session / HERE.name
    output = session / 'lean'
    output.mkdir()

    print(f'Lean outputs at {output}', flush=True)
    compiled = [compile_module(name, work, base, lake, lean, output) for name in COMMON_MODULES]
    totals = {}
    selected = list(FAMILIES) if args.family == 'both' else [args.family]
    for name in selected:
        generator, core_module, prefix, extra = FAMILIES[name]
        generated = session / f'{name}-proofs'
        subprocess.run([*PYTHON, str(work / generator), '--output', str(generated),
                        '--batch-size', str(args.batch_size)], check=True)
        compiled.append(compile_module(core_module, work, base, lake, lean, output))
        batches = sorted(path.stem for path in generated.glob(f'{prefix}Batch*.lean'))
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            jobs = [pool.submit(compile_module, module, generated, base, lake, lean, output)
                    for module in [*extra, *batches]]
            try:
                for job in jobs:
                    batch = job.result()
                    compiled.append(batch)
                    print(f'Checked {batch["module"]} ({batch["seconds"]} s)', flush=True)
            except BaseException:
                for job in jobs:
                    job.cancel()
                raise
        compiled.append(compile_module(f'{prefix}Coverage', generated, base, lake, lean, output))
        print(f'Checked complete {name} coverage', flush=True)
        totals[name] = {'batches': len(batches)}
        if name == 'fork':
            totals[name]['certificates'] = 670
        else:
            totals[name].update(certificates=5087, original_layouts=4050, marked_cases=10229,
                                exact_length_exceptions=1)
    result = {'status': 'passed', 'families': totals, 'compiled': compiled}
    summary = session / 'summary.json'
    summary.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8', newline='\n')
    print(summary, flush=True)


if __name__ == '__main__':
    main()
