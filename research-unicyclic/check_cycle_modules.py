"""Compile the unicyclic research modules against a built checkout."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess


ROOT = Path(__file__).resolve().parent
MODULES = ('CycleSeeds', 'CycleArcs', 'CyclePacking', 'CycleSupport',
           'CertificateDeadline', 'AttachmentProjection', 'AttachmentTiming', 'AttachmentRecovery',
           'SubdivisionProjection', 'SubdivisionCertificate')
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def executable(name, directory):
    if directory is None:
        command = shutil.which(name)
        if command is None:
            raise FileNotFoundError(f'{name} is not on PATH')
        return Path(command).absolute()
    suffix = '.exe' if os.name == 'nt' else ''
    return directory.resolve() / (name + suffix)


def read_axioms(output):
    lists = re.findall(r'depends on axioms:\s*\[([^]]*)\]', output)
    if not lists and 'does not depend on any axioms' not in output:
        raise ValueError('Lean module did not report an axiom audit')
    found = {axiom.strip() for group in lists for axiom in group.split(',') if axiom.strip()}
    if found - ALLOWED_AXIOMS:
        raise ValueError(f'Unexpected Lean axioms: {sorted(found - ALLOWED_AXIOMS)}')
    return sorted(found)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, required=True)
    parser.add_argument('--bin', type=Path, help='directory containing lake and lean')
    parser.add_argument('modules', nargs='+', choices=MODULES)
    args = parser.parse_args()
    lake = executable('lake', args.bin)
    lean = executable('lean', args.bin)
    assert shutil.disk_usage(ROOT).free > 2**30 and os.access(ROOT, os.W_OK)
    assert (args.base / '.lake/build/lib/lean/formalization-targets.olean').is_file()
    assert (args.base / 'lean-toolchain').read_text(encoding='utf-8').strip().endswith('v4.35.0')
    manifest = json.loads((args.base / 'lake-manifest.json').read_text(encoding='utf-8'))
    mathlib = next(package for package in manifest['packages'] if package['name'] == 'mathlib')
    assert mathlib['rev'] == '56a005855ea17e0b0958f73ec801ae140b0a1679'
    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S_%fZ')
    run = ROOT / 'build-runs' / stamp
    run.mkdir(parents=True, exist_ok=False)
    print(run, flush=True)
    temporary = run / 'temp'
    temporary.mkdir()
    env = os.environ.copy()
    env.update(TEMP=str(temporary), TMP=str(temporary), TMPDIR=str(temporary),
               PATH=str(lake.parent) + os.pathsep + env['PATH'],
               LEAN_PATH=str(run))
    records = []
    for name in args.modules:
        source = ROOT / (name + '.lean')
        command = [str(lake), 'env', str(lean),
                   '-DwarningAsError=true', '-R', str(ROOT), '-o', str(run / (name + '.olean')),
                   str(source)]
        log = run / (name + '.log')
        with log.open('x', encoding='utf-8') as output:
            result = subprocess.run(command, cwd=args.base, env=env, stdout=output,
                                    stderr=subprocess.STDOUT)
        contents = log.read_text(encoding='utf-8', errors='replace')
        print(contents, end='', flush=True)
        record = {'module': name, 'exit_code': result.returncode,
                  'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest()}
        if result.returncode == 0:
            record['axioms'] = read_axioms(contents)
        records.append(record)
        if result.returncode:
            break
    (run / 'result.json').write_text(json.dumps(records, indent=2) + '\n', encoding='utf-8')
    raise SystemExit(records[-1]['exit_code'])


if __name__ == '__main__':
    main()
