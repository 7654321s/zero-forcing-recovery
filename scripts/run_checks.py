"""Run the release integrity check, Lean build, axiom audit and experiments."""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import hashlib
import json
import os
import platform
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
IGNORED = {'.git', '.lake', 'build', '__pycache__'}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify_files():
    manifest = json.loads((ROOT/'verification/release-files.json').read_text(encoding='utf-8'))
    actual = set()
    for directory, folders, files in os.walk(ROOT):
        folders[:] = [name for name in folders if name not in IGNORED]
        for name in files:
            path = Path(directory)/name
            actual.add(path.relative_to(ROOT).as_posix())
    if actual != set(manifest) | {'verification/release-files.json'}:
        raise ValueError('Release file inventory differs; inspect added or missing files.')
    for relative, expected in manifest.items():
        if digest(ROOT/relative) != expected:
            raise ValueError('Release file changed: '+relative)
    snapshot = json.loads((ROOT/'verification/verified-snapshot.json').read_text(encoding='utf-8'))
    for row in snapshot['sources']:
        if digest(ROOT/row['file']) != row['sha256']:
            raise ValueError('Proof source changed: '+row['file'])
    return len(actual)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lake', default='lake', help='Lake executable for the pinned Lean toolchain')
    args = parser.parse_args()
    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S_%fZ')
    out = ROOT/'build/checks'/stamp
    out.mkdir(parents=True)
    summary = dict(status='running', started_utc=datetime.now(timezone.utc).isoformat(),
                   operating_system=platform.system(), python_version=platform.python_version(),
                   project_proofs_built_from_source=None, independent_human_review=False,
                   novelty_confirmed=False, steps=[])

    def save():
        (out/'summary.json').write_text(json.dumps(summary, indent=2)+'\n', encoding='utf-8')

    def step(name, command):
        start = time.monotonic()
        print('Starting '+name, flush=True)
        log = out/(name+'.log')
        summary['current_step'] = name
        save()
        with log.open('w', encoding='utf-8') as handle:
            result = subprocess.run(command, cwd=ROOT, stdout=handle, stderr=subprocess.STDOUT)
        summary['steps'].append(dict(name=name, command=command, exit_code=result.returncode,
                                     log=log.name, log_sha256=digest(log),
                                     elapsed_seconds=time.monotonic()-start))
        save()
        print(name+' exit '+str(result.returncode), flush=True)
        if result.returncode:
            print('\n'.join(log.read_text(encoding='utf-8', errors='replace').splitlines()[-50:]), flush=True)
            raise RuntimeError(name+' failed; see '+str(log.relative_to(ROOT)))

    save()
    try:
        summary['release_files_checked'] = verify_files()
        proof_dir = ROOT/'.lake/build/lib/lean'
        existing = list(proof_dir.glob('formalization*.olean'))
        summary['project_proof_oleans_before_build'] = len(existing)
        step('lake-version', [args.lake, '--version'])
        step('build', [args.lake, '--no-ansi', '--wfail', 'build'])
        summary['project_proofs_built_from_source'] = not existing
        python = [sys.executable, '-X', 'utf8']
        step('axiom-audit', python+['scripts/audit_axioms.py', '--lake', args.lake])
        step('long-arm', python+['scripts/experiment.py'])
        step('one-short', python+['scripts/one_short_experiment.py'])
        step('small-trees', python+['scripts/classification_experiment.py'])
        step('paper-comparison', python+['scripts/compare_discrepancy_predicate.py',
             '--source', '.', '--output', 'build/paper-comparison.json'])
        step('specification', [args.lake, 'env', 'lean', 'review/SpecificationReadback.lean'])
        audit = json.loads((ROOT/'build/audit/result.json').read_text(encoding='utf-8'))
        trees = json.loads((ROOT/'build/classification-small-trees.json').read_text(encoding='utf-8'))
        if audit['status'] != 'passed' or audit['checked_declarations'] != 511:
            raise ValueError('Unexpected axiom audit result')
        if trees['trees'] != 95 or trees['positive'] != 21:
            raise ValueError('Unexpected finite-tree check result')
        summary.update(status='passed', source_modules=71, checked_declarations=511,
                       small_trees=95, positive_small_trees=21,
                       release_files_checked=verify_files())
    except Exception as exc:
        summary.update(status='failed', error_type=type(exc).__name__, error=str(exc))
    summary['finished_utc'] = datetime.now(timezone.utc).isoformat()
    save()
    print(json.dumps(summary, indent=2), flush=True)
    return 0 if summary['status'] == 'passed' else 1


if __name__ == '__main__':
    raise SystemExit(main())
