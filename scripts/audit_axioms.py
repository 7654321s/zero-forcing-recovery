"""Check source hashes and audit all named declarations using the installed Lake."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lake', default='lake', help='Lake executable, with pinned Lean installed')
    parser.add_argument('--output-dir', type=Path, default=ROOT / 'build' / 'audit')
    args = parser.parse_args()
    manifest = json.loads((ROOT / 'verification/verified-snapshot.json').read_text(encoding='utf-8'))
    for row in manifest['sources']:
        actual = hashlib.sha256((ROOT / row['file']).read_bytes()).hexdigest()
        if actual != row['sha256']:
            raise SystemExit('Source changed: ' + row['file'])
    expected_rows = json.loads((ROOT / 'verification/expected-axioms.json').read_text(encoding='utf-8'))
    expected = {row['theorem']: set(row['axioms']) for row in expected_rows}
    if len(expected) != len(expected_rows) or len(expected) != manifest['named_theorems']:
        raise SystemExit('Invalid declaration inventory.')
    command = [args.lake, 'env', 'lean', 'Audit.lean']
    result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True,
                            encoding='utf-8', errors='replace')
    log = result.stdout + result.stderr
    args.output_dir.mkdir(parents=True, exist_ok=True)
    (args.output_dir / 'lean.log').write_text(log, encoding='utf-8')
    found = {m[1]: {a.strip() for a in m[2].split(',') if a.strip()}
             for m in re.finditer(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log)}
    found.update({m[1]: set() for m in re.finditer(r"'([^']+)' does not depend on any axioms", log)})
    problems = []
    if result.returncode:
        problems.append('Lean exited with code ' + str(result.returncode))
    if 'warning:' in log:
        problems.append('Lean emitted a warning; inspect lean.log.')
    if set(found) != set(expected):
        problems.append('Missing or unexpected declaration in audit output.')
    for name, axioms in found.items():
        if not axioms <= ALLOWED:
            problems.append('Nonstandard axiom in ' + name + ': ' + ', '.join(sorted(axioms - ALLOWED)))
        if name in expected and axioms != expected[name]:
            problems.append('Axiom dependencies changed: ' + name)
    report = dict(status='failed' if problems else 'passed', checked_declarations=len(found),
                  source_modules=len(manifest['sources']), allowed_axioms=sorted(ALLOWED),
                  problems=problems, command=command,
                  log_sha256=hashlib.sha256(log.encode('utf-8')).hexdigest())
    (args.output_dir / 'result.json').write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(report, indent=2))
    raise SystemExit(bool(problems))


if __name__ == '__main__':
    main()
