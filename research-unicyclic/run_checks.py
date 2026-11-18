"""Reproduce the unicyclic Lean proofs, finite certificates and census."""

import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess
import sys

from check_cycle_modules import MODULES


HERE = Path(__file__).resolve().parent
REPO = HERE.parent
PYTHON = [sys.executable, '-X', 'utf8', '-B']
REPLAYS = (
    ('verify_path_padding_coverage.py', 'path-padding-coverage-replay.json', ()),
    ('verify_adjacent_fork_bases.py', 'adjacent-fork-coverage-replay.json', ()),
    ('verify_size_two_witnesses.py', 'size-two-witness-replay.json', ()),
    ('enumerate_unicyclic.py', 'unicyclic-through-11.json', ('--max-vertices', '11')),
)


def reproduce(work, script, expected, options):
    actual = 'reproduced-' + expected
    print(f'Reproducing {expected}', flush=True)
    subprocess.run([*PYTHON, script, *options, '--output', actual], cwd=work, check=True)
    # JSON equality allows the platform's newline convention without ignoring data.
    if json.loads((work / actual).read_bytes()) != json.loads((work / expected).read_bytes()):
        raise ValueError(f'{actual} differs from the published {expected} in {work}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', type=Path, default=REPO,
                        help='checkout with the pinned Lean dependencies and built core modules')
    parser.add_argument('--lean-bin', type=Path, help='directory containing lake and lean')
    args = parser.parse_args()
    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S_%fZ')
    output = REPO / 'build' / 'unicyclic-checks' / stamp
    subprocess.run([*PYTHON, str(HERE / 'prepare_reproduction.py'), '--output', str(output)],
                   check=True)
    work = output / HERE.name
    lean_options = [] if args.lean_bin is None else ['--bin', str(args.lean_bin.resolve())]
    subprocess.run([*PYTHON, 'check_cycle_modules.py', '--base', str(args.base.resolve()),
                    *lean_options, *MODULES], cwd=work, check=True)
    for script, expected, options in REPLAYS:
        reproduce(work, script, expected, options)
    summary = {
        'status': 'passed',
        'lean_modules': list(MODULES),
        'matching_reports': [expected for _, expected, _ in REPLAYS],
    }
    (output / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n', encoding='utf-8')
    print(output / 'summary.json')


if __name__ == '__main__':
    main()
