"""Replay the general certificates for a cycle with two distinct leaf sites."""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
helpers = runpy.run_path(str(HERE / 'verify_family_arguments.py'))
cycle_graph = helpers['cycle_graph']
add_leaves = helpers['add_leaves']
verify_certificate = helpers['verify_certificate']
BASELINE = helpers['BASELINE']


def witness(n, distance):
    assert n >= 4 and 1 <= distance <= n // 2
    leaf_zero = n
    if distance == 1:
        return 'adjacent', [1, 2, 3, leaf_zero], [1, 3], 2, max(2, (n - 1) // 2), n - 1
    if n == 2 * distance:
        return 'opposite', [0, 1, n - 1, leaf_zero], [n - 1, leaf_zero], 0, distance, distance + 1
    if distance == 2:
        return 'distance_two', [1, 2, 3, leaf_zero], [2, leaf_zero], 3, max(3, n - 3), n - 1
    if n == 2 * distance + 1:
        return 'odd_almost_opposite', [1, 2, n - 1, leaf_zero], [2, leaf_zero], n - 1, distance + 1, distance + 2
    return ('separated', [1, 2 * distance - 1, 2 * distance, leaf_zero], [1, leaf_zero],
            2 * distance - 1, n - distance - 1, n - distance)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-cycle-length', type=int, default=100)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.max_cycle_length < 4:
        parser.error('the maximum cycle length must be at least four')
    completion_time = runpy.run_path(str(BASELINE))['completion_time']
    counts = Counter()
    first_cases = {}
    for n in range(4, args.max_cycle_length + 1):
        for distance in range(1, n // 2 + 1):
            adj = list(cycle_graph(n))
            add_leaves(adj, 0, 1)
            add_leaves(adj, distance, 1)
            case, blue, killing, slow, deadline, delayed = witness(n, distance)
            verify_certificate(completion_time, adj, sum(1 << v for v in blue),
                               sum(1 << v for v in killing), 1 << slow, deadline, delayed)
            counts[case] += 1
            if case not in first_cases:
                first_cases[case] = {'cycle_length': n, 'distance': distance, 'blue': blue,
                                     'minimum_killing': killing, 'slow_loss': slow,
                                     'restricted_deadline': deadline, 'slow_completion_time': delayed}
    report = {'status': 'passed', 'max_cycle_length': args.max_cycle_length,
              'cases_checked': sum(counts.values()), 'counts_by_construction': dict(counts),
              'first_instance_by_construction': first_cases,
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'baseline_sha256': hashlib.sha256(BASELINE.read_bytes()).hexdigest()}
    with args.output.open('x', encoding='utf-8') as output:
        output.write(json.dumps(report, indent=2) + '\n')
    print(json.dumps({key: value for key, value in report.items()
                      if key != 'first_instance_by_construction'}, indent=2))


if __name__ == '__main__':
    main()
