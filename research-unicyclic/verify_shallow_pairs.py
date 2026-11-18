"""Replay the one-loss obstruction for shallow cycle attachments with sibling leaves."""

from itertools import product
from pathlib import Path
from random import Random
import argparse
import hashlib
import json
import runpy


HERE = Path(__file__).resolve().parent
args_source = runpy.run_path(str(HERE / 'verify_family_arguments.py'))
cycle_graph = args_source['cycle_graph']
add_leaves = args_source['add_leaves']
verify_certificate = args_source['verify_certificate']
BASELINE = args_source['BASELINE']


def replay(counts, completion_time):
    n = len(counts)
    adj = list(cycle_graph(n))
    leaves = [add_leaves(adj, v, count) for v, count in enumerate(counts)]
    a = next(v for v, count in enumerate(counts) if count >= 2)
    first = leaves[a] & -leaves[a]
    rest = leaves[a] ^ first
    support = first | (rest & -rest)
    near = (1 << a) | adj[a]
    attached_elsewhere = [v for v, count in enumerate(counts) if count and v != a]
    other = [(v, x) for v in attached_elsewhere for x in ((v - 1) % n, (v + 1) % n)
             if (near & (1 << x)) == 0]
    left, right = (a - 1) % n, (a + 1) % n
    if other:
        y, x = other[0]
        blue = ((1 << len(adj)) - 1) ^ (1 << x)
        verify_certificate(completion_time, adj, blue, support, leaves[y] & -leaves[y], 1, 2)
        return 'separate_leaf_attachment'
    if not attached_elsewhere:
        blue = (1 << a) | (1 << left) | (1 << right) | leaves[a]
        deadline = (n - 2) // 2
        verify_certificate(completion_time, adj, blue, support, 1 << a, deadline, deadline + 1)
        return 'single_attachment'

    c = (a + 2) % n
    assert n == 4 and attached_elsewhere == [c]
    support = (1 << left) | (1 << right)
    blue = support | (1 << a) | leaves[a]
    if counts[c] == 1:
        verify_certificate(completion_time, adj, blue, support, 1 << a, 2, 3)
        return 'opposite_single_leaf'
    blue |= leaves[c]
    verify_certificate(completion_time, adj, blue, support, leaves[c] & -leaves[c], 1, 2)
    return 'opposite_sibling_leaves'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    completion_time = runpy.run_path(str(BASELINE))['completion_time']
    checks = {}

    def check(counts):
        if max(counts) < 2:
            return
        case = replay(counts, completion_time)
        checks[case] = checks.get(case, 0) + 1

    for n in range(4, 9):
        for counts in product(range(3), repeat=n):
            check(counts)
    rng = Random(20261118)
    for n in range(4, 31):
        for _ in range(20):
            check(tuple(rng.randrange(5) for _ in range(n)))
    report = {'status': 'passed', 'replayed_labelled_instances': sum(checks.values()),
              'counts_by_construction': checks,
              'grid': 'All leaf counts 0..2 on cycles of lengths 4..8',
              'sample': '20 seeded leaf count vectors in 0..4 for each length 4..30',
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'baseline_sha256': hashlib.sha256(BASELINE.read_bytes()).hexdigest()}
    with args.output.open('x', encoding='utf-8') as output:
        output.write(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
