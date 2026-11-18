"""Replay certificates for a triangle with at most one path per site."""

import argparse
from itertools import combinations_with_replacement
import hashlib
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
branch = runpy.run_path(str(HERE / 'verify_branch_witnesses.py'))
tools = branch['tools']
bits = branch['bits']

# Cycle vertices are 0, 1, 2. The remaining labels follow each arm outward, by site.
SMALL_WITNESSES = {
    (2, 1, 0): ((0, 2, 3, 5), (2, 5), 0, 2, 3),
    (2, 2, 0): ((1, 2, 4, 5), (2, 4), 1, 3, 4),
    (2, 1, 1): ((0, 1, 4, 5), (1, 5), 0, 3, 4),
    (2, 2, 1): ((0, 1, 3, 4, 6), (0, 4), 1, 3, 4),
    (2, 2, 2): ((1, 2, 4, 5), (4, 5), 1, 4, 5),
    (3, 1, 0): ((0, 1, 2, 3), (1, 2), 0, 2, 3),
    (3, 2, 0): ((0, 1, 2, 3, 6), (1, 2), 0, 2, 3),
    (3, 3, 0): ((1, 2, 3, 4, 6), (2, 3), 1, 3, 4),
    (3, 1, 1): ((0, 1, 2, 3, 5), (1, 2), 0, 2, 3),
    (3, 2, 1): ((0, 1, 2, 3, 5), (1, 2), 0, 3, 4),
    (3, 3, 1): ((0, 1, 2, 3, 5), (1, 2), 0, 4, 5),
    (3, 2, 2): ((0, 1, 2, 3, 5), (1, 2), 0, 3, 4),
    (3, 3, 2): ((0, 1, 2, 3, 5), (1, 2), 0, 4, 5),
    (3, 3, 3): ((0, 1, 2, 3, 5), (1, 2), 0, 4, 5),
}


def graph(lengths):
    adj = list(branch['family']['cycle_graph'](3))
    arms = []
    for site, length in enumerate(lengths):
        start = len(adj)
        branch['attach_path'](adj, site, length)
        arms.append(tuple(range(start, len(adj))))
    return adj, arms


def long_witness(lengths, arms):
    length, p, q = lengths
    first = arms[0][0]
    if p == q == 1:
        b_leaf = arms[1][0]
        return bits((0, 2, first, b_leaf)), bits((2, b_leaf)), 1 << first, max(length-1, 3), length+1
    seeds = [0, 1, 2, first]
    for arm in arms[1:]:
        seeds.extend(arm[:-1:2])
    return bits(seeds), bits((1, 2)), 1 << first, length-1, length


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    time = runpy.run_path(str(branch['BASELINE']))['completion_time']
    verify = tools['verify_certificate']
    small = []
    expected = {(l, p, q) for l in (2, 3) for p in range(1, l+1) for q in range(p+1)}
    assert set(SMALL_WITNESSES) == expected
    for lengths, (blue, killing, slow, deadline, delayed) in SMALL_WITNESSES.items():
        adj, _ = graph(lengths)
        verify(time, adj, bits(blue), bits(killing), 1 << slow, deadline, delayed)
        small.append(dict(lengths=lengths, blue=blue, killing=killing, slow=slow,
                          restricted_deadline=deadline, slow_completion_time=delayed))

    checked = 0
    for l in (*range(4, 26), 31, 64, 127):
        sites = range(l+1) if l <= 25 else sorted({0, 1, 2, 3, 4, 5, l//2, l-1, l})
        for q, p in combinations_with_replacement(sites, 2):
            if p == 0:
                continue
            lengths = (l, p, q)
            adj, arms = graph(lengths)
            verify(time, adj, *long_witness(lengths, arms))
            checked += 1

    report = {'status': 'passed', 'small_cases': small, 'grid_checked': checked,
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    with args.output.open('x', encoding='utf-8') as output:
        output.write(json.dumps(report, indent=2) + '\n')
    print(f'Passed {len(small)} exact short cases and {checked} long-path replay instances.')


if __name__ == '__main__':
    main()
