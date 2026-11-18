"""Replay the asymmetric two-interval construction for short-path mixtures."""

import argparse
from collections import Counter
import hashlib
from itertools import product
import json
from pathlib import Path
import random
import runpy


HERE = Path(__file__).resolve().parent
length_two = runpy.run_path(str(HERE / 'verify_length_two_complete.py'))
separated = length_two['separated']
dense = length_two['dense']
branch = length_two['branch']
tools = length_two['tools']
bits = length_two['bits']
with_paths = length_two['with_paths']


def candidates(adj):
    cycle = branch['cycle_vertices'](adj)
    _, children = branch['tree_structure'](adj, cycle)
    paths = dense['paths_at'](children, cycle)
    full = (1 << len(adj)) - 1
    for a, arm in sorted(paths.items()):
        if len(arm) != 1:
            continue
        order = tools['cycle_order'](adj, cycle, a)
        for ring in (order, order[:1] + order[:0:-1]):
            y, t = ring[1:3]
            if children[y] or len(paths.get(t, ())) < 2:
                continue
            remote_white = bits((y, arm[0]))
            span = ring[5:-2]
            positions = [i for i, v in enumerate(span) if children[v]]
            for i, j in zip(positions, positions[1:]):
                gap = j-i-1
                if not 1 <= gap <= 3:
                    continue
                left = paths.get(span[i])
                right = paths.get(span[j])
                if left is None or right is None:
                    continue
                if gap == 1:
                    long, short = sorted((left, right), key=len, reverse=True)
                    if len(long) > 2 or len(short) != 1:
                        continue
                    white = bits(long[1:] + short)
                    support = (long[0], span[i+1])
                else:
                    if len(left) != 1 or len(right) != 1:
                        continue
                    white = bits(left + right)
                    support = (span[i+1], span[j-1])
                yield dense['record'](f'short_clock_gap_{gap}', full, white | remote_white,
                                      support, t, 2, 3)


def ring_from_word(gaps, lengths):
    positions = [0]
    for g in gaps[:-1]:
        positions.append(positions[-1]+g+1)
    return with_paths(len(gaps)+sum(gaps), {v: [L] for v, L in zip(positions, lengths)})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    time = runpy.run_path(str(branch['BASELINE']))['completion_time']
    counts = Counter()
    forced = Counter()

    def verify(adj, cert):
        delay = cert['slow_completion_time']
        if delay is None:
            delay = time(adj, cert['blue'] ^ cert['slow'])
        tools['verify_certificate'](time, adj, cert['blue'], cert['killing'], cert['slow'],
                                    cert['restricted_deadline'], delay)

    for gap, n in product((1, 2, 3), (14, 19, 51)):
        adj = with_paths(n, {0: [1], 2: [2], 5: [2 if gap == 1 else 1], 6+gap: [1]})
        cert = next(c for c in candidates(adj) if c['case'] == f'short_clock_gap_{gap}')
        verify(adj, cert)
        forced[cert['case']] += 1

    rng = random.Random(61118)
    for n, repeats in product((9, 10, 11, 15, 22), range(120)):
        gaps = [rng.randrange(4) for _ in range(n)]
        lengths = [rng.randrange(1, 3) for _ in range(n)]
        lengths[0] = 2
        adj = ring_from_word(gaps, lengths)
        cert = length_two['formula'](adj) or next(candidates(adj), None)
        assert cert, (gaps, lengths)
        verify(adj, cert)
        counts[cert['case']] += 1

    for n, step in product((9, 10, 15, 24), (2, 3, 5)):
        lengths = [2 if i % step == 0 and i != n-1 else 1 for i in range(n)]
        adj = ring_from_word([1]*n, lengths)
        cert = next(candidates(adj))
        verify(adj, cert)
        forced[cert['case']] += 1

    report = {'status': 'passed', 'placement_replays': dict(counts),
              'asymmetric_case_replays': dict(forced),
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    with args.output.open('x', encoding='utf-8') as output:
        output.write(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
