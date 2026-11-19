"""Replay the certificates for two cycles sharing a vertex or joined by a bridge."""

import argparse
from collections import Counter
from pathlib import Path
import runpy


ROOT = Path(__file__).resolve().parents[1]
SIMULATOR = runpy.run_path(str(ROOT / 'scripts' / 'classification_experiment.py'))
completion_time = SIMULATOR['completion_time']
every_minimum_support = SIMULATOR['every_minimum_support']


def graph(p, q, shared):
    """Return adjacency masks and the labels in cyclic order, starting at the roots."""
    a = list(range(p))
    b = ([0] if shared else []) + list(range(p, p + q - shared))
    adj = [0] * (p + q - shared)
    edges = [(ring[i - 1], v) for ring in (a, b) for i, v in enumerate(ring)]
    if not shared:
        edges.append((a[0], b[0]))
    for x, y in edges:
        adj[x] |= 1 << y
        adj[y] |= 1 << x
    return tuple(adj), a, b


def certificate(p, q, shared, a, b):
    """Use the cases in RESEARCH.md, with 3 <= p <= q and the bowtie excluded."""
    x, y = a[0], b[0]
    if p >= 6:
        exterior = set(b) - {x}
        blue = exterior | set(a[1:4])
        if p % 2:
            blue.add(a[5])
            case, deadline = 'long odd', (p - 3) // 2
        else:
            case, deadline = 'long even', (p - 2) // 2
        return case, blue, (a[1], a[3]), a[2], deadline
    if p == 4:
        return 'square', set(b) | {x, a[1], a[3]}, (a[1], a[3]), x, 1
    if p == 5 and shared:
        blue = (set(b) - {b[-2]}) | {a[1], a[2], a[3]}
        return 'shared pentagon', blue, (a[1], a[2]), b[-1], 1
    if p == 5:
        blue = (set(b) - {b[-1]}) | {a[1], a[2], a[3]}
        return 'bridged pentagon', blue, (a[1], a[3]), a[2], 2
    if shared and q == 4:
        blue = set(a + b) - {b[2]}
        return 'shared triangle and square', blue, (a[1], a[2]), x, 1
    if shared:
        blue = set(a + b) - {b[2], b[3]}
        return 'shared triangle and longer cycle', blue, (a[1], a[2]), b[1], 1
    if q == 3:
        return 'bridged triangles', set(a + b[1:]), (a[1], a[2]), b[1], 1
    if q == 4:
        blue = set(a + b) - {b[2]}
        return 'bridged triangle and square', blue, (a[1], a[2]), y, 1
    return 'bridged triangle and longer cycle', set(a + b[1:-1]), (a[1], a[2]), b[-2], 1


def check(p, q, shared):
    adj, a, b = graph(p, q, shared)
    if shared and p == q == 3:
        result, witness, colorings, supports = every_minimum_support(adj)
        if not result:
            raise AssertionError(witness)
        return f'bowtie ({colorings} forcing sets and {supports} minimum supports)'

    case, blue, support, slow, deadline = certificate(p, q, shared, a, b)
    if len(set(support)) != 2 or not set(support) <= blue or slow not in blue - set(support):
        raise AssertionError((case, blue, support, slow))
    start = sum(1 << v for v in blue)
    singles = {v: completion_time(adj, start ^ (1 << v)) for v in blue}
    double = completion_time(adj, start ^ sum(1 << v for v in support))
    restricted = max(completion_time(adj, start), *(singles[v] for v in support))
    infinity = len(adj) + 1
    if (max(singles.values()) >= infinity or double != infinity
            or restricted != deadline or singles[slow] != deadline + 1):
        raise AssertionError((shared, p, q, blue, support, slow, double, restricted, singles))
    return case


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-cycle', type=int, default=32)
    args = parser.parse_args()
    if args.max_cycle < 3:
        parser.error('--max-cycle must be at least 3')
    for shared in (True, False):
        counts = Counter(check(p, q, shared) for p in range(3, args.max_cycle + 1)
                         for q in range(p, args.max_cycle + 1))
        print('Shared vertex' if shared else 'Bridge edge', sum(counts.values()), 'graphs')
        for case, count in sorted(counts.items()):
            print(' ', case, count)


if __name__ == '__main__':
    main()
