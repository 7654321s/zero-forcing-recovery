"""Census theta graphs and replay nearby theta, diamond and bouquet constructions."""

import argparse
from itertools import combinations_with_replacement
from pathlib import Path
import runpy


ROOT = Path(__file__).resolve().parents[1]
SIMULATOR = runpy.run_path(str(ROOT / 'scripts' / 'classification_experiment.py'))
TOOLS = runpy.run_path(str(ROOT / 'research-unicyclic' / 'verify_size_two_witnesses.py'))
completion_time = SIMULATOR['completion_time']
every_minimum_support = SIMULATOR['every_minimum_support']
POSITIVE_CORES = {(1, 2, 2), (2, 2, 2), (2, 2, 3)}
# With theta's numbering, the entries give whites, support, slow loss and the two times.
SHORT_SHARED_EDGE = {
    (2, 3): ((4,), (2, 3), 0, 1, 2),
    (2, 4): ((2,), (3, 5), 1, 1, 2),
    (3, 3): ((2, 5), (3, 4), 0, 2, 3),
    (3, 4): ((2, 6), (3, 4), 1, 2, 3),
    (4, 4): ((5, 6, 7), (2, 4), 0, 2, 3),
}


def theta(lengths):
    """Use vertices 0 and 1 as the ends of the three paths."""
    start = 2
    paths = []
    edges = []
    for length in lengths:
        path = [0, *range(start, start + length - 1), 1]
        start += length - 1
        paths.append(path)
        edges.extend(zip(path, path[1:]))
    return TOOLS['adjacency'](start, edges), paths


def mask(vertices):
    return sum(1 << vertex for vertex in vertices)


def certify(adj, blue, support, slow, early, late):
    if (support.bit_count() != 2 or slow.bit_count() != 1 or (support | slow) & ~blue
            or slow & support):
        raise AssertionError((blue, support, slow))
    TOOLS['verify_certificate'](completion_time, adj, blue, support, slow, early, late)


def theta_census(max_order):
    positive = []
    negative = 0
    for lengths in combinations_with_replacement(range(1, max_order), 3):
        if lengths[1] < 2 or sum(lengths) > max_order + 1:
            continue
        adj, _ = theta(lengths)
        if lengths in POSITIVE_CORES:
            result, counterexample, _, _ = every_minimum_support(adj)
            if not result:
                raise AssertionError((lengths, counterexample))
            positive.append(lengths)
            continue
        row = TOOLS['find_size_two'](adj, completion_time)
        if row is None:
            raise AssertionError(f'No two-loss certificate at {lengths}')
        certify(adj, row['blue'], row['killing'], row['slow'], row['restricted_deadline'],
                row['slow_completion_time'])
        negative += 1
    return positive, negative


def theta_families(limit):
    count = 0
    for second in (2, 3, 4):
        for last in range(4 if second == 2 else 5, limit + 1):
            adj, (a, b, c) = theta((2, second, last))
            if second == 2:
                white, delayed = {1, c[-2]}, 0
            else:
                white, delayed = {b[-2], c[-3]}, c[-2]
            blue = ((1 << len(adj)) - 1) ^ mask(white)
            certify(adj, blue, mask([a[1], b[1]]), 1 << delayed, 1, 2)
            count += 1
    return count


def shared_edge_families(limit):
    count = largest_gap = 0
    for r in range(3, limit + 1):
        lengths = range(2, r + 1) if r <= 40 else (2, 3, 4, r - 1, r)
        for q in lengths:
            adj, (_, b, c) = theta((1, q, r))
            if r < 5:
                white, support, slow, restricted, delayed = SHORT_SHARED_EDGE[q, r]
                blue = ((1 << len(adj)) - 1) ^ mask(white)
            else:
                blue = mask([0, 1, c[1], c[3], *b[2:q - 1:2], *c[2:r - 1:2]])
                support, slow = (c[1], c[3]), 1
                short_whites = (q + 1) // 2
                long_whites = (r - 3) // 2
                restricted = (short_whites + long_whites + 2) // 2
                delayed = long_whites + 1 + (short_whites + 1) // 2
            certify(adj, blue, mask(support), 1 << slow, restricted, delayed)
            count += 1
            largest_gap = max(largest_gap, delayed - restricted)
    return count, largest_gap


def append_leaves(adj, root, count):
    leaves = []
    for _ in range(count):
        vertex = len(adj)
        adj[root] |= 1 << vertex
        adj.append(1 << root)
        leaves.append(vertex)
    return leaves


def diamond_families(limit):
    census_count = 0
    for left, right in combinations_with_replacement(range(6), 2):
        adj, _ = theta((1, 2, 2))
        append_leaves(adj, 0, left)
        append_leaves(adj, 1, right)
        result, counterexample, _, _ = every_minimum_support(adj)
        if result != (left != 1):
            raise AssertionError((left, right, result, counterexample))
        census_count += 1

    certificates = 0
    for count in range(1, limit + 1):
        adj, _ = theta((1, 2, 2))
        delayed, = append_leaves(adj, 0, 1)
        append_leaves(adj, 1, count)
        certify(adj, ((1 << len(adj)) - 1) ^ 3, mask([2, 3]), 1 << delayed, 2, 3)

        adj, _ = theta((1, 2, 2))
        append_leaves(adj, 2, count)
        certify(adj, ((1 << len(adj)) - 1) ^ (1 << 2), mask([0, 1]), 1 << 3, 1, 2)
        certificates += 2

    for length in range(2, limit + 1):
        adj, _ = theta((1, 2, 2))
        tip = 0
        for _ in range(length):
            tip, = append_leaves(adj, tip, 1)
        certify(adj, mask(range(5)), mask([2, 3]), 1 << 4, length - 1, length)
        certificates += 1
    return census_count, certificates


def append_cycle(adj, root, length):
    vertices = [root, *range(len(adj), len(adj) + length - 1)]
    adj.extend([0] * (length - 1))
    for i, v in enumerate(vertices):
        u = vertices[i - 1]
        adj[v] |= 1 << u
        adj[u] |= 1 << v
    return vertices[1:]


def bouquet_families():
    pairs = runpy.run_path(str(ROOT / 'research-bicyclic' / 'check_two_cycles.py'))
    positive, negative = 0, 0
    for count in range(2, 6):
        for lengths in combinations_with_replacement(range(3, 9), count):
            p, q = lengths[0], lengths[-1]
            base, a, b = pairs['graph'](p, q, True)
            adj = list(base)
            added = []
            for length in lengths[1:-1]:
                added.extend(append_cycle(adj, 0, length))
            if q == 3:
                result, counterexample, _, _ = every_minimum_support(adj)
                if not result:
                    raise AssertionError((lengths, counterexample))
                positive += 1
                continue
            _, blue, support, slow, deadline = pairs['certificate'](p, q, True, a, b)
            certify(adj, mask(blue) | mask(added), mask(support), 1 << slow, deadline, deadline + 1)
            negative += 1
    return positive, negative


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-order', type=int, default=15)
    parser.add_argument('--parameter-limit', type=int, default=80)
    args = parser.parse_args()
    if args.max_order < 4 or args.parameter_limit < 5:
        parser.error('expected an order of at least 4 and a parameter limit of at least 5')
    positive, negative = theta_census(args.max_order)
    print(f'Theta census through order {args.max_order}: {len(positive) + negative} graphs', flush=True)
    print('Positive path triples:', positive, flush=True)
    print('Negative theta certificates:', negative, flush=True)
    print('Parametric theta certificate replays:', theta_families(args.parameter_limit), flush=True)
    shared_edge_count, largest_gap = shared_edge_families(args.parameter_limit)
    print(f'Shared-edge certificates: {shared_edge_count}, largest gap: {largest_gap}', flush=True)
    census_count, certificates = diamond_families(args.parameter_limit)
    print('Exact diamond root-leaf census:', census_count, flush=True)
    print('Parametric diamond certificate replays:', certificates, flush=True)
    positive_bouquets, negative_bouquets = bouquet_families()
    print('Exact positive bouquets:', positive_bouquets, flush=True)
    print('Bouquet certificate replays:', negative_bouquets, flush=True)


if __name__ == '__main__':
    main()
