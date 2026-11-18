"""Replay staggered local intervals and complete the dense single-path case."""

import argparse
from collections import Counter
import hashlib
from itertools import product
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
remote = runpy.run_path(str(HERE / 'verify_remote_site_intervals.py'))
branch = remote['branch']
tools = remote['tools']
bits = branch['bits']
neighbors = branch['neighbors']
with_paths = remote['with_paths']

FOUR_CYCLE = {
    (2, 1, 1, 1): ((1, 2, 3, 5, 6), (3, 5), 2, 3, 4),
    (2, 2, 1, 1): ((1, 2, 3, 5, 6), (3, 5), 1, 3, 4),
    (2, 1, 2, 1): ((0, 2, 3, 4, 6), (0, 6), 2, 3, 4),
    (2, 2, 2, 1): ((0, 1, 2, 3, 4, 6), (0, 6), 1, 2, 3),
    (2, 2, 2, 2): ((1, 2, 3, 5, 6), (3, 5), 1, 4, 5),
}


def partial_path(path, first):
    seeds = path[1:-1:2]
    if first:
        seeds = path[:1] + seeds
    return bits(path) ^ bits(seeds)


def record(case, full, white, support, slow, early, late):
    return dict(case=case, blue=full ^ white, killing=bits(support), slow=1 << slow,
                restricted_deadline=early, slow_completion_time=late)


def paths_at(children, cycle):
    result = {}
    for v in cycle:
        arms = branch['pendant_paths'](v, children)
        if arms is not None and len(arms) == 1:
            result[v] = arms[0]
    return result


def staggered_candidates(adj):
    cycle = branch['cycle_vertices'](adj)
    if len(cycle) < 5:
        return
    _, children = branch['tree_structure'](adj, cycle)
    paths = paths_at(children, cycle)
    full = (1 << len(adj)) - 1
    for p, left in sorted(paths.items()):
        order = tools['cycle_order'](adj, cycle, p)
        for ring in (order, order[:1] + order[:0:-1]):
            x, q, t = ring[1:4]
            if q not in paths:
                continue
            right = paths[q]
            early_left = (len(left)+2)//2
            if x in paths and all(children[v] for v in children[t]):
                bound = 1 + max(len(paths[x]), len(right))
                if early_left <= bound:
                    white = partial_path(left, True) | bits(paths[x] + right) | (1 << q)
                    yield record('white_site', full, white, (left[0], x), t, bound, bound+1)
            if not children[x] and not children[t]:
                y, source = ring[3:5]
                if all(children[v] for v in children[source]) and early_left <= 1+len(right):
                    white = partial_path(left, True) | bits(right) | (1 << y)
                    yield record('white_bare_vertex', full, white, (left[0], x),
                                 source, 1+len(right), 2+len(right))


def dense_long_candidate(adj):
    cycle = branch['cycle_vertices'](adj)
    if len(cycle) < 4:
        return None
    _, children = branch['tree_structure'](adj, cycle)
    paths = paths_at(children, cycle)
    if len(paths) != len(cycle):
        return None
    a = max(sorted(cycle), key=lambda v: len(paths[v]))
    length = len(paths[a])
    if length < 3:
        return None
    ring = tools['cycle_order'](adj, cycle, a)
    p, x, q = ring[1:4]
    white = bits(paths[a]) | partial_path(paths[p], True) | partial_path(paths[q], False)
    middle = paths[x]
    if len(middle) == 1:
        white |= 1 << x
        second = middle[0]
    else:
        white |= bits(middle) ^ bits(middle[:-1:2])
        second = x
    return record('dense_long', (1 << len(adj)) - 1, white, (paths[p][0], second),
                  p, length, None)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    time = runpy.run_path(str(branch['BASELINE']))['completion_time']
    counts = Counter()

    def verify(adj, cert):
        delayed = time(adj, cert['blue'] ^ cert['slow'])
        assert delayed < len(adj)+1
        if cert['slow_completion_time'] is not None:
            assert delayed == cert['slow_completion_time']
        tools['verify_certificate'](time, adj, cert['blue'], cert['killing'], cert['slow'],
                                    cert['restricted_deadline'], delayed)
        counts[cert['case']] += 1

    for lengths, (blue, killing, slow, early, late) in FOUR_CYCLE.items():
        adj = with_paths(4, {v: [L] for v, L in enumerate(lengths)})
        verify(adj, record('four_cycle_fixed', (1 << len(adj))-1,
                           ((1 << len(adj))-1) ^ bits(blue), killing, slow, early, late))
    for n in range(5, 12):
        for lengths in product((1, 2), repeat=n):
            if max(lengths) == 1:
                continue
            adj = with_paths(n, {v: [L] for v, L in enumerate(lengths)})
            verify(adj, next(staggered_candidates(adj)))

    for n, m, style in product((*range(4, 15), 37, 81), (3, 4, 5, 23, 65), (0, 1, 2)):
        other_limit = min(m, 5) if n > 15 or m > 23 else m
        lengths = [m if v == style else 1 + ((13*v+style) % other_limit) for v in range(n)]
        adj = with_paths(n, {v: [L] for v, L in enumerate(lengths)})
        verify(adj, dense_long_candidate(adj))

    for n in (5, 6, 9, 24, 71):
        for left, middle, right in product((1, 2, 7), (1, 2, 4), (1, 2, 8)):
            for tail in ((), (2,), (2, 4)):
                for kind in ('white_site', 'white_bare_vertex'):
                    site = 3 if kind == 'white_site' else 4
                    paths = {0: [left], 2: [right], site: tail}
                    if kind == 'white_site':
                        paths[1] = [middle]
                    adj = with_paths(n, paths)
                    for cert in staggered_candidates(adj):
                        if cert['case'] == kind:
                            verify(adj, cert)

    assert set(counts) == {'four_cycle_fixed', 'white_site', 'white_bare_vertex', 'dense_long'}
    report = {'status': 'passed', 'grid_counts': dict(counts),
              'four_cycle_cases': [dict(lengths=l, blue=b, killing=h, slow=z, early=e, late=d)
                                   for l, (b, h, z, e, d) in FOUR_CYCLE.items()],
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    with args.output.open('x', encoding='utf-8') as output:
        output.write(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'four_cycle_cases'}, indent=2))


if __name__ == '__main__':
    main()
