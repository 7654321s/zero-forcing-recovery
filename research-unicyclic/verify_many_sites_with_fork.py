"""Replay local interval comparisons when one attachment tree branches."""

import argparse
from collections import Counter
import hashlib
from itertools import product
import json
from pathlib import Path
import random
import runpy


HERE = Path(__file__).resolve().parent
four = runpy.run_path(str(HERE / 'verify_four_cycle_complete.py'))
stem = runpy.run_path(str(HERE / 'verify_short_fork_stems.py'))
common = runpy.run_path(str(HERE / 'verify_ring_branch_witnesses.py'))
branch = four['branch']
pair = four['pair']
dense = four['dense']
tools = four['tools']
bits = four['bits']
attach = four['attach']
neighbors = four['neighbors']
partial = dense['partial_path']


def local_intervals(adj, cycle, children, paths):
    for p, left in sorted(paths.items()):
        order = tools['cycle_order'](adj, cycle, p)
        for ring in (order, order[:1] + order[:0:-1]):
            i = next(i for i, w in enumerate(ring[1:], 1) if children[w])
            if i == 1:
                x, q = ring[1:3]
                if x not in paths or q not in paths:
                    continue
                middle = paths[x]
                white = partial(left, True) | partial(paths[q], False)
                if len(middle) == 1:
                    white |= 1 << x
                    z = middle[0]
                else:
                    white |= bits(middle) ^ bits(middle[:-1:2])
                    z = x
                H = (left[0], z)
            elif 2 <= i <= 4:
                q = ring[i]
                if q not in paths:
                    continue
                if i == 2:
                    white = partial(left, True) | partial(paths[q], False)
                    H = (left[0], ring[1])
                else:
                    white = partial(left, False) | partial(paths[q], False)
                    H = (ring[1], ring[i-1])
            else:
                continue
            yield white, H


def short_leaf_clocks(adj, a, cycle, children, paths):
    for order in (ring for p in sorted(cycle)
                  for base in [tools['cycle_order'](adj, cycle, p)]
                  for ring in (base, base[:1] + base[:0:-1])):
        # Only the cyclic order matters. This traverses both orientations.
        q, y, t = order[:3]
        if (len(paths.get(q, ())) == 1 and (not children[y] or len(paths.get(y, ())) == 1)
                and all(children[v] for v in children[t])):
            yield bits((y, paths[q][0], *paths.get(y, ()))), t, t != a

        r, p, t, q = order[:4]
        if len(paths.get(p, ())) != 1 or len(paths.get(q, ())) != 1 or r == a:
            continue
        if not children[r]:
            white = bits((r, p, q))
        elif len(paths.get(r, ())) == 1:
            white = bits((p, q, paths[r][0]))
        else:
            continue
        yield white, paths[p][0], t != a


def candidates(adj):
    cycle = branch['cycle_vertices'](adj)
    if len(cycle) < 5 or branch['twins'](adj):
        return
    _, children = branch['tree_structure'](adj, cycle)
    paths = dense['paths_at'](children, cycle)
    roots = [v for v in cycle if children[v] and v not in paths]
    if len(roots) != 1 or len(paths) < 3:
        return
    a = roots[0]
    M = max(map(len, paths.values()))
    full = (1 << len(adj))-1
    for u in four['rooted_vertices'](children, a):
        arms = list(pair['path_arms'](children, u))
        for arm in arms:
            K = len(arm)
            if K < max(3, 2*M):
                continue
            for white, H in local_intervals(adj, cycle, children, paths):
                yield dense['record']('long_fork_against_interval', full,
                                      white | bits(arm[1:]), H, u, K-1, K)
        if M != 1 or len(arms) < 2:
            continue
        first, second = sorted(arms, key=len)[:2]
        if len(second) != 2:
            continue
        for white, slow, independent in short_leaf_clocks(adj, a, cycle, children, paths):
            if u == a and (not independent or white & adj[a] & bits(cycle) or len(first) != 1):
                continue
            yield dense['record']('short_fork_against_leaf_clock', full,
                                  white | partial(first, True) | partial(second, True),
                                  (first[0], second[0]), slow, 2, 3)


def side_fork(adj):
    """Adjacent short fork with a cycle parent and a length-two side branch."""
    cycle = branch['cycle_vertices'](adj)
    if len(cycle) < 5 or branch['twins'](adj):
        return
    _, children = branch['tree_structure'](adj, cycle)
    full = (1 << len(adj))-1
    for a in cycle:
        paths = [p for p in pair['path_arms'](children, a) if len(p) == 2]
        for u in children[a]:
            arms = branch['pendant_paths'](u, children)
            if arms is None or list(map(len, arms)) != [1, 2]:
                continue
            for path in paths:
                yield dense['record']('short_fork_adjacent_to_cycle', full,
                                      bits((a, arms[0][0], path[1])),
                                      arms[1], path[0], 2, 3)


def one_for_graph(adj):
    cycle = branch['cycle_vertices'](adj)
    _, children = branch['tree_structure'](adj, cycle)
    return (next(candidates(adj), None) or next(side_fork(adj), None)
            or next(four['prior']['fork_and_remote'](adj, cycle, children), None)
            or next(stem['candidates'](adj), None)
            or branch['branch_witness'](adj, cycle)
            or next(common['ring_witnesses'](adj, cycle), None)
            or next(pair['candidates'](adj), None)
            or next(dense['remote']['interval']['candidates'](adj), None))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    time = runpy.run_path(str(branch['BASELINE']))['completion_time']
    counts = Counter()
    rng = random.Random(71909)

    def verify(adj, cert):
        assert cert
        tools['verify_certificate'](time, adj, cert['blue'], cert['killing'], cert['slow'],
                                    cert['restricted_deadline'], cert['slow_completion_time'])
        counts[cert.get('case', 'long_interval')] += 1

    for sites, depth, length, style in product((4, 6, 9), (0, 1, 3, 11), (2, 3, 7, 31), range(12)):
        if sites == 4 and depth == 0 and length == 2:
            continue
        gaps = [rng.randrange(5) for _ in range(sites)]
        n = sites + sum(gaps)
        if n < 5:
            continue
        adj = list(branch['family']['cycle_graph'](n))
        cursor = 0
        for i, gap in enumerate(gaps):
            if i:
                attach(adj, cursor, 1 if style < 9 else rng.randrange(1, 12))
            cursor += 1 + gap
        u = attach(adj, 0, depth)
        attach(adj, u, 1)
        attach(adj, u, length)
        verify(adj, one_for_graph(adj))

    for n, leaves in ((5, (2, 3, 4)), (8, (1, 3, 5, 7)), (21, (1, 3, 11))):
        adj = list(branch['family']['cycle_graph'](n))
        for v in leaves:
            attach(adj, v, 1)
        attach(adj, 0, 2)
        u = attach(adj, 0, 1)
        attach(adj, u, 1)
        attach(adj, u, 2)
        verify(adj, next(side_fork(adj)))

    report = {'status': 'passed', 'grid_counts': dict(counts),
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    with args.output.open('x', encoding='utf-8') as output:
        json.dump(report, output, indent=2)
        output.write('\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
