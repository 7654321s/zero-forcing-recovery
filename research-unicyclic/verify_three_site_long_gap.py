"""Replay two competing clocks on a bare gap opposite a branching site."""

import argparse
from collections import Counter
from itertools import product
import hashlib
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
forks = runpy.run_path(str(HERE / 'verify_many_sites_with_fork.py'))
branch = forks['branch']
tools = forks['tools']
pair = forks['pair']
dense = forks['dense']
bits = forks['bits']
attach = forks['attach']
neighbors = forks['neighbors']


def candidates(adj):
    cycle = branch['cycle_vertices'](adj)
    if len(cycle) < 7:
        return
    _, children = branch['tree_structure'](adj, cycle)
    paths = dense['paths_at'](children, cycle)
    nonpaths = [v for v in cycle if children[v] and v not in paths]
    if len(nonpaths) != 1 or len(paths) != 2:
        return
    a = nonpaths[0]
    order = tools['cycle_order'](adj, cycle, a)
    if order[1] not in paths or order[-1] not in paths:
        return
    if len(paths[order[1]]) > len(paths[order[-1]]):
        order = order[:1] + order[:0:-1]
    b, c = order[1], order[-1]
    gap = order[2:-1]
    g = len(gap)
    left, right = paths[b], paths[c]
    white = bits(gap)
    for path in (left, right):
        white |= bits(path) ^ bits(path[:-1:2])
    if len(left) >= 2:
        if g % 2 == 0:
            white ^= 1 << gap[1]
        ring_fast = ((g if g % 2 else g-1)+2)//2
        ring_slow = a
        kind = 'both_long'
    elif len(right) >= 2:
        white ^= 1 << gap[0]
        ring_fast = (g+1)//2
        ring_slow = gap[0]
        kind = 'one_leaf'
    else:
        white ^= bits((gap[0], gap[-1]))
        ring_fast = max(2, g//2)
        ring_slow = gap[0]
        kind = 'two_leaves'
    full = (1 << len(adj))-1
    for u in forks['four']['rooted_vertices'](children, a):
        for arm in pair['path_arms'](children, u):
            K = len(arm)
            if K < max(3, 2*len(right)):
                continue
            slow = u if K-1 >= ring_fast else ring_slow
            yield dense['record'](kind, full, white | bits(arm[1:]), (b, c), slow,
                                  max(ring_fast, K-1), None)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    time = runpy.run_path(str(branch['BASELINE']))['completion_time']
    counts = Counter()
    for g, depth, ends, long, side in product(
            (4, 5, 6, 9, 18, 39, 83), (0, 1, 3, 19),
            ((1, 1), (1, 2), (1, 5), (3, 1), (2, 2), (4, 3)), (0, 39), (False, True)):
        n = g+3
        adj = list(branch['family']['cycle_graph'](n))
        attach(adj, 1, ends[0])
        attach(adj, n-1, ends[1])
        u = attach(adj, 0, depth)
        attach(adj, u, 1)
        attach(adj, u, max(3, 2*max(ends), long))
        if side:
            attach(adj, 0, 2)
            attach(adj, u, 2)
        matches = list(candidates(adj))
        assert matches, (g, depth, ends, long, side)
        for cert in matches:
            late = time(adj, cert['blue'] ^ cert['slow'])
            tools['verify_certificate'](time, adj, cert['blue'], cert['killing'], cert['slow'],
                                        cert['restricted_deadline'], late)
            counts[cert['case']] += 1
    report = {'status': 'passed', 'grid_counts': dict(counts),
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    with args.output.open('x', encoding='utf-8') as output:
        json.dump(report, output, indent=2)
        output.write('\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
