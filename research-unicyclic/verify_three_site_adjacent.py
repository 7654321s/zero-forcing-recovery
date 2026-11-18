"""Replay delayed fronts when the two simple attachment sites are adjacent."""

import argparse
from collections import Counter
from itertools import product
import hashlib
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
gap = runpy.run_path(str(HERE / 'verify_three_site_long_gap.py'))
forks = gap['forks']
branch = gap['branch']
tools = gap['tools']
pair = gap['pair']
dense = gap['dense']
bits = gap['bits']
attach = gap['attach']


def candidates(adj):
    cycle = branch['cycle_vertices'](adj)
    _, children = branch['tree_structure'](adj, cycle)
    paths = dense['paths_at'](children, cycle)
    nonpaths = [v for v in cycle if children[v] and v not in paths]
    if len(nonpaths) != 1 or len(paths) != 2:
        return
    a = nonpaths[0]
    order = tools['cycle_order'](adj, cycle, a)
    pos = sorted(order.index(v) for v in paths)
    if pos[1] != pos[0]+1:
        return
    if min(pos[0]-1, len(order)-1-pos[1]) >= 3:
        if pos[0]-1 < len(order)-1-pos[1]:
            order = order[:1] + order[:0:-1]
        mode = 'two_long_sides'
    else:
        if pos[0]-1 > len(order)-1-pos[1]:
            order = order[:1] + order[:0:-1]
        if max(pos[0]-1, len(order)-1-pos[1]) < 13:
            return
        mode = 'one_short_side'
    bpos, cpos = sorted(order.index(v) for v in paths)
    L, R = bpos-1, len(order)-1-cpos
    b, c = order[bpos:cpos+1]
    white_site = b if L == 0 or (mode == 'two_long_sides' and R > 3 and len(paths[b]) >= 2) else c
    path = paths[white_site]
    markers = order[-3:]
    white = bits([a, white_site, *order[1:bpos], *order[cpos+1:-3]])
    white |= bits(path) ^ bits(path[:-1:2])
    if mode == 'one_short_side' and white_site == c and len(path) == 1:
        exterior = R-1
    else:
        count = L+R-2
        if count % 2:
            pad = order[2] if mode == 'two_long_sides' else order[cpos+2]
            white ^= 1 << pad
            count -= 1
            if mode == 'two_long_sides':
                L -= 1
            else:
                R -= 1
        ring_time = 1+count//2
        site_time = 1+min(L+1, R-2)
        exterior = max(ring_time, site_time+(len(path)+1)//2)

    M = max(map(len, paths.values()))
    full = (1 << len(adj))-1
    for u in forks['four']['rooted_vertices'](children, a):
        for arm in pair['path_arms'](children, u):
            K = len(arm)
            if K < max(3, 2*M):
                continue
            local = K-1+(u == a)
            slow = arm[0] if local >= exterior else markers[1]
            yield dense['record'](mode, full, white | bits(arm[1:]),
                                  (markers[0], markers[2]), slow,
                                  max(local, exterior), None)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    time = runpy.run_path(str(branch['BASELINE']))['completion_time']
    counts = Counter()
    for L, R, depth, end_lengths, tail in product(
            (0, 1, 2, 3, 4, 9, 18), (3, 4, 5, 7, 13, 14, 31),
            (0, 1, 8), ((1, 1), (1, 2), (3, 1), (2, 3), (4, 7)), (0, 37)):
        eligible = min(L, R) >= 3 or max(L, R) >= 13
        if not eligible:
            continue
        n = L+R+3
        adj = list(branch['family']['cycle_graph'](n))
        attach(adj, L+1, end_lengths[0])
        attach(adj, L+2, end_lengths[1])
        u = attach(adj, 0, depth)
        attach(adj, u, 1)
        attach(adj, u, max(3, 2*max(end_lengths), tail))
        matches = list(candidates(adj))
        assert matches
        for cert in matches:
            late = time(adj, cert['blue'] ^ cert['slow'])
            try:
                tools['verify_certificate'](time, adj, cert['blue'], cert['killing'], cert['slow'],
                                            cert['restricted_deadline'], late)
            except AssertionError as e:
                raise AssertionError((L, R, depth, end_lengths, tail, late, cert)) from e
            counts[cert['case']] += 1
    report = {'status': 'passed', 'grid_counts': dict(counts),
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    with args.output.open('x', encoding='utf-8') as output:
        json.dump(report, output, indent=2)
        output.write('\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
