"""Replay the three-site residual with only short descending paths in the fork."""

import argparse
from collections import Counter
import hashlib
from itertools import product
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
fixed = runpy.run_path(str(HERE / 'verify_four_or_five_fork_sites.py'))
forks = fixed['forks']
branch = forks['branch']
tools = forks['tools']
bits = forks['bits']
attach = forks['attach']
edge = runpy.run_path(str(HERE / 'verify_blue_edge_lifts.py'))
short = forks['dense']['record']

# n=5, a=0, branches 1 and 2 at a; then the two leaves in site order.
CONSECUTIVE = {
    (1, 2): ((3, 4), (0, 1, 3, 4, 5, 7), (5, 7), 1),
    (1, 4): ((2, 3), (0, 1, 2, 3, 5, 6), (0, 5), 6),
}
ALL_LONG = {
    5: ((0, 1, 2, 3, 4, 5, 6), (2, 3), 0, 2, 3),
    6: ((0, 1, 2, 3, 4, 6, 7), (6, 7), 3, 3, 4),
}


def stem_candidates(adj):
    cycle = branch['cycle_vertices'](adj)
    _, children = branch['tree_structure'](adj, cycle)
    paths = forks['dense']['paths_at'](children, cycle)
    a = next(v for v in cycle if children[v] and v not in paths)
    u = a
    while len(children[u]) == 1:
        u = children[u][0]
    arms = branch['pendant_paths'](u, children)
    assert u != a and list(map(len, arms)) == [1, 2]
    full = (1 << len(adj))-1
    for white, slow, _ in forks['short_leaf_clocks'](adj, a, cycle, children, paths):
        yield short('three_site_short_stem', full, white | (1 << arms[1][-1]),
                    (arms[0][0], arms[1][0]), slow, 2, 3)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    time = runpy.run_path(str(branch['BASELINE']))['completion_time']
    counts = Counter()
    cases = []

    def verify(adj, cert):
        tools['verify_certificate'](time, adj, cert['blue'], cert['killing'], cert['slow'],
                                    cert['restricted_deadline'], cert['slow_completion_time'])
        counts[cert['case']] += 1

    for gaps in product(range(4), repeat=3):
        if gaps > gaps[::-1] or sum(gaps) < 2:
            continue
        adj = fixed['graph'](gaps)
        cert = fixed['find'](adj, time)
        assert cert, gaps
        verify(adj, cert)
        cases.append(dict(gaps=gaps, **cert))

    for sites, (edge_to_extend, blue, H, z) in CONSECUTIVE.items():
        adj = list(branch['family']['cycle_graph'](5))
        attach(adj, 0, 1)
        attach(adj, 0, 2)
        for s in sites:
            attach(adj, s, 1)
        assert bits(edge_to_extend) & bits(blue) == bits(edge_to_extend)
        assert not bits(edge_to_extend) & bits((*H,z))
        assert any(not adj[v] & ~bits(blue) for v in edge_to_extend)
        for increment in (0, 1, 2, 5, 19, 131):
            large = adj.copy()
            added = bits(edge['subdivide'](large, *edge_to_extend, increment)) if increment else 0
            verify(large, short('consecutive_three_sites', (1 << len(large))-1,
                                ((1 << len(large))-1) ^ (bits(blue) | added), H, z, 2, 3))

    for n, (blue, H, z, early, late) in ALL_LONG.items():
        adj = list(branch['family']['cycle_graph'](n))
        attach(adj, 0, 2)
        attach(adj, 0, 2)
        attach(adj, 1, 1)
        attach(adj, n-1, 1)
        for loss in ((), H, (H[0],), (H[1],), (z,)):
            assert four_step(adj, bits(blue) ^ bits(loss)) & 1
        for extra in (0, 1, 2, 8):
            large = adj.copy()
            for _ in range(extra):
                attach(large, 0, 2)
            verify(large, short('all_long_root_arms', (1 << len(large))-1,
                                ((1 << len(adj))-1) ^ bits(blue), H, z, early, late))

    for gaps, depth in product(((0, 0, 2), (0, 1, 1), (1, 1, 1), (1, 1, 2),
                                (0, 0, 57), (27, 67, 1), (0, 18, 0)), (1, 2, 7, 23)):
        n = 3 + sum(gaps)
        adj = list(branch['family']['cycle_graph'](n))
        p = 1+gaps[0]
        attach(adj, p, 1)
        attach(adj, p+gaps[1]+1, 1)
        u = attach(adj, 0, depth)
        attach(adj, u, 1)
        attach(adj, u, 2)
        verify(adj, next(stem_candidates(adj)))

    report = {'status': 'passed', 'grid_counts': dict(counts), 'finite_certificates': cases,
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    with args.output.open('x', encoding='utf-8') as output:
        json.dump(report, output, indent=2)
        output.write('\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'finite_certificates'}, indent=2))


four_step = forks['four']['step']


if __name__ == '__main__':
    main()
