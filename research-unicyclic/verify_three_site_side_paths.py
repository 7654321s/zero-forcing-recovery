"""Replay exclusion using a side path or side leaf on a fork's ancestor chain."""

import argparse
from collections import Counter
import hashlib
from itertools import product
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
forks = runpy.run_path(str(HERE / 'verify_many_sites_with_fork.py'))
branch = forks['branch']
tools = forks['tools']
pair = forks['pair']
bits = forks['bits']
attach = forks['attach']
neighbors = forks['neighbors']
record = forks['dense']['record']
partial = forks['partial']


def candidates(adj):
    cycle = branch['cycle_vertices'](adj)
    parent, children = branch['tree_structure'](adj, cycle)
    full = (1 << len(adj)) - 1
    for u in sorted(set(range(len(adj))) - cycle):
        arms = branch['pendant_paths'](u, children)
        if arms is None or len(arms) != 2 or len(arms[0]) != 1 or len(arms[1]) < 2:
            continue
        s, long = arms[0][0], arms[1]
        K = len(long)
        stem = [u]
        side_whites = 0
        side_wait = []
        while parent[stem[-1]] is not None:
            lower = stem[-1]
            p = parent[lower]
            extras = [v for v in children[p] if v != lower]
            arms_by_gate = {arm[0]: arm for arm in pair['path_arms'](children, p)}
            if len(extras) > 1 or any(v not in arms_by_gate for v in extras):
                break
            distance = len(stem)
            if extras:
                side = arms_by_gate[extras[0]]
                J = len(side)
                if J >= (K+2)//2:
                    z = parent[p] if p not in cycle else next(
                        q for q in neighbors(adj[p]) if q in cycle)
                    white = bits(side) | partial([s], True) | partial(long, True)
                    yield record('long_side_path', full, white, (s, long[0]), z, J, J+1)
                if J == 1:
                    if distance == 1:
                        white = bits([u, *long[1:]])
                        yield record('side_leaf_unextended', full, white, (side[0], s),
                                     long[0], K, K+1)
                    else:
                        early = max([distance, K-1]
                                    + [max(d, distance-d)+w for d, w in side_wait])
                        slow = max([distance+K-1]
                                   + [distance-d+w for d, w in side_wait])
                        if slow > early:
                            white = bits(stem[1:] + long[1:]) | side_whites
                            yield record('side_leaf_with_intervening_paths', full, white,
                                         (side[0], s), long[0], early, slow)
                    break
                side_whites |= bits(side) ^ bits(side[:-1:2])
                side_wait.append((distance, (J+1)//2))
            stem.append(p)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    time = runpy.run_path(str(branch['BASELINE']))['completion_time']
    counts = Counter()
    raw = (HERE / 'unicyclic-through-11.json').read_bytes()
    rows = []

    def verify(adj, cert):
        tools['verify_certificate'](time, adj, cert['blue'], cert['killing'], cert['slow'],
                                    cert['restricted_deadline'], cert['slow_completion_time'])

    for index, g in enumerate(json.loads(raw)['graphs']):
        adj = tools['adjacency'](g['order'], g['edges'])
        for cert in candidates(adj):
            assert not g['every_minimum_support'], index
            verify(adj, cert)
            rows.append({'graph_index': index, **cert})

    for n, top, depth, K, option in product(
            (3, 5, 7, 13), (0, 1, 7), (1, 2, 7, 21), (2, 3, 4, 9, 30), range(3)):
        adj = list(branch['family']['cycle_graph'](n))
        p = attach(adj, 0, top)
        near = p
        for k in range(depth):
            if option == 2 and K >= 4 and 0 < k < depth:
                J = 2 if k % 2 == 0 else K//2
                attach(adj, near, J)
            near = attach(adj, near, 1)
        attach(adj, near, 1)
        attach(adj, near, K)
        attach(adj, p, (K+2)//2 if option == 1 else 1)
        attach(adj, 1, 1)
        attach(adj, n-1, 2)
        matches = list(candidates(adj))
        assert matches, (n, top, depth, K, option)
        for cert in matches:
            verify(adj, cert)
            counts[cert['case']] += 1

    report = {'status': 'passed', 'grid_counts': dict(counts), 'census_checked': len(rows),
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'census_sha256': hashlib.sha256(raw).hexdigest(), 'census_certificates': rows}
    with args.output.open('x', encoding='utf-8') as output:
        json.dump(report, output, indent=2)
        output.write('\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'census_certificates'}, indent=2))


if __name__ == '__main__':
    main()
