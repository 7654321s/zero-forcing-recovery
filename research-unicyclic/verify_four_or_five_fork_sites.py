"""Close the residual fixed short fork on four or five attachment sites."""

import argparse
from collections import Counter
from functools import lru_cache
import hashlib
from itertools import combinations, product
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
forks = runpy.run_path(str(HERE / 'verify_many_sites_with_fork.py'))
branch = forks['branch']
tools = forks['tools']
bits = forks['bits']
neighbors = forks['neighbors']
attach = forks['attach']


def graph(gaps):
    adj = list(branch['family']['cycle_graph'](len(gaps)+sum(gaps)))
    attach(adj, 0, 1)
    attach(adj, 0, 2)
    vertex = 0
    for g in gaps[:-1]:
        vertex += g+1
        attach(adj, vertex, 1)
    return adj


def arc_forts(adj):
    cycle = branch['cycle_vertices'](adj)
    _, children = branch['tree_structure'](adj, cycle)
    arms = {v: branch['pendant_paths'](v, children) for v in cycle if children[v]}
    result = set()
    for v, left in arms.items():
        order = tools['cycle_order'](adj, cycle, v)
        for left_arm in left:
            for ring in (order, order[:1] + order[:0:-1]):
                white = bits(left_arm)
                for i, w in enumerate(ring[1:], 1):
                    if w in arms and i > 1:
                        result.update(white | bits(right) for right in arms[w])
                    white |= (1 << w) | bits(u for arm in arms.get(w, ()) for u in arm)
    return sorted(result, key=lambda f: (f.bit_count(), f))


def find(adj, completion_time):
    infinity = len(adj)+1
    full = (1 << len(adj))-1

    @lru_cache(maxsize=None)
    def time(blue):
        return completion_time(adj, blue)

    forts = arc_forts(adj)
    for extra in (0, 1, 2):
        for fort in forts:
            pool = full ^ fort
            assert all((adj[v] & fort).bit_count() != 1 for v in neighbors(pool))
            pairs = tuple(combinations(neighbors(fort), 2))
            for white in combinations(neighbors(pool), extra):
                other_blue = pool ^ bits(white)
                for u, v in pairs:
                    H = bits((u, v))
                    blue = other_blue | H
                    early = max(time(blue ^ (1 << u)), time(blue ^ (1 << v)))
                    if early >= infinity:
                        continue
                    late, z = max((time(blue ^ (1 << w)), w) for w in neighbors(blue))
                    if early < late < infinity:
                        return dict(case='finite_short_fork', blue=blue, killing=H,
                                    slow=1 << z, restricted_deadline=early,
                                    slow_completion_time=late)
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    time = runpy.run_path(str(branch['BASELINE']))['completion_time']
    counts = Counter()
    rows = []
    for sites in (4, 5):
        for gaps in product(range(4), repeat=sites):
            if gaps > gaps[::-1] or sites+sum(gaps) == 4:
                continue
            adj = graph(gaps)
            cert = forks['one_for_graph'](adj)
            if cert is None:
                cert = find(adj, time)
                assert cert, gaps
                rows.append(dict(gaps=gaps, **cert))
            tools['verify_certificate'](time, adj, cert['blue'], cert['killing'], cert['slow'],
                                        cert['restricted_deadline'], cert['slow_completion_time'])
            counts[cert['case']] += 1
    report = {'status': 'passed', 'grid_counts': dict(counts), 'finite_certificates': rows,
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    with args.output.open('x', encoding='utf-8') as output:
        json.dump(report, output, indent=2)
        output.write('\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'finite_certificates'}, indent=2))


if __name__ == '__main__':
    main()
