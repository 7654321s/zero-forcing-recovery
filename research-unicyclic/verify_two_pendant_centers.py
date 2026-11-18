"""Replay certificates using two centers with disjoint pairs of pendant paths."""

import argparse
from collections import Counter
import hashlib
from itertools import combinations, product
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
branch = runpy.run_path(str(HERE / 'verify_branch_witnesses.py'))
tools = branch['tools']
bits = branch['bits']
attach = branch['attach_path']


def path_arms(children, root):
    for first in children[root]:
        path = [first]
        while len(children[path[-1]]) == 1:
            path.append(children[path[-1]][0])
        if not children[path[-1]]:
            yield path


def certificate(adj, u, v, inner, outer):
    """Try a slow loss at u and a killing pair at v."""
    full = (1 << len(adj)) - 1
    a, b = inner
    c, d = outer
    total = len(a) + len(b) - 1
    inward = len(b) - 1 + (len(a) - len(b) + 1) // 2
    fast = max(len(c), len(d), inward)
    killing = bits((c[0], d[0]))
    if total > fast:
        white = bits(a[:-1] + b[:-1] + c[1:] + d[1:])
        return dict(case='strict', centers=[u, v], arms=[a, b, c, d],
                    blue=full ^ white, killing=killing, slow=1 << a[-1],
                    restricted_deadline=fast, slow_completion_time=total)
    longest = len(a)
    if longest >= 2 and longest == len(c) and len(b) == len(d) == 1 and not adj[u] & (1 << v):
        white = bits(a[1:] + c[1:]) | (1 << u)
        return dict(case='equal_nonadjacent', centers=[u, v], arms=[a, b, c, d],
                    blue=full ^ white, killing=killing, slow=1 << a[0],
                    restricted_deadline=longest, slow_completion_time=longest+1)
    return None


def candidates(adj):
    cycle = branch['cycle_vertices'](adj)
    _, children = branch['tree_structure'](adj, cycle)
    centers = []
    for v in range(len(adj)):
        arms = sorted(path_arms(children, v), key=len, reverse=True)
        if len(arms) >= 2:
            centers.append((v, arms[:2]))
    for (u, inner), (v, outer) in combinations(centers, 2):
        assert v not in inner[0] + inner[1] and u not in outer[0] + outer[1]
        for x, y, first, second in ((u, v, inner, outer), (v, u, outer, inner)):
            result = certificate(adj, x, y, first, second)
            if result is not None:
                yield result
                break


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    data = (HERE / 'unicyclic-through-11.json').read_bytes()
    time = runpy.run_path(str(branch['BASELINE']))['completion_time']
    counts = Counter()
    records = []

    def verify(adj, cert):
        assert cert['killing'].bit_count() == 2 and cert['slow'].bit_count() == 1
        tools['verify_certificate'](time, adj, cert['blue'], cert['killing'], cert['slow'],
                                    cert['restricted_deadline'], cert['slow_completion_time'])

    for index, g in enumerate(json.loads(data)['graphs']):
        adj = tools['adjacency'](g['order'], g['edges'])
        for cert in candidates(adj):
            assert not g['every_minimum_support'], index
            verify(adj, cert)
            records.append({'graph_index': index, **cert})

    pairs = [(2, 1), (3, 1), (2, 2), (4, 3), (7, 1), (17, 5), (101, 1)]
    for n, stems, lengths in product((3, 4, 5, 9), ((0, 0), (0, 1), (1, 1), (2, 3)),
                                      product(pairs, repeat=2)):
        for second_site in sorted({1, n//2}):
            adj = list(branch['family']['cycle_graph'](n))
            centers = [attach(adj, site, depth) for site, depth in zip((0, second_site), stems)]
            for center, paths in zip(centers, lengths):
                for length in paths:
                    attach(adj, center, length)
            if max(stems) > 0:
                attach(adj, n-1, 2)
            matches = list(candidates(adj))
            if lengths[0] != lengths[1] or min(lengths[0]) >= 2 or not adj[centers[0]] & (1 << centers[1]):
                assert matches, (n, stems, lengths, centers)
            for cert in matches:
                verify(adj, cert)
                counts[cert['case']] += 1

    assert set(counts) == {'strict', 'equal_nonadjacent'}
    report = {'status': 'passed', 'census_checked': len(records), 'grid_counts': dict(counts),
              'census_sha256': hashlib.sha256(data).hexdigest(),
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'census_certificates': records}
    with args.output.open('x', encoding='utf-8') as output:
        output.write(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'census_certificates'}, indent=2))


if __name__ == '__main__':
    main()
