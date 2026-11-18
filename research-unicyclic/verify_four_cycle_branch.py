"""Replay four-cycle branch certificates and the strengthened fork comparison."""

import argparse
from collections import Counter
import hashlib
from itertools import product
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
four = runpy.run_path(str(HERE / 'verify_four_cycle_three_sites.py'))
branch = four['branch']
pair = runpy.run_path(str(HERE / 'verify_two_pendant_centers.py'))
dense = four['dense']
tools = four['tools']
bits = four['bits']
attach = branch['attach_path']
neighbors = branch['neighbors']


def fork_and_remote(adj, cycle, children):
    paths = dense['paths_at'](children, cycle)
    full = (1 << len(adj)) - 1
    for u in range(len(adj)):
        arms = sorted(pair['path_arms'](children, u), key=len)
        if len(arms) < 2:
            continue
        first, second = arms[:2]
        for a, target in paths.items():
            if a == u or u in target or len(second) > 2*len(target)-1:
                continue
            white = bits(target) | dense['partial_path'](first, True)
            white |= dense['partial_path'](second, True)
            slow = next(v for v in neighbors(adj[a]) if v in cycle)
            yield dense['record']('fork_and_white_remote', full, white,
                                  (first[0], second[0]), slow, len(target), len(target)+1)


def opposite_slow_arm(adj, cycle, children):
    if len(cycle) != 4:
        return
    paths = dense['paths_at'](children, cycle)
    if sum(bool(children[v]) and v not in paths for v in cycle) != 1:
        return
    a = next(v for v in cycle if children[v] and v not in paths)
    ring = tools['cycle_order'](adj, cycle, a)
    p, t, q = ring[1:]
    arms = [paths.get(v, []) for v in (p, q)]
    length = max(map(len, arms))
    if not children[t] and length < 2:
        return
    bound = 1 + (length+1)//2
    full = (1 << len(adj)) - 1
    pending = [a]
    while pending:
        u = pending.pop()
        pending.extend(children[u])
        for arm in pair['path_arms'](children, u):
            if len(arm) <= bound:
                continue
            white = bits(arm[1:])
            for remote in arms:
                white |= bits(remote) ^ bits(remote[:-1:2])
            yield dense['record']('opposite_pair', full, white, (p, q), u,
                                  max(len(arm)-1, bound), len(arm))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    data = (HERE / 'unicyclic-through-11.json').read_bytes()
    time = runpy.run_path(str(branch['BASELINE']))['completion_time']
    counts = Counter()
    cases = []

    def verify(adj, cert):
        tools['verify_certificate'](time, adj, cert['blue'], cert['killing'], cert['slow'],
                                    cert['restricted_deadline'], cert['slow_completion_time'])

    for index, g in enumerate(json.loads(data)['graphs']):
        adj = tools['adjacency'](g['order'], g['edges'])
        cycle = branch['cycle_vertices'](adj)
        _, children = branch['tree_structure'](adj, cycle)
        found = [*fork_and_remote(adj, cycle, children), *opposite_slow_arm(adj, cycle, children)]
        for cert in found:
            assert not g['every_minimum_support'], index
            verify(adj, cert)
            cases.append({'graph_index': index, **cert})

    for depth, (short, long), other in product(
            (0, 1, 7), ((1, 2), (2, 3), (1, 4), (2, 17), (6, 47)), (
                (0, 1, 2), (1, 0, 3), (2, 0, 2), (2, 1, 5), (1, 5, 1), (9, 1, 2))):
        adj = list(branch['family']['cycle_graph'](4))
        for r, L in enumerate(other, start=1):
            attach(adj, r, L)
        u = attach(adj, 0, depth)
        attach(adj, u, short)
        attach(adj, u, long)
        cycle = {0, 1, 2, 3}
        _, children = branch['tree_structure'](adj, cycle)
        matches = [*fork_and_remote(adj, cycle, children), *opposite_slow_arm(adj, cycle, children)]
        assert matches, (depth, short, long, other)
        for cert in matches:
            verify(adj, cert)
            counts[cert['case']] += 1

    report = {'status': 'passed', 'census_checked': len(cases), 'grid_counts': dict(counts),
              'census_sha256': hashlib.sha256(data).hexdigest(),
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'census_certificates': cases}
    with args.output.open('x', encoding='utf-8') as output:
        output.write(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'census_certificates'}, indent=2))


if __name__ == '__main__':
    main()
