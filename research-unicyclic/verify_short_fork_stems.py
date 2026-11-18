"""Replay short-fork stem certificates completing the triangular two-site case."""

import argparse
from collections import Counter
import hashlib
from itertools import product
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
triangle = runpy.run_path(str(HERE / 'verify_triangle_tree_path.py'))
pair = triangle['pair']
branch = pair['branch']
tools = branch['tools']
bits = branch['bits']
attach = branch['attach_path']


def record(case, white, full, killing, slow, early, late):
    return triangle['record'](case, full ^ bits(white), killing, slow, early, late)


def candidates(adj):
    cycle = branch['cycle_vertices'](adj)
    parent, children = branch['tree_structure'](adj, cycle)
    full = (1 << len(adj)) - 1
    for u in sorted(set(range(len(adj))) - cycle):
        arms = branch['pendant_paths'](u, children)
        if arms is None or len(arms) != 2 or len(arms[0]) != 1 or len(arms[1]) < 2:
            continue
        short, long = arms
        stem = [u]
        side_tips = []
        while parent[stem[-1]] is not None:
            lower = stem[-1]
            p = parent[lower]
            branches = [v for v in children[p] if v != lower]
            leaves = [v for v in branches if not children[v]]
            distance = len(stem)
            if len(leaves) == 1:
                interior = stem[1:] if distance > 1 else [u]
                end = max(distance, len(long)-1) if distance > 1 else len(long)
                slow = distance + len(long) - 1 if distance > 1 else len(long)+1
                yield record('two_stem_leaves', interior + side_tips + long[1:], full,
                             (leaves[0], short[0]), long[0], end, slow)

            if branches and not leaves and not side_tips and len(long) == 2:
                if distance >= 2:
                    yield record('nonleaf_stem_start', stem[1:] + short, full,
                                 long, p, distance, distance+1)
                elif p not in cycle:
                    y = parent[p]
                    if all(adj[x].bit_count() > 1 for x in branch['neighbors'](adj[y])):
                        for side in pair['path_arms'](children, p):
                            if len(side) == 2:
                                yield record('adjacent_nonleaf_stem_start', [p, *short, side[-1]],
                                             full, long, side[0], 2, 3)
            if not all(len(children[v]) == 1 and not children[children[v][0]]
                       for v in branches):
                break
            side_tips.extend(children[v][0] for v in branches)
            stem.append(p)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    data = (HERE / 'unicyclic-through-11.json').read_bytes()
    time = runpy.run_path(str(branch['BASELINE']))['completion_time']
    counts = Counter()
    records = []
    previous_reports = (
        'site-witness', 'two-sites-path', 'branch-witness', 'ring-branch-witness',
        'two-pendant-centers', 'compressed-pendant-pair', 'two-site-exhaustion', 'triangle-tree-path',
    )
    previous = {c['graph_index'] for name in previous_reports
                for c in json.loads((HERE / f'{name}-replay.json').read_bytes())['census_certificates']}
    remaining = []
    triangular_scope = 0

    def verify(adj, cert):
        tools['verify_certificate'](time, adj, cert['blue'], cert['killing'], cert['slow'],
                                    cert['restricted_deadline'], cert['slow_completion_time'])

    for index, g in enumerate(json.loads(data)['graphs']):
        adj = tools['adjacency'](g['order'], g['edges'])
        new = list(candidates(adj))
        for cert in new:
            assert not g['every_minimum_support'], index
            verify(adj, cert)
            records.append({'graph_index': index, **cert})
        if g['cycle_length'] != 3:
            continue
        cycle = branch['cycle_vertices'](adj)
        _, children = branch['tree_structure'](adj, cycle)
        if sum(bool(children[v]) for v in cycle) != 2:
            continue
        triangular_scope += 1
        if (not g['every_minimum_support'] and index not in previous
                and not branch['twins'](adj) and any(len(ch) > 1 for ch in children.values())):
            assert new, index
            remaining.append(index)

    for n, top, gap, length, variant in product((3, 4, 7), (0, 1, 4), (1, 2, 5, 31, 83),
                                                (2, 3, 10), ('leaf', 'side_paths', 'bare')):
        adj = list(branch['family']['cycle_graph'](n))
        p = attach(adj, 0, top)
        if variant == 'bare':
            attach(adj, p, 2)
        else:
            attach(adj, p, 1)
        v = p
        for i in range(1, gap+1):
            v = attach(adj, v, 1)
            if i < gap and variant == 'side_paths':
                attach(adj, v, 2)
        attach(adj, v, 1)
        attach(adj, v, length)
        # A blue attachment elsewhere tests the retained-graph argument.
        attach(adj, 1, 1)
        matches = list(candidates(adj))
        if variant != 'bare' or (length == 2 and (top or gap > 1)):
            assert matches, (n, top, gap, length, variant)
        for cert in matches:
            verify(adj, cert)
            counts[cert['case']] += 1

    report = {'status': 'passed', 'census_checked': len(records),
              'two_site_triangle_census_scope': triangular_scope, 'previous_residual_indices': remaining,
              'grid_counts': dict(counts), 'census_sha256': hashlib.sha256(data).hexdigest(),
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'census_certificates': records}
    with args.output.open('x', encoding='utf-8') as output:
        output.write(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'census_certificates'}, indent=2))


if __name__ == '__main__':
    main()
