"""Replay a killing pair on one cycle interval and a delayed force on the next."""

import argparse
from collections import Counter
import hashlib
from itertools import product
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
branch = runpy.run_path(str(HERE / 'verify_branch_witnesses.py'))
tools = branch['tools']
bits = branch['bits']
attach = branch['attach_path']


def candidates(adj):
    cycle = branch['cycle_vertices'](adj)
    _, children = branch['tree_structure'](adj, cycle)
    leaf = {}
    for v in cycle:
        leaves = [x for x in children[v] if not children[x]]
        if len(leaves) == 1:
            leaf[v] = leaves[0]
    for a in sorted(leaf):
        order = tools['cycle_order'](adj, cycle, a)
        for ring in (order, order[:1] + order[:0:-1]):
            b_index = next((i for i, v in enumerate(ring[2:], 2)
                            if children[v]), None)
            if b_index is None:
                continue
            b = ring[b_index]
            if b not in leaf:
                continue
            interior = ring[1:b_index]
            extra = [x for x in interior if children[x]]
            if extra and (len(interior) != 1 or extra[0] not in leaf or
                          len(children[extra[0]]) != 1):
                continue
            w_index = next((i for i, v in enumerate(ring[b_index+1:], b_index+1)
                            if children[v]), None)
            if w_index is None or w_index <= b_index + 1:
                continue
            w = ring[w_index]
            if w not in leaf:
                continue
            delayed_gap = ring[b_index+1:w_index]
            whites = bits(list(interior) + list(delayed_gap[1:]) +
                          [leaf[x] for x in extra] + [leaf[w]])
            yield dict(centers=[a, b, w], first_gap=list(interior),
                       second_gap=list(delayed_gap), interior_leaf=bool(extra),
                       blue=((1 << len(adj)) - 1) ^ whites,
                       killing=bits((leaf[a], leaf[b])), slow=1 << delayed_gap[0],
                       restricted_deadline=max(len(interior)+1, len(delayed_gap)),
                       slow_completion_time=len(interior)+len(delayed_gap)+1)


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

    gaps = list(product(range(1, 9), repeat=2)) + [(71, 2), (2, 79), (63, 53)]
    for (k, g), wrap, rooted_extras, extra in product(gaps, (1, 2, 7),
                                                    (False, True), (False, True)):
        if extra and k != 1:
            continue
        b, w = k+1, k+g+2
        adj = list(branch['family']['cycle_graph'](w+wrap))
        for at in (0, b, w):
            attach(adj, at, 1)
            if rooted_extras:
                attach(adj, at, 3)
        if rooted_extras and wrap > 1:
            attach(adj, w+1, 1)
            attach(adj, w+1, 2)
        if extra:
            attach(adj, 1, 1)
        matches = [cert for cert in candidates(adj) if cert['centers'] == [0, b, w]]
        assert len(matches) == 1, (k, g, wrap, rooted_extras, extra)
        verify(adj, matches[0])
        counts['shallow_interior' if extra else 'bare_interior'] += 1

    report = {'status': 'passed', 'census_checked': len(records), 'grid_counts': dict(counts),
              'census_sha256': hashlib.sha256(data).hexdigest(),
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'census_certificates': records}
    with args.output.open('x', encoding='utf-8') as output:
        output.write(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'census_certificates'}, indent=2))


if __name__ == '__main__':
    main()
