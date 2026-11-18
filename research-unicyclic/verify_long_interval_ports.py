"""Replay a certificate on a bare cycle interval bracketed by two white paths."""

import argparse
import hashlib
from itertools import product
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
pair = runpy.run_path(str(HERE / 'verify_two_pendant_centers.py'))
branch = pair['branch']
tools = branch['tools']
bits = branch['bits']
attach = branch['attach_path']
cycle_graph = branch['family']['cycle_graph']


def selected_paths(root, children):
    leaves = sum(not children[v] for v in children[root])
    if leaves > 1:
        return []
    paths = list(pair['path_arms'](children, root))
    return [p for p in paths if not leaves or len(p) == 1]


def candidates(adj):
    cycle = branch['cycle_vertices'](adj)
    _, children = branch['tree_structure'](adj, cycle)
    for a in sorted(cycle):
        start_paths = selected_paths(a, children)
        if not start_paths:
            continue
        order = tools['cycle_order'](adj, cycle, a)
        for ring in (order, order[:1] + order[:0:-1]):
            distance = next((i for i, v in enumerate(ring[1:], 1) if children[v]), None)
            if distance is None or not 5 <= distance <= len(ring) - 3:
                continue
            b = ring[distance]
            for first, last in product(start_paths, selected_paths(b, children)):
                if len(first) > len(last):
                    continue
                whites = bits(ring[:distance+1] + first + last)
                blue = (((1 << len(adj)) - 1) ^ whites) | bits(ring[1:4])
                yield dict(centers=[a, b], lengths=[len(first), len(last)], distance=distance,
                           blue=blue, killing=bits((ring[1], ring[3])), slow=1 << ring[2],
                           restricted_deadline=distance-3+len(last),
                           slow_completion_time=distance-2+len(last))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    data = (HERE / 'unicyclic-through-11.json').read_bytes()
    time = runpy.run_path(str(branch['BASELINE']))['completion_time']
    records = []

    def verify(adj, cert):
        tools['verify_certificate'](time, adj, cert['blue'], cert['killing'], cert['slow'],
                                    cert['restricted_deadline'], cert['slow_completion_time'])

    for index, g in enumerate(json.loads(data)['graphs']):
        adj = tools['adjacency'](g['order'], g['edges'])
        for cert in candidates(adj):
            assert not g['every_minimum_support'], index
            verify(adj, cert)
            records.append({'graph_index': index, **cert})

    checked = 0
    for k, side, (short, long), extras in product((4, 5, 6, 12, 37, 100),
                                                   (2, 3, 6), ((1, 1), (1, 3), (2, 2),
                                                               (3, 11), (11, 11), (2, 127)),
                                                   (0, 1, 2, 3)):
        b = k+1
        adj = list(cycle_graph(k+2+side))
        attach(adj, 0, short)
        attach(adj, b, long)
        if extras & 1:
            for v in (0, b):
                tip = attach(adj, v, 2)
                attach(adj, tip, 1)
                attach(adj, tip, 3)
        if extras & 2:
            cycle_size = k+2+side
            for i in range(b+1, cycle_size):
                attach(adj, i, 1)
                if i % 2:
                    attach(adj, i, 2)
        cert = next(c for c in candidates(adj) if c['centers'] == [0, b])
        verify(adj, cert)
        checked += 1

    report = {'status': 'passed', 'census_checked': len(records), 'grid_checked': checked,
              'census_sha256': hashlib.sha256(data).hexdigest(),
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'census_certificates': records}
    with args.output.open('x', encoding='utf-8') as output:
        output.write(json.dumps(report, indent=2) + '\n')
    print(f'Passed {len(records)} census certificates and {checked} parameter instances.')


if __name__ == '__main__':
    main()
