"""Replay the four-cycle three-site obstruction with delayed inward recovery."""

import argparse
from collections import Counter
import hashlib
from itertools import product
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
dense = runpy.run_path(str(HERE / 'verify_dense_path_sites.py'))
branch = dense['branch']
tools = dense['tools']
bits = branch['bits']
with_paths = dense['with_paths']


def candidates(adj):
    cycle = branch['cycle_vertices'](adj)
    if len(cycle) != 4:
        return
    _, children = branch['tree_structure'](adj, cycle)
    bare = [v for v in cycle if not children[v]]
    if len(bare) != 1:
        return
    t = bare[0]
    order = tools['cycle_order'](adj, cycle, t)
    full = (1 << len(adj)) - 1
    for p, x, q in (order[1:], order[:0:-1]):
        at_p = branch['pendant_paths'](p, children)
        at_x = branch['pendant_paths'](x, children)
        at_q = branch['pendant_paths'](q, children)
        if at_p is None or at_x is None or len(at_x) != 1 or at_q is None or len(at_q) != 1:
            continue
        leaves = sum(len(path) == 1 for path in at_p)
        if leaves > 1:
            continue
        selected = at_p[0] if leaves else at_p[-1]
        other = [path for path in at_p if path != selected]
        p_time = max((len(path)+1 for path in other), default=0)//2
        side = max(len(at_x[0]), len(at_q[0]))
        white = bits(selected[:-1] + at_x[0] + at_q[0]) | (1 << q)
        for path in other:
            white |= bits(path) ^ bits(path[:-1:2])
        early = max(len(selected)+side, p_time)
        late = len(selected) + max(1+side, p_time)
        yield dense['record']('four_cycle_three_sites', full, white,
                              (x, selected[-1]), p, early, late)


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
        if g['cycle_length'] != 4:
            continue
        adj = tools['adjacency'](g['order'], g['edges'])
        for cert in candidates(adj):
            assert not g['every_minimum_support'], index
            verify(adj, cert)
            cases.append({'graph_index': index, **cert})

    for end, x, q in product(((1,), (2,), (3,), (37,), (2, 2), (1, 2), (1, 31),
                               (2, 3, 6), (3, 4, 23)), (1, 2, 3, 8, 47), (1, 2, 6, 41)):
        adj = with_paths(4, {0: end, 1: (x,), 2: (q,)})
        matched = list(candidates(adj))
        assert matched, (end, x, q)
        for cert in matched:
            verify(adj, cert)
            counts['one_path_at_every_site' if len(end) == 1 else 'multiple_paths_at_endpoint'] += 1

    report = {'status': 'passed', 'census_checked': len(cases),
              'grid_counts': dict(counts),
              'census_sha256': hashlib.sha256(data).hexdigest(),
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'census_certificates': cases}
    with args.output.open('x', encoding='utf-8') as output:
        output.write(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'census_certificates'}, indent=2))


if __name__ == '__main__':
    main()
