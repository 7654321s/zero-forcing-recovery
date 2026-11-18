"""Replay a killing pair with internal seeds and a delayed remote path."""

import argparse
from collections import Counter
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


def certificate(adj, u, v, a, b, remote):
    length = len(remote)
    deadline = max(length-1, (max(len(a), len(b)) + 2) // 2)
    if deadline >= length:
        return None
    full = (1 << len(adj)) - 1
    whites = bits(remote[1:])
    for arm in (a, b):
        kept = bits(arm[:1] + arm[1:-1:2])
        whites |= bits(arm) ^ kept
    return dict(centers=[u, v], arms=[a, b, remote], blue=full ^ whites,
                killing=bits((a[0], b[0])), slow=1 << v,
                restricted_deadline=deadline, slow_completion_time=length)


def candidates(adj):
    _, children = branch['tree_structure'](adj, branch['cycle_vertices'](adj))
    at = [sorted(pair['path_arms'](children, v), key=len) for v in range(len(adj))]
    for u, paths in enumerate(at):
        if len(paths) < 2:
            continue
        for v, other in enumerate(at):
            if v == u or not other:
                continue
            arm = other[-1]
            if v in paths[0] or v in paths[1] or u in arm:
                continue
            result = certificate(adj, u, v, paths[0], paths[1], arm)
            if result is not None:
                yield result


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

    dimensions = [(2, 1), (3, 1), (3, 3), (4, 2), (8, 4), (13, 1), (57, 13)]
    for n, stems, lengths, delay in product((3, 5, 8), ((0, 0), (0, 1), (1, 1), (2, 4)),
                                               dimensions, (2, 3, 4, 6, 8, 30, 61)):
        adj = list(branch['family']['cycle_graph'](n))
        u, v = [attach(adj, site, depth) for site, depth in zip((0, 1), stems)]
        for m in lengths:
            attach(adj, u, m)
        attach(adj, v, delay)
        if n > 3:
            attach(adj, n-1, 1)
        matches = [cert for cert in candidates(adj) if cert['centers'] == [u, v]]
        assert bool(matches) == (max(lengths) <= 2 * delay - 3)
        for cert in matches:
            verify(adj, cert)
            counts['adjacent' if adj[u] & (1 << v) else 'nonadjacent'] += 1

    assert set(counts) == {'adjacent', 'nonadjacent'}
    report = {'status': 'passed', 'census_checked': len(records), 'grid_counts': dict(counts),
              'census_sha256': hashlib.sha256(data).hexdigest(),
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'census_certificates': records}
    with args.output.open('x', encoding='utf-8') as output:
        output.write(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'census_certificates'}, indent=2))


if __name__ == '__main__':
    main()
