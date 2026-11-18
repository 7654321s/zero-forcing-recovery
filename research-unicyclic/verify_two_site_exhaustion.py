"""Replay the missing two-site certificates and the adjacent short-pair exception."""

import argparse
from collections import Counter
import hashlib
from itertools import product
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
branch = runpy.run_path(str(HERE / 'verify_branch_witnesses.py'))
sites = runpy.run_path(str(HERE / 'verify_two_sites_path.py'))
tools = branch['tools']
neighbors = branch['neighbors']
bits = branch['bits']
attach = branch['attach_path']


def adjacent_short_pair(adj, cycle, u, v, arms_u, arms_v):
    if not adj[u] & (1 << v) or not (adj[v] & bits(cycle - {u, v})):
        return None
    short_u = [arm for arm in arms_u if len(arm) == 1]
    short_v = [arm for arm in arms_v if len(arm) == 1]
    long_u = next((arm for arm in arms_u if len(arm) == 2), None)
    long_v = next((arm for arm in arms_v if len(arm) == 2), None)
    if len(short_u) != 1 or not short_v or long_u is None or long_v is None:
        return None
    white = bits((v, short_u[0][0], long_v[-1]))
    return dict(case='adjacent_short_pair', centers=[u, v],
                blue=((1 << len(adj)) - 1) ^ white, killing=bits(long_u),
                slow=1 << long_v[0], restricted_deadline=2, slow_completion_time=3)


def adjacent_candidates(adj, cycle, children):
    arms = {u: branch['pendant_paths'](u, children) for u in cycle}
    # The structural exhaustion only needs centers whose child subtrees are paths.
    for u in sorted(cycle):
        if arms[u] is None:
            continue
        for v in sorted(cycle.intersection(neighbors(adj[u]))):
            if arms[v] is not None:
                cert = adjacent_short_pair(adj, cycle, u, v, arms[u], arms[v])
                if cert is not None:
                    yield cert


def separated_two_sites(adj, cycle, attachments):
    a, b = sorted(attachments)
    ring = tools['cycle_order'](adj, cycle, a)
    n = len(ring)
    if ring.index(b) > n // 2:
        ring = ring[:1] + ring[:0:-1]
    distance = ring.index(b)
    if distance < 3 or (n % 2 == 0 and n - distance < 5):
        return None
    support = bits((ring[1], ring[-1]))
    blue = bits(set(range(len(adj))) - cycle) | bits((a, b)) | support
    if n % 2 == 0:
        blue |= 1 << ring[-3]
    white = n - (blue & bits(cycle)).bit_count()
    assert white % 2 == 1
    return dict(case='separated_two_sites', centers=[a, b], blue=blue, killing=support,
                slow=1 << a, restricted_deadline=(white+1)//2,
                slow_completion_time=(white+3)//2)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    data = (HERE / 'unicyclic-through-11.json').read_bytes()
    time = runpy.run_path(str(branch['BASELINE']))['completion_time']
    counts = Counter()
    records = []
    complete_scope = 0
    pair = runpy.run_path(str(HERE / 'verify_two_pendant_centers.py'))
    remote = runpy.run_path(str(HERE / 'verify_compressed_pendant_pair.py'))
    family = branch['family']

    def verify(adj, cert):
        assert cert['killing'].bit_count() == 2 and cert['slow'].bit_count() == 1
        tools['verify_certificate'](time, adj, cert['blue'], cert['killing'], cert['slow'],
                                    cert['restricted_deadline'], cert['slow_completion_time'])

    for index, g in enumerate(json.loads(data)['graphs']):
        adj = tools['adjacency'](g['order'], g['edges'])
        cycle = branch['cycle_vertices'](adj)
        _, children = branch['tree_structure'](adj, cycle)
        roots = {u for u in cycle if children[u]}
        adjacent = list(adjacent_candidates(adj, cycle, children))
        separated = separated_two_sites(adj, cycle, roots) if len(roots) == 2 else None
        for cert in adjacent + ([separated] if separated else []):
            assert not g['every_minimum_support'], index
            verify(adj, cert)
            records.append({'graph_index': index, **cert})
        if len(roots) == 2 and len(cycle) >= 4:
            assert not g['every_minimum_support'], index
            if not branch['twins'](adj):
                cert = next(iter(adjacent), None) or separated or sites['witness'](adj, cycle, roots)
                if cert is None:
                    cert = (next(pair['candidates'](adj), None) or next(remote['candidates'](adj), None))
                assert cert is not None, index
                verify(adj, cert)
            complete_scope += 1

    for n, extra in product((*range(3, 26), 47, 101), range(4)):
        adj = list(family['cycle_graph'](n))
        for u in (0, 1):
            attach(adj, u, 1)
            attach(adj, u, 2)
            if extra & 2:
                attach(adj, u, 4)
        if extra & 1:
            for u in range(2, n):
                attach(adj, u, 1)
                if u % 2 == 0:
                    attach(adj, u, 2)
        cycle = set(range(n))
        _, children = branch['tree_structure'](adj, cycle)
        cert = next(adjacent_candidates(adj, cycle, children))
        verify(adj, cert)
        counts[cert['case']] += 1

    for n in (*range(6, 28), 40, 61, 128):
        for d, length in product(range(3, n//2+1), (1, 2, 3, 11)):
            adj = list(family['cycle_graph'](n))
            attach(adj, 0, length)
            if length % 2:
                attach(adj, 0, 4)
            attach(adj, d, 3)
            if length % 3:
                attach(adj, d, 1)
            cert = separated_two_sites(adj, set(range(n)), (0, d))
            if n in (6, 8) and n == 2*d:
                assert cert is None
                continue
            assert cert is not None
            verify(adj, cert)
            counts[cert['case']] += 1

    report = {'status': 'passed', 'census_certificates': records,
              'census_checked': len(records), 'complete_two_site_scope': complete_scope,
              'grid_counts': dict(counts),
              'census_sha256': hashlib.sha256(data).hexdigest(),
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    with args.output.open('x', encoding='utf-8') as output:
        output.write(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'census_certificates'}, indent=2))


if __name__ == '__main__':
    main()
