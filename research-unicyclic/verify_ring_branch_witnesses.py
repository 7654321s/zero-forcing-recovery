"""Replay local counterexamples at a cycle vertex with several pendant paths."""

import argparse
from collections import Counter
import hashlib
from itertools import combinations_with_replacement
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
branch = runpy.run_path(str(HERE / 'verify_branch_witnesses.py'))
tools = branch['tools']
bits = branch['bits']
attach_path = branch['attach_path']
cycle_graph = branch['family']['cycle_graph']


def blockers(adj, cycle, children, a):
    ring = tools['cycle_order'](adj, cycle, a)
    n = len(ring)
    left = next((v for v in children[ring[1]] if children[v]), None)
    right = next((v for v in children[ring[-1]] if children[v]), None)
    if left is not None and right is not None:
        return 'two_off_cycle_blockers', (left, right)
    if n >= 5 and left is not None:
        return 'mixed_blockers', (left, ring[-2])
    if n >= 5 and right is not None:
        return 'mixed_blockers', (ring[2], right)
    if n >= 7 or (n in (5, 6) and (children[ring[2]] or children[ring[-2]])):
        return 'two_ring_blockers', (ring[2], ring[-2])
    if n == 4 and children[ring[2]]:
        return 'opposite_ring_blocker', (ring[2],)
    return None


def ring_witnesses(adj, cycle):
    _, children = branch['tree_structure'](adj, cycle)
    full = (1 << len(adj)) - 1
    for a in sorted(cycle):
        arms = branch['pendant_paths'](a, children)
        if arms is None or len(arms) < 2:
            continue
        longest = arms[-1]
        length = len(longest)
        if len(arms[0]) >= 2:
            result = blockers(adj, cycle, children, a)
            if result is None:
                continue
            case, exterior_whites = result
            arm_whites = bits(v for arm in arms for v in arm[1:])
            yield dict(case=case, center=a, exterior_whites=exterior_whites,
                       blue=full ^ (arm_whites | bits(exterior_whites)),
                       killing=bits((arms[0][0], longest[0])), slow=1 << a,
                       restricted_deadline=length, slow_completion_time=length+1)
        elif len(arms) >= 3 and len(arms[1]) >= 2:
            other = arms[-2]
            arm_whites = bits(longest[:-1]) | bits(v for arm in arms[:-1] for v in arm[1:])
            yield dict(case='protected_center_one_short', center=a, blue=full ^ arm_whites,
                       killing=bits((arms[0][0], longest[-1])), slow=1 << other[0],
                       restricted_deadline=length, slow_completion_time=length+len(other)-1)


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
        for cert in ring_witnesses(adj, branch['cycle_vertices'](adj)):
            assert not g['every_minimum_support'], index
            verify(adj, cert)
            records.append({'graph_index': index, **cert})

    for n in range(3, 17):
        cycle = set(range(n))
        exteriors = [(), ((1, 2),), ((n-1, 2),), ((1, 2), (n-1, 3))]
        if n >= 4:
            exteriors.extend([((2, 1),), ((n-2, 2),), ((2, 1), (n-2, 2), (1, 1))])
        vectors = [(2, 127), (1, 2, 100)]
        for size in (2, 3):
            vectors.extend(arms for arms in combinations_with_replacement(range(1, 6), size)
                           if arms.count(1) == 0 or (size == 3 and arms.count(1) == 1))
        for exterior in exteriors:
            for arms in vectors:
                adj = list(cycle_graph(n))
                for at, length in exterior:
                    attach_path(adj, at, length)
                for length in arms:
                    attach_path(adj, 0, length)
                for cert in ring_witnesses(adj, cycle):
                    verify(adj, cert)
                    counts[cert['case']] += 1

    assert set(counts) == {'two_off_cycle_blockers', 'mixed_blockers', 'two_ring_blockers',
                           'opposite_ring_blocker', 'protected_center_one_short'}
    report = {'status': 'passed', 'census_checked': len(records), 'grid_counts': dict(counts),
              'census_sha256': hashlib.sha256(data).hexdigest(),
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'census_certificates': records}
    with args.output.open('x', encoding='utf-8') as output:
        output.write(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'census_certificates'}, indent=2))


if __name__ == '__main__':
    main()
