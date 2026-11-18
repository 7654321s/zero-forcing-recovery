"""Replay local counterexamples at the outermost non-trivial branch of a unicyclic graph."""

import argparse
from collections import Counter, deque
import hashlib
from itertools import combinations_with_replacement
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
tools = runpy.run_path(str(HERE / 'verify_site_witnesses.py'))
neighbors = tools['neighbors']
bits = tools['bits']
BASELINE = tools['BASELINE']
cycle_vertices = tools['cycle_vertices']
twins = tools['helpers']['twins']
family = tools['family']


def tree_structure(adj, cycle):
    parent = {v: None for v in cycle}
    children = {v: [] for v in range(len(adj))}
    waiting = deque(sorted(cycle))
    while waiting:
        v = waiting.popleft()
        for w in neighbors(adj[v]):
            if w not in parent:
                parent[w] = v
                children[v].append(w)
                waiting.append(w)
    return parent, children


def pendant_paths(v, children):
    arms = []
    for w in children[v]:
        path = [w]
        while children[w]:
            if len(children[w]) != 1:
                return None
            w = children[w][0]
            path.append(w)
        arms.append(path)
    return sorted(arms, key=lambda x: (len(x), x[0]))


def branch_witness(adj, cycle):
    parent, children = tree_structure(adj, cycle)
    full = (1 << len(adj)) - 1
    twinned = {x for pair in twins(adj) for x in pair}
    for a in range(len(adj)):
        if a in cycle or len(children[a]) < 2:
            continue
        arms = pendant_paths(a, children)
        if arms is None or sum(len(x) == 1 for x in arms) > 1:
            continue
        p = parent[a]
        if len(arms[0]) >= 2:
            y = next((w for w in neighbors(adj[p])
                      if w != a and adj[w].bit_count() > 1 and w not in twinned), None)
            if y is None:
                continue
            blue = full ^ ((1 << y) | bits(v for arm in arms for v in arm[1:]))
            support = bits((arms[0][0], arms[-1][0]))
            longest = len(arms[-1])
            return dict(case='all_long_delayed_center', center=a, external_white=y, blue=blue,
                        killing=support, slow=1 << a, restricted_deadline=longest,
                        slow_completion_time=longest+1)
        if len(arms) >= 3:
            longest = arms[-1]
            other = arms[-2]
            whites = bits(longest[:-1]) | bits(v for arm in arms[:-1] for v in arm[1:])
            return dict(case='protected_center_one_short', center=a, blue=full ^ whites,
                        killing=bits((arms[0][0], longest[-1])), slow=1 << other[0],
                        restricted_deadline=len(longest),
                        slow_completion_time=len(longest)+len(other)-1)
    return None


def attach_path(adj, at, length):
    for _ in range(length):
        family['add_leaves'](adj, at, 1)
        at = len(adj) - 1
    return at


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    data = (HERE / 'unicyclic-through-11.json').read_bytes()
    time = runpy.run_path(str(BASELINE))['completion_time']
    counts = Counter()
    records = []

    def verify(adj, cert):
        assert cert['killing'].bit_count() == 2 and cert['slow'].bit_count() == 1
        tools['verify_certificate'](time, adj, cert['blue'], cert['killing'], cert['slow'],
                                    cert['restricted_deadline'], cert['slow_completion_time'])

    for index, g in enumerate(json.loads(data)['graphs']):
        adj = tools['adjacency'](g['order'], g['edges'])
        cycle = cycle_vertices(adj)
        cert = branch_witness(adj, cycle)
        if cert is not None:
            assert not g['every_minimum_support'], index
            verify(adj, cert)
            records.append({'graph_index': index, **cert})

    for n in (5, 6, 7, 9, 12, 16):
        for stem in (1, 2, 4):
            for length in (2, 3, 4):
                vectors = list(combinations_with_replacement(range(1, 7), length))
                if length == 2:
                    vectors.append((3, 127))
                if length == 3:
                    vectors.append((1, 2, 100))
                for arms in vectors:
                    if arms.count(1) > 1 or (length == 2 and arms[0] == 1):
                        continue
                    adj = list(family['cycle_graph'](n))
                    root = attach_path(adj, 0, stem)
                    for size in arms:
                        attach_path(adj, root, size)
                    # Extra arms at a different cycle site exercise the exterior argument.
                    if stem % 2 == 0:
                        attach_path(adj, 2, 3)
                    cert = branch_witness(adj, set(range(n)))
                    assert cert is not None
                    verify(adj, cert)
                    counts[cert['case']] += 1

    report = {'status': 'passed', 'census_checked': len(records), 'grid_counts': dict(counts),
              'census_sha256': hashlib.sha256(data).hexdigest(),
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'census_certificates': records}
    with args.output.open('x', encoding='utf-8') as output:
        output.write(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'census_certificates'}, indent=2))


if __name__ == '__main__':
    main()
