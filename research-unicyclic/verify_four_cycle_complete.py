"""Close the four-cycle classification with leaf clocks and finite root pairs."""

import argparse
from collections import Counter
import hashlib
from itertools import product
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
prior = runpy.run_path(str(HERE / 'verify_four_cycle_branch.py'))
branch = prior['branch']
pair = prior['pair']
dense = prior['dense']
tools = prior['tools']
bits = prior['bits']
neighbors = prior['neighbors']
attach = prior['attach']

# Canonical roots are 0,1,2,3. Add the two paths at 0, then the listed leaves.
AT_ROOT = {
    ((1, 3), (1, 2)): ((0, 1, 2, 4, 5, 7), (2, 7), 1, 2, 3),
    ((1, 3), (1, 3)): ((1, 2, 4, 5, 8), (1, 8), 5, 3, 4),
    ((1, 3), (2, 2)): ((1, 2, 4, 5, 8), (1, 8), 2, 4, 5),
    ((1, 3), (2, 3)): ((1, 2, 4, 5, 9), (1, 9), 2, 5, 6),
    ((1, 3), (3, 3)): ((0, 2, 3, 4, 6, 10), (2, 10), 3, 4, 5),
    ((1, 2), (1, 2)): ((0, 1, 3, 4, 5), (1, 4), 0, 2, 3),
    ((1, 2), (1, 3)): ((0, 1, 3, 4, 5), (1, 4), 0, 2, 3),
    ((1, 2), (2, 2)): ((0, 1, 3, 5, 6), (1, 5), 3, 3, 4),
    ((1, 2), (2, 3)): ((0, 1, 2, 3, 4, 6), (1, 3), 0, 2, 3),
    ((1, 2), (3, 3)): ((0, 1, 2, 3, 4, 7), (1, 3), 0, 2, 3),
    ((1, 2, 3), (1, 2)): ((0, 2, 3, 4, 5, 7), (4, 7), 2, 2, 3),
    ((1, 2, 3), (1, 3)): ((2, 3, 4, 5, 8), (2, 8), 5, 3, 4),
    ((1, 2, 3), (2, 2)): ((0, 1, 2, 3, 5, 6, 8), (2, 8), 3, 2, 3),
    ((1, 2, 3), (2, 3)): ((0, 2, 3, 4, 6, 9), (2, 9), 6, 3, 4),
    ((1, 2, 3), (3, 3)): ((0, 2, 3, 4, 7, 10), (2, 10), 4, 3, 4),
}


def rooted_vertices(children, a):
    pending = [a]
    while pending:
        v = pending.pop()
        yield v
        pending.extend(children[v])


def candidates(adj, cycle, children):
    if len(cycle) != 4:
        return
    paths = dense['paths_at'](children, cycle)
    nonpaths = [v for v in cycle if children[v] and v not in paths]
    if len(nonpaths) != 1 or len(paths) < 2 or any(len(w) != 1 for w in paths.values()):
        return
    a = nonpaths[0]
    ring = tools['cycle_order'](adj, cycle, a)
    if not children[ring[1]]:
        ring = ring[:1] + ring[:0:-1]
    p, t, q = ring[1:]
    full = (1 << len(adj)) - 1

    arms = branch['pendant_paths'](a, children)
    if arms and len(arms) >= 2 and len(arms[1]) <= 3 and len(arms[1]) >= 2:
        positions = tuple(i for i, v in enumerate(ring) if v in paths)
        lengths = tuple(map(len, arms[:2]))
        verts = ring + arms[0] + arms[1] + [paths[ring[i]][0] for i in positions]
        blue, H, slow, early, late = AT_ROOT[positions, lengths]
        white = bits(verts) ^ bits(verts[i] for i in blue)
        yield dense['record']('short_root_pair', full, white, (verts[i] for i in H),
                              verts[slow], early, late)

    for u in rooted_vertices(children, a):
        arms = sorted(pair['path_arms'](children, u), key=len)
        if not children[t] and p in paths and q in paths:
            for path in arms:
                if len(path) >= 4:
                    white = bits([p, paths[q][0], *path[1:]])
                    waits_two = bool(adj[u] & (1 << a)) and len(children[u]) == 1
                    delayed = len(path) + waits_two
                    yield dense['record']('long_arm_with_bare_opposite', full, white,
                                          (paths[p][0], q), u, len(path)-1, delayed)
        if u == a or len(arms) < 2 or not 2 <= len(arms[1]) <= 3:
            continue
        first, second = arms[:2]
        white = dense['partial_path'](first, True) | dense['partial_path'](second, True)
        if q in paths:
            white |= bits((p, q))
            slow = paths[p][0]
            case = 'opposite_leaves_recover'
        else:
            white |= bits((t, paths[p][0], paths[t][0]))
            slow = q
            case = 'bare_vertex_delays_leaf'
        yield dense['record'](case, full, white, (first[0], second[0]), slow, 2, 3)


def step(adj, blue):
    added = 0
    for v in neighbors(blue):
        w = adj[v] & ~blue
        if w.bit_count() == 1:
            added |= w
    return blue | added


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    data = (HERE / 'unicyclic-through-11.json').read_bytes()
    time = runpy.run_path(str(branch['BASELINE']))['completion_time']
    counts = Counter()
    rows = []
    scope = 0

    def verify(adj, c):
        tools['verify_certificate'](time, adj, c['blue'], c['killing'], c['slow'],
                                    c['restricted_deadline'], c['slow_completion_time'])

    for (sites, arms), (blue, H, z, early, late) in AT_ROOT.items():
        adj = list(branch['family']['cycle_graph'](4))
        for length in arms:
            attach(adj, 0, length)
        for v in sites:
            attach(adj, v, 1)
        for loss in ((), H, (H[0],), (H[1],), (z,)):
            assert step(adj, bits(blue) ^ bits(loss)) & 1
        verify(adj, dict(blue=bits(blue), killing=bits(H), slow=1 << z,
                         restricted_deadline=early, slow_completion_time=late))
        counts['root_table'] += 1

    for index, g in enumerate(json.loads(data)['graphs']):
        if g['cycle_length'] != 4:
            continue
        adj = tools['adjacency'](g['order'], g['edges'])
        cycle = branch['cycle_vertices'](adj)
        _, children = branch['tree_structure'](adj, cycle)
        assert g['every_minimum_support'] == (len(adj) == 4)
        scope += 1
        for c in candidates(adj, cycle, children):
            verify(adj, c)
            rows.append({'graph_index': index, **c})

    for sites, (small, long), depth, extra in product(
            ((1, 3), (1, 2), (1, 2, 3)),
            ((1, 2), (1, 3), (2, 2), (2, 3), (3, 3), (1, 7), (3, 43)),
            (0, 1, 6, 51), (False, True)):
        adj = list(branch['family']['cycle_graph'](4))
        a = attach(adj, 0, depth)
        attach(adj, a, small)
        attach(adj, a, long)
        if extra:
            attach(adj, a, 2)
            if depth:
                attach(adj, 0, 3)
        for v in sites:
            attach(adj, v, 1)
        cycle = set(range(4))
        _, children = branch['tree_structure'](adj, cycle)
        cases = list(candidates(adj, cycle, children))
        if not cases:
            cases = list(prior['opposite_slow_arm'](adj, cycle, children))
        assert cases, (sites, small, long, depth, extra)
        for cert in cases:
            verify(adj, cert)
            counts[cert['case']] += 1

    report = {'status': 'passed', 'cycle_four_census_scope': scope, 'census_checked': len(rows),
              'grid_counts': dict(counts), 'census_sha256': hashlib.sha256(data).hexdigest(),
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'census_certificates': rows}
    with args.output.open('x', encoding='utf-8') as output:
        output.write(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'census_certificates'}, indent=2))


if __name__ == '__main__':
    main()
