"""Replay certificate extensions that may add a single blue leaf."""

import argparse
from collections import Counter
import hashlib
from itertools import combinations
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
tree = runpy.run_path(str(HERE / 'verify_pendant_lifts.py'))
branch = tree['branch']
tools = branch['tools']
neighbors = branch['neighbors']


def forces_except(adj, blue, anchor):
    full = (1 << len(adj)) - 1
    while blue != full:
        added = 0
        for v in neighbors(blue & ~(1 << anchor)):
            whites = adj[v] & ~blue
            if whites.bit_count() == 1:
                added |= whites
        if not added:
            return False
        blue |= added
    return True


def leaf_certificate(adj, anchor, time):
    infinity = len(adj) + 1
    times = [time(adj, blue) for blue in range(1 << len(adj))]

    def stable(blue):
        return blue & (1 << anchor) or any(
            blue & (1 << v) and (adj[v] & ~blue).bit_count() == 1
            for v in neighbors(adj[anchor]))

    for blue, initial in enumerate(times):
        if initial == infinity or blue.bit_count() < 3 or not stable(blue):
            continue
        if not forces_except(adj, blue, anchor):
            continue
        single = {1 << v: times[blue ^ (1 << v)] for v in neighbors(blue)}
        if infinity in single.values():
            continue
        stable_single = {loss: t for loss, t in single.items() if stable(blue ^ loss)}
        if not stable_single:
            continue
        slow = max(stable_single, key=stable_single.get)
        peak = stable_single[slow]
        for u, v in combinations((loss for loss, t in stable_single.items() if t < peak), 2):
            if times[blue ^ u ^ v] == infinity and stable(blue ^ u ^ v):
                return dict(blue=blue, killing=u | v, slow=slow,
                            restricted_deadline=max(single[u], single[v]), slow_completion_time=peak)
    return None


def leaf_cuts(children):
    return [(v, x, {v}) for x, group in children.items() for v in group if not children[v]]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    data = (HERE / 'unicyclic-through-11.json').read_bytes()
    census_sha256 = hashlib.sha256(data).hexdigest()
    graphs = json.loads(data)['graphs']
    by_code = {tuple(g['rooted_codes']): i for i, g in enumerate(graphs)}
    time = runpy.run_path(str(branch['BASELINE']))['completion_time']
    known_negative = set()
    for name in ('site-witness', 'two-sites-path', 'branch-witness', 'ring-branch-witness', 'pendant-lift'):
        replay = json.loads((HERE / f'{name}-replay.json').read_bytes())
        assert replay['census_sha256'] == census_sha256
        known_negative.update(c['graph_index'] for c in replay['census_certificates'])

    records = []
    remaining = []
    counts = Counter()
    for index, g in enumerate(graphs):
        if g['every_minimum_support']:
            continue
        adj = tools['adjacency'](g['order'], g['edges'])
        cycle = branch['cycle_vertices'](adj)
        children, off_cycle, sites, leaves, kind = tree['coordinates'](adj, cycle)
        if tree['previously_proved'](index, known_negative, adj, cycle, off_cycle, sites, leaves):
            known_negative.add(index)
            continue
        for first, anchor, removed in leaf_cuts(children) + list(tree['nontrivial_cuts'](children)):
            vertices = [v for v in range(len(adj)) if v not in removed]
            reduced = tree['induced'](adj, vertices)
            core = by_code[tree['canonical_code'](reduced)]
            if core not in known_negative:
                continue
            cert_search = leaf_certificate if len(removed) == 1 else tree['anchored_certificate']
            cert = cert_search(reduced, vertices.index(anchor), time)
            if cert is None:
                continue
            extended = tree['lift'](cert, vertices, removed)
            tools['verify_certificate'](time, adj, extended['blue'], extended['killing'],
                                        extended['slow'], extended['restricted_deadline'],
                                        extended['slow_completion_time'])
            known_negative.add(index)
            counts[kind] += 1
            records.append(dict(graph_index=index, core_graph_index=core, first=first, anchor=anchor,
                                removed=sorted(removed), **extended))
            break
        else:
            remaining.append(dict(graph_index=index, cycle_length=len(cycle), kind=kind))

    report = {'status': 'passed', 'census_sha256': census_sha256,
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'new_counts': dict(counts), 'new_census_certificates': len(records),
              'outstanding_census_members': remaining, 'census_certificates': records}
    with args.output.open('x', encoding='utf-8') as output:
        output.write(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items()
                      if k not in ('census_certificates', 'outstanding_census_members')}, indent=2))
    print('Outstanding in the census:', len(remaining),
          sorted({(r['cycle_length'], r['kind']) for r in remaining}))


if __name__ == '__main__':
    main()
