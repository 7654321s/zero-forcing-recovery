"""Audit the scope and replay of extending a certificate by an all-blue tree."""

import argparse
from collections import Counter
import hashlib
from itertools import combinations
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
branch = runpy.run_path(str(HERE / 'verify_branch_witnesses.py'))
tools = branch['tools']
bits = branch['bits']
neighbors = branch['neighbors']
canonical_code = branch['family']['experiment']['canonical_code']


def coordinates(adj, cycle):
    _, children = branch['tree_structure'](adj, cycle)
    off_cycle = set(range(len(adj))) - cycle
    sites = [v for v in cycle if children[v]]
    leaves = sum(not children[v] for v in off_cycle)
    if leaves == len(off_cycle):
        kind = 'shallow'
    elif any(len(children[v]) >= 2 for v in off_cycle):
        kind = 'branching_off_cycle'
    else:
        kind = 'deeper_paths'
    return children, len(off_cycle), len(sites), leaves, kind


def previously_proved(index, replay_indices, adj, cycle, off_cycle, sites, leaves):
    return (index in replay_indices or bool(branch['twins'](adj))
            or len(cycle) == 3 and off_cycle == leaves
            or len(cycle) >= 4 and (sites == leaves == 1 or off_cycle == leaves == sites == 2))


def nontrivial_cuts(children):
    parent = {v: p for p, group in children.items() for v in group}
    for first, attachment in sorted(parent.items()):
        if not children[first]:
            continue
        pending = [first]
        removed = set()
        while pending:
            v = pending.pop()
            removed.add(v)
            pending.extend(children[v])
        yield first, attachment, removed


def induced(adj, vertices):
    label = {v: i for i, v in enumerate(vertices)}
    return [bits(label[w] for w in neighbors(adj[v]) if w in label) for v in vertices]


def lift(cert, vertices, removed):
    return {**cert, 'blue': bits(vertices[v] for v in neighbors(cert['blue'])) | bits(removed),
            'killing': bits(vertices[v] for v in neighbors(cert['killing'])),
            'slow': bits(vertices[v] for v in neighbors(cert['slow']))}


def anchored_certificate(adj, anchor, time):
    infinity = len(adj) + 1
    times = [time(adj, blue) for blue in range(1 << len(adj))]

    def stable(blue):
        return blue & (1 << anchor) or any(
            blue & (1 << v) and (adj[v] & ~blue).bit_count() == 1
            for v in neighbors(adj[anchor]))

    for blue, initial in enumerate(times):
        if initial == infinity or blue.bit_count() < 3 or not stable(blue):
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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    data = (HERE / 'unicyclic-through-11.json').read_bytes()
    census_sha256 = hashlib.sha256(data).hexdigest()
    graphs = json.loads(data)['graphs']
    by_code = {tuple(g['rooted_codes']): i for i, g in enumerate(graphs)}
    time = runpy.run_path(str(branch['BASELINE']))['completion_time']
    replay_indices = set()
    for name in ('site-witness', 'two-sites-path', 'branch-witness', 'ring-branch-witness'):
        replay = json.loads((HERE / f'{name}-replay.json').read_bytes())
        assert replay['census_sha256'] == census_sha256
        replay_indices.update(c['graph_index'] for c in replay['census_certificates'])

    known_negative = set()
    records = []
    pending_before = Counter()
    pending_after = Counter()
    assert [g['order'] for g in graphs] == sorted(g['order'] for g in graphs)
    for index, g in enumerate(graphs):
        if g['every_minimum_support']:
            continue
        adj = tools['adjacency'](g['order'], g['edges'])
        cycle = branch['cycle_vertices'](adj)
        children, off_cycle, sites, leaves, kind = coordinates(adj, cycle)
        if previously_proved(index, replay_indices, adj, cycle, off_cycle, sites, leaves):
            known_negative.add(index)
            continue
        pending_before[kind] += 1
        for first, anchor, removed in nontrivial_cuts(children):
            vertices = [v for v in range(len(adj)) if v not in removed]
            reduced = induced(adj, vertices)
            core = by_code[canonical_code(reduced)]
            if core not in known_negative:
                continue
            cert = anchored_certificate(reduced, vertices.index(anchor), time)
            if cert is None:
                continue
            extended = lift(cert, vertices, removed)
            tools['verify_certificate'](time, adj, extended['blue'], extended['killing'],
                                        extended['slow'], extended['restricted_deadline'],
                                        extended['slow_completion_time'])
            known_negative.add(index)
            records.append(dict(graph_index=index, core_graph_index=core, first=first, anchor=anchor,
                                removed=sorted(removed), **extended))
            break
        else:
            pending_after[kind] += 1

    assert sum(pending_before.values()) - sum(pending_after.values()) == len(records)
    report = {'status': 'passed', 'previously_pending': dict(pending_before),
              'still_pending': dict(pending_after), 'new_census_certificates': len(records),
              'census_sha256': census_sha256,
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'census_certificates': records}
    with args.output.open('x', encoding='utf-8') as output:
        output.write(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'census_certificates'}, indent=2))


if __name__ == '__main__':
    main()
