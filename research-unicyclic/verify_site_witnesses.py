"""Replay graph-size-independent one-loss witnesses for attached cycles."""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
helpers = runpy.run_path(str(HERE / 'verify_twinned_unicyclic.py'))
family = runpy.run_path(str(HERE / 'verify_family_arguments.py'))
adjacency = helpers['adjacency']
cycle_vertices = helpers['cycle_vertices']
neighbors = helpers['neighbors']
verify_certificate = helpers['verify_certificate']
BASELINE = helpers['BASELINE']


def bits(vertices):
    return sum(1 << v for v in vertices)


def cycle_order(adj, cycle, root):
    ring = [root]
    old, v = root, next(w for w in neighbors(adj[root]) if w in cycle)
    while v != root:
        ring.append(v)
        old, v = v, next(w for w in neighbors(adj[v]) if w in cycle and w != old)
    assert set(ring) == cycle
    return ring


def independent_sites_witness(adj, cycle, sites):
    ring_mask = bits(cycle)
    site_mask = bits(sites)
    if any(adj[v] & site_mask for v in sites):
        return None
    for root in sorted(sites):
        pair = adj[root] & ring_mask
        others = site_mask ^ (1 << root)
        if any(adj[v] & others for v in neighbors(pair)):
            continue
        blue_ring = site_mask | pair
        whites = len(cycle) - blue_ring.bit_count()
        if whites % 2 == 0:
            spare = next((v for v in sorted(cycle)
                          if not (blue_ring & (1 << v)) and not (blue_ring & adj[v])), None)
            if spare is None:
                continue
            blue_ring |= 1 << spare
            whites -= 1
        assert whites >= 1
        full = (1 << len(adj)) - 1
        return 'delayed_start', (full ^ ring_mask) | blue_ring, pair, 1 << root, (whites + 1)//2, (whites + 3)//2
    return None


def five_cycle_one_site_witness(adj, cycle, root):
    ring = cycle_order(adj, cycle, root)
    outside = sorted(set(range(len(adj))) - cycle)
    all_outside = bits(outside)
    blue_ring = bits(ring[:4])
    first = {}
    for leaf in outside:
        if adj[leaf].bit_count() != 1:
            continue
        parent = next(neighbors(adj[leaf]))
        if parent in first:
            return ('five_siblings', all_outside | bits((ring[0], ring[1], ring[4])),
                    bits((first[parent], leaf)), 1 << root, 1, 2)
        first[parent] = leaf
    killing = bits((ring[1], ring[3]))
    if root in first:
        return 'five_direct_leaf', all_outside | blue_ring, killing, 1 << first[root], 1, 2
    parent, leaf = next(iter(first.items()))
    blue = (all_outside ^ (1 << leaf)) | blue_ring
    slow_time = 3 if adj[parent].bit_count() == 2 and (adj[parent] & (1 << root)) else 2
    return 'five_deep_leaf', blue, killing, 1 << parent, 1, slow_time


def witness_on_one_site(adj, cycle, root):
    if len(cycle) == 5:
        return five_cycle_one_site_witness(adj, cycle, root)
    witness = independent_sites_witness(adj, cycle, {root})
    assert witness is not None
    return witness


def rooted_code(edges, vertex=0, parent=None):
    return '(' + ''.join(sorted(rooted_code(edges, w, vertex) for w in neighbors(edges[vertex])
                                if w != parent)) + ')'


def rooted_trees(max_added):
    trees = {'()': (0,)}
    for _ in range(max_added):
        extended = {}
        for tree in trees.values():
            for at in range(len(tree)):
                adj = list(tree)
                adj[at] |= 1 << len(adj)
                adj.append(1 << at)
                extended.setdefault(rooted_code(adj), tuple(adj))
        trees = extended
        yield from trees.values()


def attach_tree(n, tree):
    adj = list(family['cycle_graph'](n)) + [0] * (len(tree) - 1)
    labels = [0] + list(range(n, len(adj)))
    for i, mask in enumerate(tree):
        adj[labels[i]] |= bits(labels[j] for j in neighbors(mask))
    return adj


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    data = (HERE / 'unicyclic-through-11.json').read_bytes()
    census = json.loads(data)['graphs']
    time = runpy.run_path(str(BASELINE))['completion_time']
    records = []
    counts = Counter()

    def check(adj, certificate):
        case, blue, killing, slow, deadline, delayed = certificate
        assert killing.bit_count() == 2 and slow.bit_count() == 1
        verify_certificate(time, adj, blue, killing, slow, deadline, delayed)
        return dict(case=case, blue=blue, killing=killing, slow=slow,
                    restricted_deadline=deadline, slow_completion_time=delayed)

    for index, graph in enumerate(census):
        adj = adjacency(graph['order'], graph['edges'])
        cycle = cycle_vertices(adj)
        outside = set(range(len(adj))) - cycle
        if len(cycle) < 4 or not outside:
            continue
        sites = {v for v in cycle if any(w in outside for w in neighbors(adj[v]))}
        if len(sites) == 1:
            cert = witness_on_one_site(adj, cycle, next(iter(sites)))
            counts['census_one_site'] += 1
        else:
            cert = independent_sites_witness(adj, cycle, sites)
            if cert is None:
                continue
            counts['census_multiple_sites'] += 1
        assert not graph['every_minimum_support'], index
        records.append({'graph_index': index, **check(adj, cert)})

    for tree in rooted_trees(8):
        for n in range(4, 31):
            adj = attach_tree(n, tree)
            check(adj, witness_on_one_site(adj, set(range(n)), 0))
            counts['rooted_tree_grid'] += 1

    for n in range(4, 17):
        bare = family['cycle_graph'](n)
        cycle = set(range(n))
        for mask in range(1, 1 << n):
            if mask.bit_count() < 2:
                continue
            sites = set(neighbors(mask))
            if any(bare[v] & mask for v in sites):
                continue
            adj = list(bare)
            for v in sorted(sites):
                parent = v
                for _ in range(1 + v % 3):
                    family['add_leaves'](adj, parent, 1)
                    parent = len(adj) - 1
            cert = independent_sites_witness(adj, cycle, sites)
            if cert is not None:
                check(adj, cert)
                counts['separated_site_grid'] += 1

    report = {'status': 'passed', 'counts': dict(counts),
              'rooted_tree_grid': 'All nonempty rooted attachments through eight added vertices and ring lengths 4..30.',
              'separated_site_grid': 'All eligible independent site sets on rings 4..16 with paths of lengths 1..3.',
              'census_sha256': hashlib.sha256(data).hexdigest(),
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'census_certificates': records}
    with args.output.open('x', encoding='utf-8') as output:
        output.write(json.dumps(report, indent=2) + '\n')
    print(json.dumps({key: value for key, value in report.items() if key != 'census_certificates'},
                     indent=2))


if __name__ == '__main__':
    main()
