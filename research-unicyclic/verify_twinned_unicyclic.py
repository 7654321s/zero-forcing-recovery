"""Produce one-loss certificates for the complete twinned unicyclic class."""

import argparse
from collections import Counter, deque
import hashlib
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
helpers = runpy.run_path(str(HERE / 'verify_twin_obstruction.py'))
adjacency = helpers['adjacency']
neighbors = helpers['neighbors']
verify_certificate = helpers['verify_certificate']
BASELINE = helpers['BASELINE']


def twins(adj):
    return [(u, v) for u in range(len(adj)) for v in range(u + 1, len(adj))
            if not ((adj[u] ^ adj[v]) & ~((1 << u) | (1 << v)))]


def cycle_vertices(adj):
    degree = [row.bit_count() for row in adj]
    leaves = deque(i for i, d in enumerate(degree) if d == 1)
    while leaves:
        v = leaves.popleft()
        degree[v] = 0
        for w in neighbors(adj[v]):
            if degree[w] > 0:
                degree[w] -= 1
                if degree[w] == 1:
                    leaves.append(w)
    return {v for v, d in enumerate(degree) if d == 2}


def exact_one_round(adj, whites):
    covered = 0
    for v, mask in enumerate(adj):
        if whites & (1 << v):
            continue
        white_neighbors = mask & whites
        if white_neighbors.bit_count() == 1:
            covered |= white_neighbors
    return covered == whites


def two_white_witness(adj, pairs):
    order = len(adj)
    full = (1 << order) - 1
    twin_vertices = {v for pair in pairs for v in pair}
    for x in range(order):
        if x in twin_vertices:
            continue
        wx = 1 << x
        slow = next((z for z in range(order) if z != x
                     and not exact_one_round(adj, wx | (1 << z))), None)
        if slow is None:
            continue
        for u, v in pairs:
            if exact_one_round(adj, wx | (1 << u)) and exact_one_round(adj, wx | (1 << v)):
                return {'case': 'two_white_vertices', 'blue': full ^ wx,
                        'killing': (1 << u) | (1 << v), 'slow': 1 << slow,
                        'restricted_deadline': 1, 'slow_completion_time': 2}
    return None


def single_site_witness(adj, pairs, cycle):
    sites = [v for v in cycle if any(w not in cycle for w in neighbors(adj[v]))]
    siblings = [(u, v) for u, v in pairs if adj[u].bit_count() == 1 and adj[u] == adj[v]]
    if len(cycle) < 4 or len(sites) != 1 or not siblings:
        return None
    root = sites[0]
    blue = sum(1 << v for v in range(len(adj)) if v not in cycle)
    blue |= (1 << root) | sum(1 << v for v in neighbors(adj[root]) if v in cycle)
    u, v = siblings[0]
    deadline = (len(cycle) - 2) // 2
    return {'case': 'one_site_delayed_cycle_start', 'blue': blue,
            'killing': (1 << u) | (1 << v), 'slow': 1 << root,
            'restricted_deadline': deadline, 'slow_completion_time': deadline + 1}


def predicted_positive_with_twins(adj, cycle):
    if len(adj) == len(cycle):
        return True
    if len(cycle) != 3 or any(mask.bit_count() > 1 for v, mask in enumerate(adj) if v not in cycle):
        return False
    counts = sorted(sum(w not in cycle for w in neighbors(adj[v])) for v in cycle)
    return 1 not in counts or counts == [0, 0, 1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, default=HERE / 'unicyclic-through-11.json')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    data = args.input.read_bytes()
    graphs = json.loads(data)['graphs']
    time = runpy.run_path(str(BASELINE))['completion_time']
    statistics = Counter()
    witnesses = []
    for index, graph in enumerate(graphs):
        adj = adjacency(graph['order'], graph['edges'])
        pairs = twins(adj)
        if not pairs:
            statistics['twin_free_positive' if graph['every_minimum_support'] else 'twin_free_negative'] += 1
            continue
        cycle = cycle_vertices(adj)
        assert len(cycle) == graph['cycle_length']
        assert predicted_positive_with_twins(adj, cycle) == graph['every_minimum_support'], index
        if graph['every_minimum_support']:
            statistics['twinned_positive'] += 1
            continue
        witness = two_white_witness(adj, pairs) or single_site_witness(adj, pairs, cycle)
        assert witness is not None, (index, graph)
        verify_certificate(time, adj, witness['blue'], witness['killing'], witness['slow'],
                           witness['restricted_deadline'], witness['slow_completion_time'])
        statistics[witness['case']] += 1
        witnesses.append({'graph_index': index, **witness})
    report = {'status': 'passed', 'graphs': len(graphs), 'statistics': dict(statistics),
              'certificates': len(witnesses), 'input_sha256': hashlib.sha256(data).hexdigest(),
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'witnesses': witnesses}
    with args.output.open('x', encoding='utf-8') as file:
        file.write(json.dumps(report, indent=2) + '\n')
    print(json.dumps({key: value for key, value in report.items() if key != 'witnesses'}, indent=2))


if __name__ == '__main__':
    main()
