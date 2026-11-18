"""Replay family proofs and audit their agreement with exact small-graph data."""

import argparse
import hashlib
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
experiment = runpy.run_path(str(HERE / 'enumerate_unicyclic.py'))
BASELINE = experiment['BASELINE']
cycle_graph = experiment['cycle_graph']
neighbors = experiment['neighbors']


def add_leaves(adj, center, count):
    added = 0
    for _ in range(count):
        leaf = 1 << len(adj)
        adj[center] |= leaf
        adj.append(1 << center)
        added |= leaf
    return added


def verify_certificate(time, adj, blue, killing, slow, deadline, delayed):
    infinity = len(adj) + 1
    assert time(adj, blue ^ killing) == infinity
    assert all(time(adj, blue ^ (1 << v)) < infinity for v in neighbors(blue))
    assert time(adj, blue) <= deadline
    assert max(time(adj, blue ^ (1 << v)) for v in neighbors(killing)) == deadline
    assert time(adj, blue ^ slow) == delayed > deadline


def attachments_to_long_cycle(time):
    checked = 0
    for n in range(4, 51):
        for size in range(1, 26):
            path = list(cycle_graph(n))
            for i in range(size):
                add_leaves(path, 0 if i == 0 else len(path) - 1, 1)
            half = (n - 2) // 2
            if n >= 5:
                verify_certificate(time, path, 7 | (1 << (n - 1)), 5, 2,
                                   max(size + 1, half), n - 3 + size)
            else:
                blue = 3 | (1 << (n - 1)) | (((1 << size) - 1) << n)
                verify_certificate(time, path, blue, (1 << (n - 1)) | 2, 1, 1, 2)
            checked += 1
            if size >= 2:
                fan = list(cycle_graph(n))
                leaves = add_leaves(fan, 0, size)
                blue = 3 | (1 << (n - 1)) | leaves
                verify_certificate(time, fan, blue, 3 << n, 1, half, half + 1)
                checked += 1
    return checked


def excluded_triangle_attachments(time):
    checked = 0
    adj = list(cycle_graph(3))
    leaves_x = add_leaves(adj, 0, 1)
    leaves_y = add_leaves(adj, 1, 1)
    add_leaves(adj, 2, 1)
    verify_certificate(time, adj, 3 | leaves_x | leaves_y, leaves_x | leaves_y, 1, 2, 3)
    checked += 1
    for a in range(2, 26):
        for b in range(26):
            adj = list(cycle_graph(3))
            add_leaves(adj, 0, 1)
            leaves_y = add_leaves(adj, 1, a)
            leaves_z = add_leaves(adj, 2, b)
            blue = (5 | leaves_y) if b <= 1 else (1 | leaves_y | leaves_z)
            verify_certificate(time, adj, blue, 3 << 4, 1, 2, 3)
            checked += 1
    return checked


def in_candidate(record):
    order = record['order']
    code = record['rooted_codes']
    if len(code) == order:
        return True
    if len(code) != 3 or any(s[1:-1] != '()' * ((len(s) - 2) // 2) for s in code):
        return False
    counts = sorted((len(s) - 2) // 2 for s in code)
    return 1 not in counts or counts in ([0, 0, 1], [0, 1, 1])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, default=HERE / 'unicyclic-through-11.json')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    data_bytes = args.input.read_bytes()
    data = json.loads(data_bytes)
    assert hashlib.sha256(BASELINE.read_bytes()).hexdigest() == data['baseline_sha256']
    for row in data['graphs']:
        assert in_candidate(row) == row['every_minimum_support'], row
    time = runpy.run_path(str(BASELINE))['completion_time']
    report = {
        'status': 'passed',
        'unicyclic_graphs_compared': len(data['graphs']),
        'positive_graphs': sum(row['every_minimum_support'] for row in data['graphs']),
        'long_cycle_exclusion_witnesses': attachments_to_long_cycle(time),
        'excluded_triangle_witnesses': excluded_triangle_attachments(time),
        'input_sha256': hashlib.sha256(data_bytes).hexdigest(),
        'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    args.output.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
