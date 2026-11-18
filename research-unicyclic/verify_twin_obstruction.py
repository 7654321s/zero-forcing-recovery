"""Replay the two-white-vertex obstruction against the unicyclic census."""

import argparse
import hashlib
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
proof_tools = runpy.run_path(str(HERE / 'verify_family_arguments.py'))
neighbors = proof_tools['neighbors']
verify_certificate = proof_tools['verify_certificate']
BASELINE = proof_tools['BASELINE']


def adjacency(order, edges):
    masks = [0] * order
    for a, b in edges:
        masks[a] |= 1 << b
        masks[b] |= 1 << a
    return masks


def paired_leaf_obstruction(masks, leaves_by_parent):
    full = (1 << len(masks)) - 1
    for a, leaves_a in enumerate(leaves_by_parent):
        if len(leaves_a) < 2:
            continue
        for x, neighbors_x in enumerate(masks):
            if x == a or neighbors_x.bit_count() < 2 or neighbors_x & (1 << a):
                continue
            if any(not ((neighbors_x ^ neighbors_z) & ~(1 << x | 1 << z))
                   for z, neighbors_z in enumerate(masks) if z != x):
                continue
            for y in neighbors(neighbors_x):
                if leaves_by_parent[y]:
                    return {'pair_parent': a, 'initial_white': x, 'delayed_leaf_parent': y,
                            'blue': full ^ (1 << x),
                            'killing': (1 << leaves_a[0]) | (1 << leaves_a[1]),
                            'slow': 1 << leaves_by_parent[y][0]}
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, default=HERE / 'unicyclic-through-11.json')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    data = args.input.read_bytes()
    graphs = json.loads(data)['graphs']
    time = runpy.run_path(str(BASELINE))['completion_time']
    rows = []
    leafy_positives = 0
    leafy_negatives = 0
    deep = 0
    for graph_index, graph in enumerate(graphs):
        masks = adjacency(graph['order'], graph['edges'])
        leaves = [[v for v in neighbors(mask) if masks[v].bit_count() == 1] for mask in masks]
        core = [v for v, mask in enumerate(masks) if mask.bit_count() > 1]
        witness = paired_leaf_obstruction(masks, leaves)
        if all(len(leaves[v]) >= 2 for v in core):
            if len(core) == 3:
                assert graph['cycle_length'] == 3 and graph['every_minimum_support']
                leafy_positives += 1
            else:
                assert witness and not graph['every_minimum_support']
                leafy_negatives += 1
        if witness is None:
            continue
        assert not graph['every_minimum_support']
        verify_certificate(time, masks, witness['blue'], witness['killing'], witness['slow'], 1, 2)
        has_deep_attachment = len(core) > graph['cycle_length']
        deep += has_deep_attachment
        rows.append({'graph_index': graph_index, 'deep_attachment': has_deep_attachment, **witness})
    report = {'status': 'passed', 'graphs_examined': len(graphs), 'witnesses_replayed': len(rows),
              'deep_attachment_witnesses': deep, 'leafy_positives': leafy_positives,
              'leafy_negatives': leafy_negatives,
              'input_sha256': hashlib.sha256(data).hexdigest(),
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'witnesses': rows}
    with args.output.open('x', encoding='utf-8') as output:
        output.write(json.dumps(report, indent=2) + '\n')
    print(json.dumps({key: value for key, value in report.items() if key != 'witnesses'}, indent=2))


if __name__ == '__main__':
    main()
