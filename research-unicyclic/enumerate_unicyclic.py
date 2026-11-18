"""Enumerate connected unicyclic graphs up to isomorphism and check their loss curves."""

import argparse
from collections import Counter, deque
import hashlib
import json
from pathlib import Path
import runpy


PROJECT = Path(__file__).resolve().parent.parent
BASELINE = PROJECT / ('runs/20261118T002947_523991Z-github-publication/source/'
                      'scripts/classification_experiment.py')


def neighbors(mask):
    while mask:
        vertex = mask & -mask
        yield vertex.bit_length() - 1
        mask ^= vertex


def cycle_graph(order):
    return tuple((1 << ((v - 1) % order)) | (1 << ((v + 1) % order))
                 for v in range(order))


def canonical_code(adj):
    degrees = [bits.bit_count() for bits in adj]
    leaves = deque(v for v, degree in enumerate(degrees) if degree == 1)
    while leaves:
        v = leaves.popleft()
        degrees[v] = 0
        for w in neighbors(adj[v]):
            if degrees[w] > 0:
                degrees[w] -= 1
                if degrees[w] == 1:
                    leaves.append(w)
    core = {v for v, degree in enumerate(degrees) if degree == 2}
    assert len(core) >= 3

    def rooted(v, parent):
        children = sorted(rooted(w, v) for w in neighbors(adj[v])
                          if w != parent and w not in core)
        return '(' + ''.join(children) + ')'

    start = min(core)
    ordered = [start]
    previous, current = start, next(w for w in neighbors(adj[start]) if w in core)
    while current != start:
        ordered.append(current)
        previous, current = current, next(w for w in neighbors(adj[current])
                                          if w in core and w != previous)
    assert set(ordered) == core
    labels = tuple(rooted(v, -1) for v in ordered)
    return min(orientation[i:] + orientation[:i]
               for orientation in (labels, labels[::-1]) for i in range(len(labels)))


def graphs(maximum):
    family = {}
    for n in range(3, maximum + 1):
        cycle = cycle_graph(n)
        extended = {canonical_code(cycle): cycle}
        for previous in family.values():
            for v in range(n - 1):
                graph = list(previous) + [1 << v]
                graph[v] |= 1 << (n - 1)
                extended.setdefault(canonical_code(graph), tuple(graph))
        family = extended
        yield n, family


def certificate(adj, witness, completion_time, subsets):
    blue = witness['blue']
    killing = witness['minimum_killing']
    budget = witness['budget']
    size = witness['minimum_killing_size']
    deadline = witness['restricted_time']
    infinity = len(adj) + 1
    assert completion_time(adj, blue) < infinity
    assert completion_time(adj, blue ^ killing) == infinity
    assert all(completion_time(adj, blue ^ loss) < infinity
               for loss in subsets(blue) if loss.bit_count() < size)
    global_loss = max((loss for loss in subsets(blue) if loss.bit_count() <= budget),
                      key=lambda loss: completion_time(adj, blue ^ loss))
    assert completion_time(adj, blue ^ global_loss) == witness['global_time'] > deadline
    restricted = [dict(loss=list(neighbors(loss)), time=completion_time(adj, blue ^ loss))
                  for loss in subsets(killing) if loss.bit_count() <= budget]
    assert max(row['time'] for row in restricted) == deadline
    return dict(blue=list(neighbors(blue)), minimum_killing=list(neighbors(killing)),
                minimum_killing_size=size, budget=budget, deadline=deadline,
                global_loss=list(neighbors(global_loss)), global_time=witness['global_time'],
                restricted_losses=restricted)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-vertices', type=int, default=9, choices=range(3, 12))
    parser.add_argument('--baseline', type=Path, default=BASELINE)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    baseline = runpy.run_path(str(args.baseline))
    check = baseline['every_minimum_support']
    summaries = []
    records = []
    for order, family in graphs(args.max_vertices):
        positive = Counter()
        negative = Counter()
        for code, adj in sorted(family.items()):
            actual, witness, colourings, supports = check(adj)
            length = len(code)
            (positive if actual else negative)[length] += 1
            edges = [[v, w] for v, mask in enumerate(adj) for w in neighbors(mask) if v < w]
            records.append(dict(order=order, cycle_length=length, rooted_codes=code,
                                edges=edges, every_minimum_support=actual,
                                forcing_colourings_checked=colourings,
                                minimum_killing_sets_checked=supports,
                                counterexample=None if actual else certificate(
                                    adj, witness, baseline['completion_time'], baseline['subsets'])))
        summary = dict(order=order, graphs=len(family), positive=sum(positive.values()),
                       positive_by_cycle_length=sorted(positive.items()),
                       negative_by_cycle_length=sorted(negative.items()))
        summaries.append(summary)
        print(json.dumps(summary), flush=True)
    report = dict(status='finite_enumeration_complete', max_vertices=args.max_vertices,
                  enumeration='Every graph is a pure cycle or is obtained by adding a leaf. The cycle decorations are canonical under rotation and reversal.',
                  scope='All initial forcing sets, minimum killing sets and budgets for positives. A replayed explicit witness for negatives.',
                  baseline_sha256=hashlib.sha256(args.baseline.read_bytes()).hexdigest(),
                  experiment_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  summaries=summaries, graphs=records)
    args.output.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')


if __name__ == '__main__':
    main()
