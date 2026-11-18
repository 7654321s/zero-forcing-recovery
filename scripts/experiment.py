"""Exact synchronous zero forcing for the published all-long-arm witnesses.

Uses only Python's standard library. None denotes infinite propagation time.
This is a finite reproduction, independent of the Lean proof implementation.
"""
from itertools import combinations
import argparse
import json
from pathlib import Path


def propagation_time(adj, initial):
    blue = set(initial)
    for time in range(len(adj) + 1):
        if len(blue) == len(adj):
            return time
        forces = set()
        for source in blue:
            white = adj[source] - blue
            if len(white) == 1:
                forces.update(white)
        if not forces:
            return None
        blue.update(forces)
    raise RuntimeError('A strict coloring increase cannot exceed the vertex count.')


def losses(allowed, budget):
    ordered = sorted(allowed)
    for size in range(min(budget, len(ordered)) + 1):
        for items in combinations(ordered, size):
            yield set(items)


def worst_time(adj, initial, allowed, budget):
    values = [propagation_time(adj, initial - loss) for loss in losses(allowed, budget)]
    return None if None in values else max(values)


def witness(lengths):
    if len(lengths) < 3 or min(lengths) < 2:
        raise ValueError('Need at least three arms, each of length at least two.')
    adj = [set() for _ in range(1 + sum(lengths))]
    arms = []
    offset = 1
    for length in lengths:
        arm = list(range(offset, offset + length))
        arms.append(arm)
        for u, v in zip([0] + arm, arm):
            adj[u].add(v)
            adj[v].add(u)
        offset += length
    longest = max(range(len(lengths)), key=lengths.__getitem__)
    a, b = [i for i in range(len(lengths)) if i != longest][:2]
    initial = {arm[0] for arm in arms} | {arms[a][1], arms[b][1]}
    support = {arms[a][1], arms[b][1]}
    if propagation_time(adj, initial) is None:
        raise RuntimeError('Initial set failed to force.')
    if propagation_time(adj, initial - support) is not None:
        raise RuntimeError('Support failed to kill.')
    if any(propagation_time(adj, initial - loss) is None for loss in losses(initial, 1)):
        raise RuntimeError('Found a killing set smaller than the proposed support.')
    global_profile = [worst_time(adj, initial, initial, k) for k in range(3)]
    support_profile = [worst_time(adj, initial, support, k) for k in range(3)]
    maximum = max(lengths)
    if global_profile[1] != maximum + 1 or support_profile[1] != maximum:
        raise RuntimeError('Unexpected propagation-time separation.')
    return dict(arm_lengths=lengths, vertices=len(adj), initial=sorted(initial),
                minimum_killing_support=sorted(support), killing_number=2,
                budgets=[0, 1, 2], global_worst_times=global_profile,
                support_worst_times=support_profile,
                null_means='infinite propagation time',
                enumeration_scope='all losses of size at most two in this initial set')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    results = {'status': 'finite_witness_reproduction_passed',
               'general_proof': 'formalization-path-star-all-long.lean',
               'examples': [witness(ls) for ls in [[2, 2, 2], [2, 3, 5], [4, 2, 6, 3]]]}
    rendered = json.dumps(results, indent=2) + '\n'
    if args.output:
        args.output.write_text(rendered, encoding='utf-8')
    print(rendered, end='')


if __name__ == '__main__':
    main()
