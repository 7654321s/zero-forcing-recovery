"""Replay random lift certificates and sharp cubic fort charging examples."""

import argparse
from collections import Counter, deque
from itertools import pairwise
from pathlib import Path
from random import Random
import runpy


MODEL = runpy.run_path(str(Path(__file__).with_name('check_multiple_loss_bounds.py')))
adjacency = MODEL['adjacency']
mask = MODEL['mask']
members = MODEL['members']


def random_cover(graph, sheets, generator):
    edges = []
    for v, row in enumerate(graph):
        for u in members(row):
            if u > v:
                targets = generator.sample(range(sheets), sheets)
                edges.extend((v * sheets + s, u * sheets + t) for s, t in enumerate(targets))
    return adjacency(len(graph) * sheets, edges)


def sharp_cubic_fort(depth):
    """Subdivide a cubic graph whose root has a full tree through depth stages."""
    edges = []
    leaves = (0,)
    order = 1
    for height in range(depth):
        branch = 3 if height == 0 else 2
        children = tuple(range(order, order + branch * len(leaves)))
        edges.extend((v, u) for i, v in enumerate(leaves)
                     for u in children[i * branch:(i + 1) * branch])
        order += len(children)
        leaves = children
    edges.extend(pairwise((*leaves, leaves[0])))
    if len(edges) % 3:
        raise AssertionError('The subdivision vertices must split into triples')
    lifted = []
    for i, (u, v) in enumerate(edges):
        subdivision = order + i
        auxiliary = order + len(edges) + i // 3
        lifted.extend(((u, subdivision), (v, subdivision), (subdivision, auxiliary)))
    graph = adjacency(order + len(edges) + len(edges) // 3, lifted)
    fort = (1 << order) - 1
    seeds = ((1 << len(graph)) - 1) ^ fort ^ 1
    return graph, seeds, fort


def check_charge(graph, seeds, fort, deadline):
    time, arrival = MODEL['trace'](graph, seeds)
    if time != deadline or not fort:
        raise AssertionError(('intact time or empty fort', time, deadline))
    if any((row & fort).bit_count() == 1 for v, row in enumerate(graph) if not fort & (1 << v)):
        raise AssertionError('Expected a fort')

    uses = Counter()
    for v in members(fort & ~seeds):
        source = MODEL['force_source'](graph, arrival, v)
        if fort & (1 << source):
            parent = source
        else:
            previous = (graph[source] & fort) ^ (1 << v)
            parent = next(members(previous))
        if arrival[parent] >= arrival[v]:
            raise AssertionError(('parent arrival', parent, v))
        uses[parent] += 1
    if any(count > (3 if seeds & (1 << v) else 2) for v, count in uses.items()):
        raise AssertionError(('cubic child count', uses))
    if fort.bit_count() > (3 * 2**deadline - 2) * (fort & seeds).bit_count():
        raise AssertionError('A fort exceeds its charging bound')


def check_cubic_bipartite(graph):
    coloring = {0: 0}
    queue = deque([0])
    while queue:
        v = queue.popleft()
        if graph[v].bit_count() != 3:
            raise AssertionError(('not cubic', v))
        for u in members(graph[v]):
            if u not in coloring:
                coloring[u] = 1 - coloring[v]
                queue.append(u)
            if coloring[u] == coloring[v]:
                raise AssertionError(('not bipartite', u, v))
    if len(coloring) != len(graph):
        raise AssertionError('The graph is disconnected')


def check_sharpness():
    for depth in range(1, 5):
        graph, seeds, fort = sharp_cubic_fort(depth)
        check_cubic_bipartite(graph)
        check_charge(graph, seeds, fort, depth)
        if fort.bit_count() != 3 * 2**depth - 2 or (seeds & fort).bit_count() != 1:
            raise AssertionError(('sharpness', depth))


def check_random_example(certify):
    base, blue, lost, waves = MODEL['bipartite_cubic_chain_certificate'](2)
    sheets = 7
    graph = random_cover(base, sheets, Random(3129))
    check_cubic_bipartite(graph)
    MODEL['check_no_two_edge_cut'](graph)

    def copies(vertices):
        return tuple(v * sheets + s for v in vertices for s in range(sheets))

    for v, row in enumerate(graph):
        if tuple(u // sheets for u in members(row)) != tuple(members(base[v // sheets])):
            raise AssertionError(('neighbor projection', v))
    seeds = mask(copies(members(blue)))
    removed = mask(copies(members(lost)))
    if MODEL['completion_time'](graph, seeds) != 2 or removed.bit_count() != 28 or len(waves) != 14:
        raise AssertionError('Unexpected intact or designated timing')
    MODEL['check_arrival_waves'](graph, seeds ^ removed, [copies(wave) for wave in waves])
    check_charge(graph, seeds, (1 << len(graph)) - 1, 2)
    if certify:
        check_eleven_losses(graph, seeds)
    return len(graph)


def check_eleven_losses(graph, seeds):
    from pysat.card import ITotalizer
    from pysat.solvers import Solver

    seed_vars = [v + 1 for v in members(seeds)]
    clauses = [seed_vars]
    for v, row in enumerate(graph):
        neighbors = tuple(members(row))
        for u in neighbors:
            clauses.append([v + 1, -(u + 1), *(w + 1 for w in neighbors if w != u)])
    _, arrival = MODEL['trace'](graph, seeds)
    available_seeds = [0] * len(graph)
    for v in sorted(range(len(graph)), key=arrival.__getitem__):
        if arrival[v] == 0:
            available_seeds[v] = 1 << v
            continue
        source = MODEL['force_source'](graph, arrival, v)
        earlier = (graph[source] ^ (1 << v)) | (1 << source)
        for u in members(earlier):
            available_seeds[v] |= available_seeds[u]
        # A fort containing v contains one of these earlier vertices.
        clauses.append([-(v + 1), *(u + 1 for u in members(available_seeds[v]))])
    budget = 11
    with ITotalizer(lits=seed_vars, ubound=budget, top_id=len(graph)) as counter:
        with Solver(name='cadical195', bootstrap_with=clauses + counter.cnf.clauses) as solver:
            # Retain learned clauses between successive loss budgets.
            for b in range(3, budget + 1):
                if solver.solve(assumptions=[-counter.rhs[b]]):
                    raise AssertionError(('a loss of at most eleven seeds blocks recovery', b))
    print('Every loss of at most eleven seeds permits recovery in the sample lift', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certify-eleven-losses', action='store_true',
                        help='replay the optional exact SAT exclusion using PySAT')
    args = parser.parse_args()
    check_sharpness()
    print('Cubic charging bound attained at deadlines one through four', flush=True)
    order = check_random_example(args.certify_eleven_losses)
    print(f'{order}-vertex lift preserves two intact and fourteen designated rounds', flush=True)
