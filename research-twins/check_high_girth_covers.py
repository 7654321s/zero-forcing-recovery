"""Replay a mod-2 homology lift and check the girth-based fort bound."""

from collections import deque
from itertools import combinations
from pathlib import Path
import runpy


MODEL = runpy.run_path(str(Path(__file__).with_name('check_multiple_loss_bounds.py')))
adjacency = MODEL['adjacency']
mask = MODEL['mask']
members = MODEL['members']


def homology_cover(graph):
    """Give the chords of a spanning tree independent binary coordinates."""
    tree = set()
    seen = {0}
    frontier = deque([0])
    while frontier:
        u = frontier.popleft()
        for v in members(graph[u]):
            if v not in seen:
                seen.add(v)
                frontier.append(v)
                tree.add(tuple(sorted((u, v))))
    if len(seen) != len(graph):
        raise ValueError('The base graph must be connected')

    voltages = {}
    sheets = 1
    for u, row in enumerate(graph):
        for v in members(row):
            if v <= u:
                continue
            edge = (u, v)
            voltages[edge] = 0
            if edge not in tree:
                voltages[edge] = sheets
                sheets *= 2
    edges = ((u * sheets + s, v * sheets + (s ^ shift))
             for (u, v), shift in voltages.items() for s in range(sheets))
    return adjacency(len(graph) * sheets, edges), sheets


def check_girth(graph, expected):
    """Search all BFS balls deep enough to detect every cycle up to expected."""
    neighbors = [tuple(members(row)) for row in graph]
    shortest = expected + 1
    for root in range(len(graph)):
        depth = {root: 0}
        parent = {root: None}
        frontier = deque([root])
        while frontier:
            u = frontier.popleft()
            for v in neighbors[u]:
                if v not in depth:
                    if depth[u] < expected // 2:
                        parent[v] = u
                        depth[v] = depth[u] + 1
                        frontier.append(v)
                elif v != parent[u] and parent[v] != u:
                    shortest = min(shortest, depth[u] + depth[v] + 1)
    if shortest != expected:
        raise AssertionError(('girth', shortest, expected))


def fort_size_lower_bound(min_degree, girth):
    branch = min_degree - 1
    vertex_depth = (girth - 1) // 4
    pair_depth = (girth - 3) // 4
    return max(1 + min_degree * sum(branch**i for i in range(vertex_depth)),
               2 * sum(branch**i for i in range(pair_depth + 1)))


def check_small_graphs():
    k4 = adjacency(4, combinations(range(4), 2))
    graph, sheets = homology_cover(k4)
    if sheets != 8:
        raise AssertionError(('K4 sheet count', sheets))
    check_girth(graph, 6)
    MODEL['check_connected'](graph, 3)
    MODEL['check_no_two_edge_cut'](graph)

    # The point-line incidence graph of the Fano plane has girth six.
    heawood = adjacency(14, ((p, 7 + (p + d) % 7) for p in range(7) for d in (0, 1, 3)))
    check_girth(heawood, 6)
    for base, g, expected in ((k4, 3, 2), (heawood, 6, 4)):
        size = next(count for count in range(1, len(base) + 1)
                    if any(all((row & fort).bit_count() != 1
                               for v, row in enumerate(base) if not fort & (1 << v))
                           for fort in map(mask, combinations(range(len(base)), count))))
        if size != expected or size != fort_size_lower_bound(3, g):
            raise AssertionError(('fort size', g, expected, size))


def check_delayed_cover():
    base, blue, lost, waves = MODEL['cubic_two_round_chain_certificate'](1)
    MODEL['check_no_two_edge_cut'](base)
    check_girth(base, 3)
    graph, sheets = homology_cover(base)

    def copies(vertices):
        return tuple(v * sheets + sheet for v in vertices for sheet in range(sheets))

    MODEL['check_connected'](graph, 3)
    check_girth(graph, 6)
    if sheets != 512 or len(graph) != 8192 or any(row.bit_count() != 3 for row in graph):
        raise AssertionError(('cubic cover size', sheets, len(graph)))
    for u, row in enumerate(graph):
        projected = tuple(v // sheets for v in members(row))
        if projected != tuple(members(base[u // sheets])):
            raise AssertionError(('local neighbor bijection', u))
    seeds = mask(copies(members(blue)))
    removed = mask(copies(members(lost)))
    if MODEL['completion_time'](graph, seeds) != 2 or removed.bit_count() != 512 or len(waves) != 8:
        raise AssertionError('Unexpected intact time or designated loss')
    MODEL['check_arrival_waves'](graph, seeds ^ removed, [copies(wave) for wave in waves])


if __name__ == '__main__':
    check_small_graphs()
    print('Girth and fort bounds checked on small graphs', flush=True)
    check_delayed_cover()
    print('8192-vertex homology cover: girth six, intact time two, exact delay eight', flush=True)
