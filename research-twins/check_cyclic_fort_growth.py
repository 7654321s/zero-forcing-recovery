"""Compute cyclic and finite fort costs with a finite transfer graph."""

from heapq import heappop, heappush
from itertools import combinations, product
from math import gcd
from pathlib import Path
import runpy


PROJECTION = runpy.run_path(str(Path(__file__).with_name('check_finite_fort_projection.py')))
neighborhoods = PROJECTION['neighborhoods']


def transfer(graph, seeds):
    radius = max(1, PROJECTION['largest_shift'](graph))
    patterns = range(1 << len(graph))
    edges = {}
    for window in product(patterns, repeat=2 * radius + 1):
        center = window[radius]
        if any(not (center & (1 << u))
               and sum(bool(window[radius + shift] & (1 << v)) for v, shift in row) == 1
               for u, row in enumerate(graph)):
            continue
        weight = (center & seeds).bit_count()
        edges.setdefault(window[:-1], []).append((window[1:], weight))
    return edges, (0,) * (2 * radius)


def cyclic_costs(edges, zero, last):
    best = [float('inf')] * last
    for start in edges.keys() - {zero}:
        current = {start: 0}
        for i in range(last):
            next_cost = {}
            for u, cost in current.items():
                for v, weight in edges.get(u, ()):
                    total = cost + weight
                    if total < next_cost.get(v, float('inf')):
                        next_cost[v] = total
            current = next_cost
            if start in current:
                best[i] = min(best[i], current[start])
    return best


def distances(edges, start):
    pending = [(0, start)]
    best = {start: 0}
    while pending:
        cost, u = heappop(pending)
        if cost != best[u]:
            continue
        for v, weight in edges.get(u, ()):
            total = cost + weight
            if total < best.get(v, float('inf')):
                best[v] = total
                heappush(pending, (total, v))
    return best


def finite_cost(edges, zero):
    reverse = {}
    for u, row in edges.items():
        for v, weight in row:
            reverse.setdefault(v, []).append((u, weight))
    forward = distances(edges, zero)
    backward = distances(reverse, zero)
    return min((forward[u] + backward[u] for u in (forward.keys() & backward.keys()) - {zero}),
               default=float('inf'))


def forces(graph, seeds):
    blue = seeds
    while True:
        additions = 0
        for v, neighbors in enumerate(graph):
            if blue & (1 << v):
                white_neighbors = neighbors & ~blue
                if white_neighbors.bit_count() == 1:
                    additions |= white_neighbors
        if not additions:
            return blue.bit_count() == len(graph)
        blue |= additions


def reduce(graph, seeds, sheets):
    adjacent = []
    lifted_seeds = []
    for sheet in range(sheets):
        for u, row in enumerate(graph):
            adjacent.append(sum(1 << (((sheet + shift) % sheets) * len(graph) + v)
                                for v, shift in row))
            if seeds & (1 << u):
                lifted_seeds.append(1 << (sheet * len(graph) + u))
    return adjacent, lifted_seeds


def deletion_cost(graph, seeds, sheets):
    adjacent, lifted_seeds = reduce(graph, seeds, sheets)
    intact = sum(lifted_seeds)
    for count in range(len(lifted_seeds) + 1):
        for losses in combinations(lifted_seeds, count):
            if not forces(adjacent, intact ^ sum(losses)):
                return count
    raise AssertionError('Deleting all seeds did not block recovery')


def main():
    tested = 0
    by_finite = 0
    pairs = tuple(combinations(range(3), 2))
    for shifts in product((None, -1, 0, 1), repeat=len(pairs)):
        graph = neighborhoods(3, ((u, v, d) for (u, v), d in zip(pairs, shifts) if d is not None))
        has_finite = bool(PROJECTION['maximal_projection'](graph, range(len(graph))))
        for seeds in range(1, 1 << len(graph)):
            adjacent, lifted_seeds = reduce(graph, seeds, 1)
            if not forces(adjacent, sum(lifted_seeds)):
                continue
            edges, zero = transfer(graph, seeds)
            costs = cyclic_costs(edges, zero, 4)
            for sheets, value in enumerate(costs, 1):
                if value != deletion_cost(graph, seeds, sheets):
                    raise AssertionError(('cyclic cost', shifts, seeds, sheets, value))
                tested += 1
            finite = finite_cost(edges, zero)
            if has_finite != (finite < float('inf')) or max(costs) > finite:
                raise AssertionError(('finite cost', shifts, seeds, costs, finite))
            by_finite += 1
    for q in (1, 2, 3):
        graph = neighborhoods(4, ((0, 1, 0), (1, 2, 0), (2, 3, 0), (3, 0, q)))
        # Distribute the total shift along the other three edges to keep the window small.
        distributed = neighborhoods(4, ((u, (u + 1) % 4, int(u >= 4 - q)) for u in range(4)))
        edges, zero = transfer(distributed, 0b0011)
        for sheets, value in enumerate(cyclic_costs(edges, zero, 7), 1):
            expected = sheets // gcd(sheets, q)
            if value != expected or deletion_cost(graph, 0b0011, sheets) != expected:
                raise AssertionError(('shifted cycle', sheets, q))
        if finite_cost(edges, zero) < float('inf'):
            raise AssertionError(('shifted cycle has a finite fort', q))
    print(f'{tested} cyclic transfer costs checked by deletion, {by_finite} finite existence comparisons')
    print('Shifted four-cycle formula verified on 21 cyclic covers')


if __name__ == '__main__':
    main()
