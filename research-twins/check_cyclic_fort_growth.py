"""Compute fort costs and recovery polynomials with a finite transfer graph."""

from collections import Counter, defaultdict
from functools import lru_cache
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


def recovery_polynomials(graph, seeds, last):
    """Count recoverable loss sets by cardinality for one through last sheets."""
    edges, zero = transfer(graph, seeds)
    states = sorted(set(edges) | {v for row in edges.values() for v, _ in row})
    labels = {state: i for i, state in enumerate(states)}
    centers = [state[len(zero) // 2] for state in states]
    seed_positions = [v for v in range(len(graph)) if seeds & (1 << v)]
    letters = [sum(1 << v for v, lost in zip(seed_positions, flags) if lost)
               for flags in product((False, True), repeat=len(seed_positions))]
    rows = [sum(1 << labels[v] for v, _ in edges.get(state, ())) for state in states]
    rows_for_loss = {
        lost: tuple(row if center & seeds & ~lost == 0 else 0
                    for row, center in zip(rows, centers))
        for lost in letters
    }
    marked_rows = {lost: tuple(row if center else 0 for row, center in zip(step, centers))
                   for lost, step in rows_for_loss.items()}
    identity = tuple(1 << i for i in range(len(states)))
    empty = (0,) * len(states)

    def follow(reachable, step):
        result = 0
        while reachable:
            first = reachable & -reachable
            result |= step[first.bit_length() - 1]
            reachable ^= first
        return result

    @lru_cache(maxsize=None)
    def append(relation, lost):
        total, marked = relation
        step = rows_for_loss[lost]
        marked_step = marked_rows[lost]
        return (tuple(follow(row, step) for row in total),
                tuple(follow(previous, step) | follow(row, marked_step)
                      for previous, row in zip(marked, total)))

    current = {(identity, empty): Counter({0: 1})}
    results = []
    for _ in range(last):
        following = defaultdict(Counter)
        for relation, counts in current.items():
            for lost in letters:
                target = following[append(relation, lost)]
                for degree, count in counts.items():
                    target[degree + lost.bit_count()] += count
        current = following
        recovery = Counter()
        for (_, marked), counts in current.items():
            if not any(row & bit for row, bit in zip(marked, identity)):
                recovery.update(counts)
        results.append(recovery)
    return results


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


def recovery_by_deletion(graph, seeds, sheets, loss_sheets=None):
    adjacent, lifted_seeds = reduce(graph, seeds, sheets)
    intact = sum(lifted_seeds)
    eligible = lifted_seeds
    if loss_sheets is not None:
        eligible = [v for v in lifted_seeds if (v.bit_length() - 1) // len(graph) in loss_sheets]
    return Counter(count for count in range(len(eligible) + 1)
                   for loss in combinations(eligible, count)
                   if forces(adjacent, intact ^ sum(loss)))


def check_guarded_intervals(graph, seeds, cyclic_counts):
    radius = max(1, PROJECTION['largest_shift'](graph))
    # The intact run uses at most one round per base vertex.
    gap = (4 * len(graph) + 2) * radius
    first = recovery_by_deletion(graph, seeds, gap + 1, range(1))
    second = recovery_by_deletion(graph, seeds, gap + 2, range(2))
    joined = recovery_by_deletion(graph, seeds, gap + 3, range(3))
    separated = recovery_by_deletion(graph, seeds, 2 * gap + 3, (0, gap + 1, gap + 2))
    product_counts = Counter()
    for i, left in first.items():
        for j, right in second.items():
            product_counts[i + j] += left * right
    if separated != product_counts or not cyclic_counts <= joined <= product_counts:
        raise AssertionError(('guarded recovery counts', graph, seeds))


def reduced_shifts(graph):
    potentials = {0: 0}
    pending = [0]
    while pending:
        u = pending.pop()
        for v, shift in graph[u]:
            if v not in potentials:
                potentials[v] = potentials[u] + shift
                pending.append(v)
    if len(potentials) != len(graph):
        return None
    adjusted = [(u, v, shift + potentials[u] - potentials[v])
                for u, row in enumerate(graph) for v, shift in row if u < v]
    divisor = gcd(*(shift for _, _, shift in adjusted))
    primitive = neighborhoods(len(graph), ((u, v, shift // (divisor or 1))
                                           for u, v, shift in adjusted))
    return divisor, primitive


def main():
    tested = 0
    by_finite = 0
    by_reduction = 0
    polynomials = 0
    pairs = tuple(combinations(range(3), 2))
    for shifts in product((None, -1, 0, 1), repeat=len(pairs)):
        graph = neighborhoods(3, ((u, v, d) for (u, v), d in zip(pairs, shifts) if d is not None))
        has_finite = bool(PROJECTION['maximal_projection'](graph, range(len(graph))))
        reduction = reduced_shifts(graph)
        for seeds in range(1, 1 << len(graph)):
            adjacent, lifted_seeds = reduce(graph, seeds, 1)
            if not forces(adjacent, sum(lifted_seeds)):
                continue
            edges, zero = transfer(graph, seeds)
            costs = cyclic_costs(edges, zero, 4)
            for sheets, counts in enumerate(recovery_polynomials(graph, seeds, 3), 1):
                if counts != recovery_by_deletion(graph, seeds, sheets):
                    raise AssertionError(('recovery polynomial', shifts, seeds, sheets, counts))
                if sheets == 3:
                    check_guarded_intervals(graph, seeds, counts)
                polynomials += 1
            for sheets, value in enumerate(costs, 1):
                if value != deletion_cost(graph, seeds, sheets):
                    raise AssertionError(('cyclic cost', shifts, seeds, sheets, value))
                tested += 1
                if reduction is not None:
                    divisor, primitive = reduction
                    modulus = sheets // gcd(sheets, divisor)
                    if value != deletion_cost(primitive, seeds, modulus):
                        raise AssertionError(('closed-walk reduction', shifts, seeds, sheets))
                    by_reduction += 1
            finite = finite_cost(edges, zero)
            if has_finite != (finite < float('inf')) or max(costs) > finite:
                raise AssertionError(('finite cost', shifts, seeds, costs, finite))
            by_finite += 1
    for q in (1, 2, 3):
        graph = neighborhoods(4, ((0, 1, 0), (1, 2, 0), (2, 3, 0), (3, 0, q)))
        # Distribute the total shift along the other three edges to keep the window small.
        distributed = neighborhoods(4, ((u, (u + 1) % 4, int(u >= 4 - q)) for u in range(4)))
        edges, zero = transfer(distributed, 0b0011)
        for sheets, counts in enumerate(recovery_polynomials(distributed, 0b0011, 4), 1):
            d = gcd(sheets, q)
            period = sheets // d
            if sum(counts.values()) != (4**period - 3**period)**d:
                raise AssertionError(('shifted cycle recovery probability', sheets, q, counts))
        for sheets, value in enumerate(cyclic_costs(edges, zero, 7), 1):
            expected = sheets // gcd(sheets, q)
            if value != expected or deletion_cost(graph, 0b0011, sheets) != expected:
                raise AssertionError(('shifted cycle', sheets, q))
        if finite_cost(edges, zero) < float('inf'):
            raise AssertionError(('shifted cycle has a finite fort', q))
    print(f'{tested} cyclic transfer costs checked by deletion, {by_finite} finite existence comparisons')
    print('Shifted four-cycle formula verified on 21 cyclic covers')
    print(f'{by_reduction} closed-walk reductions verified by deletion')
    print(f'{polynomials} recovery polynomials verified by exhaustive deletion')
    print(f'{by_finite} guarded-interval factorizations and coefficient bounds checked')


if __name__ == '__main__':
    main()
