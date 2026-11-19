"""Decide whether a set of base labels is the projection of a finite fort."""

from itertools import combinations, product
from pathlib import Path
import runpy


def neighborhoods(order, edges):
    """Store the offset of a neighbor relative to the source sheet."""
    graph = [[] for _ in range(order)]
    for u, v, shift in edges:
        graph[u].append((v, shift))
        graph[v].append((u, -shift))
    return graph


def largest_shift(graph):
    return max((abs(shift) for row in graph for _, shift in row), default=0)


def endpoint_search(graph, projected, direction):
    """Find endpoints or a label excluded from every feasible subset."""
    conditions = []
    for u, row in enumerate(graph):
        selected = [(v, direction * shift) for v, shift in row if v in projected]
        for v, shift in selected:
            witnesses = [(w, shift - other) for w, other in selected if w != v]
            if u in projected:
                witnesses.append((u, shift))
            if not witnesses:
                return None, v
            conditions.append((v, witnesses))

    limit = 2 * largest_shift(graph) * (len(projected) - 1)
    starts = dict.fromkeys(projected, 0)
    while True:
        changed = False
        for v, witnesses in conditions:
            needed = min(starts[w] + shift for w, shift in witnesses)
            if needed > limit:
                return None, v
            if needed > starts[v]:
                starts[v] = needed
                changed = True
        if not changed:
            return starts, None


def earliest_layers(graph, projected, direction):
    return endpoint_search(graph, projected, direction)[0]


def finite_intervals(graph, projected):
    """Return a finite interval fort with exactly the given projected labels."""
    if not projected:
        return None
    low = earliest_layers(graph, projected, 1)
    high = earliest_layers(graph, projected, -1)
    if low is None or high is None:
        return None
    separation = max(low.values()) + max(high.values()) + 2 * largest_shift(graph)
    return {v: (low[v], separation - high[v]) for v in projected}


def maximal_projection(graph, allowed):
    """Find the greatest support of a finite fort inside the allowed labels."""
    remaining = set(allowed)
    while remaining:
        for direction in (1, -1):
            _, rejected = endpoint_search(graph, remaining, direction)
            if rejected is not None:
                remaining.remove(rejected)
                break
        else:
            return remaining
    return remaining


def check_intervals(graph, projected, intervals):
    if set(intervals) != projected or any(a > b for a, b in intervals.values()):
        raise AssertionError('Incorrect projected support')
    selected = {(v, sheet) for v, (lo, hi) in intervals.items() for sheet in range(lo, hi + 1)}
    boundary_count = {}
    for v, sheet in selected:
        for u, shift in graph[v]:
            neighbor = (u, sheet + shift)
            if neighbor not in selected:
                boundary_count[neighbor] = boundary_count.get(neighbor, 0) + 1
    if 1 in boundary_count.values():
        raise AssertionError('An outside vertex sees just one selected neighbor')
    span = max(hi for _, hi in intervals.values()) - min(lo for lo, _ in intervals.values()) + 1
    limit = 4 * largest_shift(graph) * (len(projected) - 1) + 2 * largest_shift(graph) + 1
    if span > limit:
        raise AssertionError(('unexpected interval span', span, limit))


def brute_first_layers(graph, projected, direction):
    """Independently check the minimum-at-a-neighbor condition on small cases."""
    vertices = sorted(projected)
    limit = 2 * largest_shift(graph) * (len(vertices) - 1)
    for values in product(range(limit + 1), repeat=len(vertices)):
        levels = dict(zip(vertices, values))
        for u, row in enumerate(graph):
            shifted = [levels[v] - direction * shift for v, shift in row if v in levels]
            if shifted:
                lowest = min(shifted)
                if shifted.count(lowest) == 1 and (u not in levels or lowest < levels[u]):
                    break
        else:
            return True
    return False


def check_small_graphs():
    pairs = tuple(combinations(range(4), 2))
    tested = found = one_end = 0
    for assignments in product((None, -1, 0, 1), repeat=len(pairs)):
        graph = neighborhoods(4, ((u, v, shift) for (u, v), shift in zip(pairs, assignments)
                                  if shift is not None))
        greatest = set()
        for size in range(1, 5):
            for vertices in combinations(range(4), size):
                projected = set(vertices)
                intervals = finite_intervals(graph, projected)
                if size <= 2:
                    for direction in (1, -1):
                        actual = earliest_layers(graph, projected, direction) is not None
                        if actual != brute_first_layers(graph, projected, direction):
                            raise AssertionError(('earliest endpoint feasibility', assignments, vertices, direction))
                if intervals is not None:
                    check_intervals(graph, projected, intervals)
                    greatest.update(projected)
                    found += 1
                elif ((earliest_layers(graph, projected, 1) is None)
                      != (earliest_layers(graph, projected, -1) is None)):
                    one_end += 1
                tested += 1
        if maximal_projection(graph, range(4)) != greatest:
            raise AssertionError(('greatest projection', assignments))
    return tested, found, one_end


def check_examples():
    cycle = neighborhoods(4, ((0, 1, 0), (1, 2, 0), (2, 3, 0), (3, 0, 1)))
    if finite_intervals(cycle, {0, 2}) is not None:
        raise AssertionError('The two opposite labels do not lift to a finite fort')
    if maximal_projection(cycle, range(4)):
        raise AssertionError('A consistently shifted cycle has no finite fort')

    checks = runpy.run_path(str(Path(__file__).with_name('check_cyclic_cover_saturation.py')))
    graph, _, _, _ = checks['MODEL']['cubic_two_round_chain_certificate'](26)
    signed = neighborhoods(len(graph), ((u, v, -1 if (u, v) == (0, 1) else 1)
                                        for u, row in enumerate(graph)
                                        for v in checks['members'](row) if u < v))
    projected = {v for v, _ in checks['FOUR_BLOCK_FORT']}
    intervals = finite_intervals(signed, projected)
    if intervals is None:
        raise AssertionError('The known prism fort has a finite projection')
    check_intervals(signed, projected, intervals)
    greatest = maximal_projection(signed, range(len(signed)))
    realization = finite_intervals(signed, greatest)
    if not projected <= greatest or realization is None:
        raise AssertionError('The greatest projection omits a prism fort label')
    check_intervals(signed, greatest, realization)


if __name__ == '__main__':
    check_examples()
    tested, accepted, one_end = check_small_graphs()
    print(f'{tested} weighted four-vertex cases checked, {accepted} interval forts validated')
    print(f'In {one_end} cases only one direction admitted endpoints')
