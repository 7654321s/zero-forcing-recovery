"""Replay extremal recovery examples for several lost initial blue vertices."""

from collections import Counter, defaultdict, namedtuple
from fractions import Fraction
from functools import lru_cache
from heapq import heappop, heappush
from itertools import chain, combinations, groupby, pairwise
from pathlib import Path
from random import Random
import runpy


HERE = Path(__file__).resolve().parent
SINGLE = runpy.run_path(str(HERE / 'check_single_loss_bounds.py'))
adjacency = SINGLE['adjacency']
completion_time = SINGLE['completion_time']
mask = SINGLE['mask']
members = SINGLE['members']
trace = SINGLE['trace']


def path_certificate(rounds, losses):
    pairs = [2 * rounds + 1 + i * (2 * rounds + 2) for i in range(losses)]
    order = pairs[-1] + rounds + 2
    blue = mask([0, *pairs, *(v + 1 for v in pairs)])
    return adjacency(order, pairwise(range(order))), blue, mask(pairs), mask([0, *pairs])


def cycle_certificate(rounds, losses):
    order = (losses + 1) * (2 * rounds + 2)
    pairs = range(0, order, 2 * rounds + 2)
    blue = mask([*pairs, *(v + 1 for v in pairs)])
    return adjacency(order, pairwise([*range(order), 0])), blue, mask(pairs[1:]), mask(pairs)


def force_source(graph, arrivals, vertex):
    round_number = arrivals[vertex]
    return next(source for source in members(graph[vertex])
                if arrivals[source] < round_number
                and all(arrivals[w] < round_number
                        for w in members(graph[source] & ~(1 << vertex))))


def one_round_cycle_rank_time(losses, cycle_rank):
    extra = min(losses, cycle_rank // 2)
    if losses >= 2:
        extra = max(extra, (cycle_rank - 3) // 2)
    return 1 + 3 * losses + extra


def check_cycle_rank_trace(graph, blue, lost, cycle_rank):
    intact, full = trace(graph, blue)
    delayed, late = trace(graph, blue ^ lost)
    if delayed > len(graph) or delayed <= intact:
        raise AssertionError(('expected a finite, positive delay', intact, delayed))

    roots = set(members(lost))
    representative = {v: v for v in roots}
    forest_edges = set()
    discrepant = sorted((v for v in range(len(graph)) if 0 < full[v] < late[v]),
                        key=full.__getitem__)
    for vertex in discrepant:
        source = force_source(graph, full, vertex)
        if full[source] < late[source]:
            parent = source
        else:
            blockers = (w for w in members(graph[source] & ~(1 << vertex))
                        if late[w] >= full[vertex])
            parent = max(blockers, key=late.__getitem__) if intact == 1 else next(blockers)
            if source in representative:
                raise AssertionError(('repeated intermediate vertex', source))
            representative[source] = representative[parent]
            forest_edges.add(frozenset((parent, source)))
        representative[vertex] = representative[parent]
        forest_edges.add(frozenset((source, vertex)))

    vertex = late.index(delayed)
    trail = [(vertex, True)]
    for round_number in range(delayed, intact + 1, -1):
        source = force_source(graph, late, vertex)
        if late[source] == round_number - 1:
            vertex = source
        else:
            trail.append((source, False))
            vertex = next(w for w in members(graph[source]) if late[w] == round_number - 1)
        trail.append((vertex, True))
    distinguished = [v for v, selected in trail if selected]
    if [late[v] for v in distinguished] != list(range(delayed, intact, -1)):
        raise AssertionError(('incorrect sequence of arrival rounds', distinguished))

    visits, visit_sizes, root_visits, edges = [], [], set(), set()
    previous = None
    for vertex, selected in trail:
        if previous is None:
            visits.append(representative[vertex])
            visit_sizes.append(0)
        else:
            edge = frozenset((previous, vertex))
            if edge in edges:
                raise AssertionError(('repeated trail edge', previous, vertex))
            edges.add(edge)
            if edge not in forest_edges:
                visits.append(representative.get(vertex, vertex))
                visit_sizes.append(0)
        if selected:
            if vertex not in representative:
                raise AssertionError(('uncovered discrepancy', vertex))
            visit_sizes[-1] += 1
            if vertex in roots:
                root_visits.add(len(visits) - 1)
        previous = vertex

    surcharge = max(0, 2 * intact - 1)
    for index, size in enumerate(visit_sizes):
        limit = 2 * intact + 1 if index in root_visits else surcharge
        if size > limit:
            raise AssertionError(('too many arrivals in one visit', index, size, limit))
    revisits = len(visits) - len(set(visits))
    upper = intact + (2 * intact + 1) * len(roots) + surcharge * revisits
    if intact == 1:
        upper = min(upper, one_round_cycle_rank_time(len(roots), cycle_rank))
        groups = []
        previous_arrival = -2
        for arrival in sorted(late[z] for z in roots):
            if arrival > previous_arrival + 1:
                groups.append([])
            groups[-1].append(arrival)
            previous_arrival = arrival
        group_cost = sum(one_round_group_rank(group) for group in groups)
        excess = delayed - 1 - 3 * len(roots)
        if cycle_rank < 2 * excess + group_cost:
            raise AssertionError(('rank cost of restoration groups', cycle_rank, excess, groups))
    if intact == 2:
        if len(roots) == 1 and cycle_rank:
            upper = min(upper, (cycle_rank + 19) // 2)
        elif len(roots) >= 2:
            upper = min(upper, 2 + (3 * cycle_rank + 13 * len(roots)) // 2)
        if all(row.bit_count() <= 3 for row in graph):
            linear_bound = 2 + 5 * len(roots) + cycle_rank
            excess_rank = max(0, cycle_rank - len(roots))
            upper = min(upper, linear_bound - min(2, excess_rank))
            full_roots = (len(root_visits) == len(roots)
                          and all(visit_sizes[index] == 5 for index in root_visits))
            if full_roots:
                singletons = delayed - 2 - 5 * len(roots)
                if cycle_rank < singletons + max(0, singletons - len(roots)):
                    raise AssertionError(('subcubic full-root visit rank', cycle_rank, singletons))
            if delayed == linear_bound:
                if not full_roots or any(
                    size != 1
                    for index, (component, size) in enumerate(zip(visits, visit_sizes))
                    if component in roots and index not in root_visits
                ):
                    raise AssertionError(('subcubic equality trail', visits, visit_sizes, root_visits))
            if len(roots) == 1:
                upper = min(upper, 8 if cycle_rank <= 3 else 9)
    if intact >= 3:
        upper = min(upper, intact + (2 * intact + 3) * len(roots) + (2 * intact - 3) * cycle_rank)
        if all(row.bit_count() <= 3 for row in graph):
            coefficient = 2 * intact - 3
            linear_bound = intact + (2 * intact + 1) * len(roots) + coefficient * cycle_rank
            excess_rank = max(0, cycle_rank - len(roots))
            penalty = min(2 if intact == 3 else intact, 2 * excess_rank)
            if intact >= 4 and cycle_rank > 3 * len(roots):
                depth_two_penalty = 2 * excess_rank + 2 * (cycle_rank - 3 * len(roots))
                beyond_depth_two = max(0, cycle_rank - 6 * len(roots))
                depth_three_penalty = 2 * beyond_depth_two - min(len(roots), beyond_depth_two)
                penalty = min(intact, depth_two_penalty + depth_three_penalty)
            upper = min(upper, linear_bound - penalty)
            if delayed == linear_bound:
                root_size = 2 * intact + 1
                if len(root_visits) != len(roots) or any(
                    size != (root_size if index in root_visits else coefficient)
                    for index, (component, size) in enumerate(zip(visits, visit_sizes))
                    if component in roots
                ):
                    raise AssertionError(('subcubic long equality trail', visit_sizes, root_visits))
    if revisits > cycle_rank or delayed > upper:
        raise AssertionError(('cycle rank bound', intact, delayed, cycle_rank, revisits))
    return intact, delayed, revisits


def one_round_group_rank(arrivals):
    size = len(arrivals)
    tied_returns = size - len(set(arrivals))
    return 3 * (size - 1) + 2 * tied_returns


def check_branched_forest_extremizers():
    for intact, losses in ((0, 3), (1, 3), (2, 4), (4, 2), (7, 6)):
        path, blue, lost, _ = path_certificate(intact, losses)
        order = len(path)
        if intact == 0:
            lost = mask(range(order - losses, order))
        leaves = range(order, order + 12)
        graph = adjacency(leaves.stop, [*pairwise(range(order)), *((0, v) for v in leaves)])
        expected = (intact, intact + (2 * intact + 1) * losses, 0)
        result = check_cycle_rank_trace(graph, blue | mask(leaves), lost, 0)
        if result != expected:
            raise AssertionError(('branched forest extremizer', losses, result, expected))
        print('Branched tree attaining the forest bound:', intact, losses, len(graph), result[1])


def check_small_cycles():
    checked = 0
    for order in range(3, 12):
        graph = adjacency(order, pairwise([*range(order), 0]))
        times = [completion_time(graph, blue) for blue in range(1 << order)]
        for blue, intact in enumerate(times):
            if intact > order:
                continue
            seeds = tuple(members(blue))
            for size in range(1, min(3, len(seeds)) + 1):
                cap = intact * (size + 1) + (size + 1) // 2
                for deleted in combinations(seeds, size):
                    delayed = times[blue ^ mask(deleted)]
                    if delayed <= order:
                        if delayed > cap:
                            raise AssertionError(('cycle upper bound', order, blue, deleted))
                        checked += 1
    return checked


def check_small_subcubic_one_round():
    checked = 0
    for order in range(2, 6):
        possible = list(combinations(range(order), 2))
        for chosen in range(1 << len(possible)):
            graph = adjacency(order, (possible[i] for i in members(chosen)))
            if max(row.bit_count() for row in graph) > 3:
                continue
            times = [completion_time(graph, blue) for blue in range(1 << order)]
            for blue, intact in enumerate(times):
                if intact > 1:
                    continue
                seeds = tuple(members(blue))
                for size in range(1, len(seeds)):
                    for lost in combinations(seeds, size):
                        delayed = times[blue ^ mask(lost)]
                        if delayed <= order:
                            if delayed > 1 + 3 * size:
                                raise AssertionError(('subcubic one-round bound', graph, blue, lost))
                            checked += 1
    return checked


def compact_private_path_lengths(budget, protected_count):
    """Choose the smaller of the layouts with one or two long paths at each end."""
    def length(losses):
        return (3 * losses - 1) // 2

    longest = length(budget)
    layouts = ((1, 1),) if budget <= 2 else (
        (length(budget // 2 + 1), 1),
        (length(budget // 3 + 1), 2),
    )
    return min((tuple(longest if index < ends or index >= protected_count - ends else inner
                      for index in range(protected_count))
                for inner, ends in layouts), key=sum)


def protect_seeds(degree, edges, blue, order, deliberately_lost, seed, *, clique_support=True,
                  neutral_rank=0, unprotected_blue=(), fault_budget=None, compact=False):
    """Add private blue paths and, for the original construction, a killing support."""
    budget = len(deliberately_lost) if fault_budget is None else fault_budget
    if budget < len(deliberately_lost):
        raise ValueError('The protection budget must cover the designated loss')
    support = range(order, order + (0 if compact else budget + 1))
    order = support.stop
    support_pairs = (combinations(support, 2) if clique_support and budget <= degree
                     else pairwise(support))
    attachment = order
    for left, right in support_pairs:
        edges.extend(((order, left), (order, right)))
        blue.append(order)
        order += 1
    if support and degree != 3:
        edges.append((seed, attachment))

    paths = []
    unprotected = set(deliberately_lost).union(unprotected_blue)
    protected = [vertex for vertex in blue if vertex not in unprotected]
    lengths = (compact_private_path_lengths(budget, len(protected))
               if compact else (2 * budget + 2,) * len(protected))
    for vertex, length in zip(protected, lengths):
        path = range(order, order + length)
        edges.append((vertex, path[0]))
        edges.extend(pairwise(path))
        if support and degree == 3 and vertex == attachment:
            edges.append((seed, path[-1]))
        blue.extend(path)
        paths.append(tuple(path))
        order = path.stop
    if neutral_rank:
        start = order
        order = append_subcubic_blue_cycles(edges, paths[0][-1], order, neutral_rank, budget)
        blue.extend(range(start, order))
    return adjacency(order, edges), mask([*blue, *support]), mask(support), paths


def append_blue_triangles(edges, blue, anchor, order, count):
    for _ in range(count):
        x, y, z = range(order, order + 3)
        edges.extend(((anchor, x), (x, y), (y, z), (z, x)))
        blue.extend((x, y, z))
        anchor = y
        order += 3
    return order


def relay_arm(edges, blue, parent, order, length):
    vertices = []
    for _ in range(length):
        relay, child = order, order + 1
        edges.extend(((parent, relay), (relay, child)))
        blue.append(relay)
        vertices.append(child)
        parent = child
        order += 2
    return order, vertices


def low_rank_recovery_certificate(rounds, losses, cycle_rank, *, degree=4):
    seed, endpoint = 0, rounds
    edges, blue, deliberately_lost = list(pairwise(range(rounds + 1))), [seed], []
    additions = [(v,) for v in range(1, rounds + 1)]
    cyclic_blocks = min(losses, cycle_rank)
    extra = min((cycle_rank - cyclic_blocks) // 2, cyclic_blocks * (degree - 3))
    remaining = extra
    order = rounds + 1
    for index in range(losses):
        root = order
        order += 1
        deliberately_lost.append(root)
        blue.append(root)
        order, left = relay_arm(edges, blue, root, order, rounds)
        order, right = relay_arm(edges, blue, root, order, rounds)
        entry = left[-1]
        main = [(v,) for v in [*reversed(left), root, *right]]
        if index < cyclic_blocks:
            branch, guard = order, order + 1
            order += 2
            order, first = relay_arm(edges, blue, branch, order, rounds - 1)
            order, second = relay_arm(edges, blue, branch, order, rounds - 1)
            edges.extend(((root, branch), (branch, guard)))
            targets, arms = [], []
            for _ in range(min(degree - 3, remaining)):
                order, arm = relay_arm(edges, blue, root, order, rounds - 1)
                target = order
                order += 1
                edges.extend(((arm[-1], target), (target, entry)))
                arms.append(arm)
                targets.append(target)
            remaining -= len(targets)
            edges.append((second[-1], targets[0] if targets else entry))
            for left_target, right_target in pairwise([*targets, entry]):
                edges.extend(((order, left_target), (order, right_target)))
                blue.append(order)
                order += 1
            for offset, wave in enumerate(zip(*(reversed(arm) for arm in arms)), 1):
                main[offset] = (*main[offset], *wave)
            entry = first[-1]
            additions.extend((v,) for v in [*reversed(first), branch, *second, *targets])
            main[rounds + 1] = (right[0], guard)
        edges.append((endpoint, entry))
        additions.extend(main)
        endpoint = right[-1]
    unused_rank = cycle_rank - cyclic_blocks - 2 * extra
    order = append_blue_triangles(edges, blue, seed, order, unused_rank)
    graph, initial, support, paths = protect_seeds(
        degree, edges, blue, order, deliberately_lost, seed, clique_support=False
    )
    return graph, initial, mask(deliberately_lost), support, paths, additions


def recovery_detour(edges, blue, parent, order, length):
    center, guard = order, order + 1
    edges.extend(((parent, center), (center, guard)))
    order, left = relay_arm(edges, blue, center, order + 2, length)
    order, right = relay_arm(edges, blue, center, order, length)
    return order, left[-1], right[-1], guard, [*reversed(left), center, *right]


def deep_detour_recovery_certificate(rounds, losses, cycle_rank, degree):
    seed, endpoint = 0, rounds
    edges, blue, deliberately_lost = list(pairwise(range(rounds + 1))), [seed], []
    additions = [(v,) for v in range(1, rounds + 1)]
    shallow = min(losses, cycle_rank)
    deep = min(cycle_rank - shallow, shallow * (degree - 3))
    remaining = deep
    order = rounds + 1
    for index in range(losses):
        root = order
        order += 1
        deliberately_lost.append(root)
        blue.append(root)
        order, left = relay_arm(edges, blue, root, order, rounds)
        order, right = relay_arm(edges, blue, root, order, rounds)
        main = [(v,) for v in [*reversed(left), root, *right]]
        if index < shallow:
            first_releases, second_releases = [], []
            count = min(degree - 3, remaining)
            remaining -= count
            for _ in range(count):
                relay, parent = order, order + 1
                blue.append(relay)
                edges.extend(((root, relay), (relay, parent)))
                order, entry, exit_vertex, guard, sequence = recovery_detour(
                    edges, blue, parent, order + 2, rounds - 2
                )
                edges.append((endpoint, entry))
                additions.extend((v,) for v in sequence)
                first_releases.append(parent)
                second_releases.append(guard)
                endpoint = exit_vertex
            order, entry, exit_vertex, guard, sequence = recovery_detour(
                edges, blue, root, order, rounds - 1
            )
            edges.append((endpoint, entry))
            additions.extend((v,) for v in sequence)
            main[rounds + 1] = (right[0], guard, *first_releases)
            main[rounds + 2] = (right[1], *second_releases)
            endpoint = exit_vertex
        edges.append((endpoint, left[-1]))
        additions.extend(main)
        endpoint = right[-1]
    order = append_blue_triangles(edges, blue, seed, order, cycle_rank - shallow - deep)
    graph, initial, support, paths = protect_seeds(
        degree, edges, blue, order, deliberately_lost, seed, clique_support=False
    )
    return graph, initial, mask(deliberately_lost), support, paths, additions


def shared_center_recovery_certificate(rounds, losses, cycle_rank, *, detours=0):
    seed, endpoint = 0, rounds
    first, second = rounds + 1, rounds + 2
    edges = list(pairwise(range(rounds + 1)))
    blue, deliberately_lost = [seed, first, second], [first, second]
    sequence = list(range(1, rounds + 1))
    centers = (cycle_rank - detours + 1) // 2
    order = second + 1
    guards = {}
    for root in (first, second)[:detours]:
        order, entry, exit_vertex, guard, detour = recovery_detour(edges, blue, root, order, rounds - 1)
        edges.append((endpoint, entry))
        sequence.extend(detour)
        guards[root] = guard
        endpoint = exit_vertex
    for _ in range(centers):
        source, center = order, order + 1
        order += 2
        edges.extend(((source, first), (source, second), (source, center)))
        blue.append(source)
        order, left = relay_arm(edges, blue, center, order, rounds - 1)
        order, right = relay_arm(edges, blue, center, order, rounds - 1)
        edges.append((endpoint, left[-1]))
        sequence.extend([*reversed(left), center, *right])
        endpoint = right[-1]

    order, approach = relay_arm(edges, blue, first, order, rounds)
    edges.append((endpoint, approach[-1]))
    sequence.extend([*reversed(approach), first, second])
    order, departure = relay_arm(edges, blue, second, order, rounds)
    sequence.extend(departure)
    endpoint = departure[-1]

    for index in range(2, losses):
        root = order
        order += 1
        blue.append(root)
        deliberately_lost.append(root)
        if index < detours:
            order, entry, exit_vertex, guard, detour = recovery_detour(edges, blue, root, order, rounds - 1)
            edges.append((endpoint, entry))
            sequence.extend(detour)
            guards[root] = guard
            endpoint = exit_vertex
        order, left = relay_arm(edges, blue, root, order, rounds)
        order, right = relay_arm(edges, blue, root, order, rounds)
        edges.append((endpoint, left[-1]))
        sequence.extend([*reversed(left), root, *right])
        endpoint = right[-1]

    spare_rank = cycle_rank - (2 * centers - 1 + detours)
    order = append_blue_triangles(edges, blue, seed, order, spare_rank)
    degree = max(4, centers + 1 + bool(detours))
    graph, initial, support, paths = protect_seeds(
        degree, edges, blue, order, deliberately_lost, seed, clique_support=False
    )
    arrivals = {root: index for index, root in enumerate(sequence) if root in guards}
    additions = [(vertex,) for vertex in sequence]
    for root, guard in guards.items():
        additions[arrivals[root] + 1] += (guard,)
    return graph, initial, mask(deliberately_lost), support, paths, additions, degree


def sparse_one_round_certificate(losses, cycle_rank):
    extra_from_pair = (cycle_rank - 3) // 2
    if losses >= 2 and extra_from_pair > losses:
        cyclic_blocks = losses - 2
        pair_targets = (extra_from_pair - cyclic_blocks,)
    else:
        cyclic_blocks = min(losses, cycle_rank // 2)
        pair_targets = ()
    return assemble_one_round_certificate(losses, cycle_rank, cyclic_blocks, pair_targets)


def assemble_one_round_certificate(losses, cycle_rank, cyclic_blocks, pair_targets, *,
                                   triple_pairs=()):
    spare_cycles = cycle_rank - 2 * cyclic_blocks - sum(2 * q + 3 for q in pair_targets)
    shared_blocks = [(2, ((0, 1),) * count) for count in pair_targets]
    if triple_pairs:
        spare_cycles -= 2 * len(triple_pairs) + 4
        shared_blocks.append((3, triple_pairs))
    seed, endpoint = 0, 1
    edges, blue, deliberately_lost = [(seed, endpoint)], [seed], []
    order = 2
    degree = 4
    for size, pairs in shared_blocks:
        roots = tuple(range(order, order + size))
        blue.extend(roots)
        deliberately_lost.extend(roots)
        for index in range(size):
            root_degree = 1 + (index < 2) + sum(index in pair for pair in pairs)
            degree = max(degree, root_degree)
        order, targets, tail = one_round_block(roots, pairs, edges, blue, order + size)
        for left, right in pairwise([endpoint, *targets]):
            edges.extend(((order, left), (order, right)))
            blue.append(order)
            order += 1
        endpoint = tail

    remaining_seeds = losses - len(deliberately_lost)
    for index in range(remaining_seeds):
        if index < cyclic_blocks:
            a, b, c, z, p, q, u = range(order, order + 7)
            edges.extend(((endpoint, a), (a, z), (a, b), (a, u), (b, u),
                          (z, p), (b, p), (z, q), (c, q)))
            blue.extend((z, p, q, u))
            endpoint = c
            order += 7
        else:
            a, b, z, p = range(order, order + 4)
            edges.extend(pairwise((endpoint, a, z, p, b)))
            blue.extend((z, p))
            endpoint = b
            order += 4
        deliberately_lost.append(z)
    order = append_blue_triangles(edges, blue, seed, order, spare_cycles)
    graph, initial, support, paths = protect_seeds(
        degree, edges, blue, order, deliberately_lost, seed, clique_support=False
    )
    return graph, initial, mask(deliberately_lost), support, paths, degree


def append_subcubic_blue_cycles(edges, anchor, order, count, losses):
    for _ in range(count):
        cycle = range(order, order + 2 * losses + 4)
        edges.append((anchor, cycle.start))
        edges.extend(pairwise([*cycle, cycle.start]))
        anchor = cycle[-1]
        order = cycle.stop
    return order


def subcubic_rank_certificate(losses, cycle_rank):
    path, blue, lost, support = path_certificate(1, losses)
    edges = list(pairwise(range(len(path))))
    order = append_subcubic_blue_cycles(edges, len(path) - 2, len(path), cycle_rank, losses)
    return adjacency(order, edges), blue | mask(range(len(path), order)), lost, support


def bounded_rank_certificate(degree, losses, cycle_rank):
    if degree >= 5 and cycle_rank >= 2 * losses:
        capacity = degree - 4
        if degree >= 9 and losses >= 3 and losses % 2:
            pairs = losses // 2
            remaining_rank = cycle_rank - 2 * losses - (2 * capacity + 3) * pairs
            triple_gain = min((capacity - 3) // 2, (remaining_rank - 5) // 2)
            if triple_gain > 0:
                targets = capacity + triple_gain + 5
                available = list(degree_block_pairs(degree, 3))
                required = [(0, 1), (0, 2)]
                for pair in required:
                    available.remove(pair)
                triple_pairs = required + available[:targets - len(required)]
                return assemble_one_round_certificate(
                    losses, cycle_rank, 0, (capacity + 2,) * (pairs - 1),
                    triple_pairs=triple_pairs
                )
        blocks, spare_rank = divmod(cycle_rank - 2 * losses, 2 * capacity + 3)
        gain = min(capacity * (losses // 2),
                   capacity * blocks + max(0, (spare_rank - 3) // 2))
        full, partial = divmod(gain, capacity)
        pair_targets = (capacity + 2,) * full
        if partial:
            pair_targets += (partial + 2,)
        return assemble_one_round_certificate(losses, cycle_rank,
                                              losses - 2 * len(pair_targets), pair_targets)
    return assemble_one_round_certificate(losses, cycle_rank, min(losses, cycle_rank // 2), ())


def one_round_certificate(degree, losses):
    deliberately_lost = list(range(losses))
    edges = []
    blue = deliberately_lost[:]
    terminal = []
    order = losses
    for left, right in SINGLE['cyclic_pairs'](deliberately_lost, degree - 1):
        source, target = order, order + 1
        order += 2
        edges.extend(((source, left), (source, right), (source, target)))
        blue.append(source)
        terminal.append(target)
    seed = order
    blue.append(seed)
    edges.extend(pairwise([seed, *terminal, deliberately_lost[0]]))
    graph, initial, support, paths = protect_seeds(
        degree, edges, blue, seed + 1, deliberately_lost, seed
    )
    return graph, initial, mask(deliberately_lost), support, paths, len(terminal)


def degree_block_pairs(degree, size):
    if size == 2:
        return ((0, 1),) * (degree - 2)
    if size == 3:
        count, parity = divmod(degree - 2, 2)
        return ((0, 1),) * count + ((0, 2), (1, 2)) * (count + parity)
    return ()


def one_round_block(roots, pairs, edges, blue, order):
    targets = []
    for left, right in pairs:
        source, target = order, order + 1
        order += 2
        edges.extend(((source, roots[left]), (source, roots[right]), (source, target)))
        blue.append(source)
        targets.append(target)

    direct = range(order, order + len(roots))
    enter, tail, enter_source, tail_source = range(direct.stop, direct.stop + 4)
    edges.extend(zip(roots, direct))
    edges.extend((tail, child) for child in direct[1:])
    edges.extend(((enter, direct[0]), (enter_source, roots[0]), (enter_source, enter),
                  (tail_source, roots[min(1, len(roots) - 1)]), (tail_source, tail)))
    blue.extend((enter_source, tail_source))
    return tail_source + 1, [*targets, *direct, enter], tail


def sharp_one_round_certificate(degree, losses):
    """Build a sharp connected example for degree at least four."""
    roots = list(range(losses))
    tail_size = 0 if losses % 2 == 0 else (1 if losses == 1 or degree <= 6 else 3)
    split = losses - tail_size
    groups = [roots[i:i + 2] for i in range(0, split, 2)]
    if tail_size:
        groups.append(roots[split:])

    seed, prefix = losses, losses + 1
    edges, blue = [(seed, prefix)], [*roots, seed]
    order = prefix + 1
    for group in groups:
        pairs = degree_block_pairs(degree, len(group))
        order, targets, tail = one_round_block(group, pairs, edges, blue, order)
        for left, right in pairwise([prefix, *targets]):
            edges.extend(((order, left), (order, right)))
            blue.append(order)
            order += 1
        prefix = tail
    graph, initial, support, paths = protect_seeds(degree, edges, blue, order, roots, seed)
    return graph, initial, mask(roots), support, paths


def sharp_one_round_time(degree, losses):
    if losses == 1:
        return 5
    cap = 1 + degree * losses // 2 + 2 * losses
    if losses % 2 and degree >= 6:
        cap -= 1 if degree == 6 else 2 - degree % 2
    return cap


def layered_certificate(degree, rounds, losses):
    block, block_blue, size, _, branches = SINGLE['nonterminal_layers'](degree, rounds, False)
    block_parents = [v for branch in branches for v in branch]
    edges, blue, parents, deliberately_lost = [], [], [], []
    for copy in range(losses):
        start = copy * size
        deliberately_lost.append(start)
        edges.extend((start + a, start + b) for a, b in block)
        blue.extend(start + v for v in block_blue)
        parents.extend(start + w for w in block_parents)
    order, targets, early = SINGLE['guarded_terminal_layer'](
        degree, edges, blue, losses * size, parents
    )
    seed, first, second = range(order, order + 3)
    order += 3
    edges.extend(((seed, first), (first, second)))
    blue.append(seed)
    for left, right in pairwise([second, *targets]):
        edges.extend(((order, left), (order, right)))
        blue.append(order)
        order += 1
    graph, initial, support, paths = protect_seeds(
        degree, edges, blue, order, deliberately_lost, seed
    )
    return graph, initial, mask(deliberately_lost), support, paths, early


def subcubic_detour_center(edges, blue, host, order):
    parent, guard, relay, center = range(order, order + 4)
    blue.append(relay)
    edges.extend(((host, parent), (parent, guard), (parent, relay), (relay, center)))
    return order + 4, parent, guard, center


def subcubic_detour(edges, blue, host, order, length):
    order, parent, guard, center = subcubic_detour_center(edges, blue, host, order)
    order, incoming = relay_arm(edges, blue, center, order, length)
    order, outgoing = relay_arm(edges, blue, center, order, length)
    return order, parent, guard, center, incoming, outgoing


def append_subcubic_arm_block(edges, blue, lost, endpoint, order, detour, *, rounds=2):
    root = order
    blue.append(root)
    lost.append(root)
    order, left = relay_arm(edges, blue, root, order + 1, rounds)
    order, right = relay_arm(edges, blue, root, order, rounds)
    waves = [(v,) for v in [*reversed(left), root, *right]]
    if detour:
        order, parent, guard, center, incoming, outgoing = subcubic_detour(
            edges, blue, root, order, rounds - 2
        )
        sequence = [*reversed(incoming), center, *outgoing]
        edges.extend(((endpoint, sequence[0]), (sequence[-1], left[-1])))
        waves[rounds + 1] += (guard,)
        waves = [(v,) for v in sequence] + waves
        waves[len(incoming) + 1] += (parent,)
    else:
        edges.append((endpoint, left[-1]))
    return order, right[-1], waves


def subcubic_low_rank_certificate(losses, cycle_rank, *, rounds=2):
    seed, endpoint = 0, rounds
    edges, blue, lost = list(pairwise(range(rounds + 1))), [seed], []
    additions = [(v,) for v in range(1, rounds + 1)]
    order = rounds + 1
    for block in range(losses):
        order, endpoint, waves = append_subcubic_arm_block(
            edges, blue, lost, endpoint, order, block < cycle_rank, rounds=rounds
        )
        additions.extend(waves)
    graph, initial, support, paths = protect_seeds(
        3, edges, blue, order, lost, seed, clique_support=False,
        neutral_rank=max(0, cycle_rank - losses)
    )
    return graph, initial, mask(lost), support, paths, additions


def subcubic_center_splice_plan(rounds, losses, cycle_rank, depth_limit, *, main_sites=None):
    if main_sites is None:
        main_sites = [losses, *([2 * losses] * max(0, rounds - 2))]
    capacities, splices = [], []
    shallower_sites = arm_sites = 0
    for depth, sites in enumerate(main_sites):
        if depth >= 2:
            sites += capacities[depth - 2] - splices[depth - 1] - splices[depth - 2]
        if depth >= 3:
            arm_sites += 2 * capacities[depth - 3]
        sites += arm_sites
        splice = 0
        if 2 <= depth <= rounds - 3 and (depth_limit is None or depth <= depth_limit):
            splice = min(capacities[depth - 2], max(0, cycle_rank - shallower_sites - sites))
        splices.append(splice)
        capacities.append(sites + splice)
        shallower_sites += capacities[-1]
    return {depth: count for depth, count in enumerate(splices) if count}


DetourPlan = namedtuple('DetourPlan', ('guard', 'incoming', 'outgoing', 'center'))


LayerChoice = namedtuple('LayerChoice', ('remaining', 'copies', 'ordinary_gain',
                                         'activation_rank', 'extra_capacity'))


def subcubic_ordinary_margins(rounds):
    """Count the ordinary marginal gains by deadline and gain."""
    margins = [Counter(), Counter()]
    shortened = [Counter(), Counter()]
    prefixes = [Counter(), Counter()]
    for remaining in range(2, rounds + 1):
        first = 2 * remaining - 3
        counts = Counter({first: 1})
        if remaining == 4:
            counts[1] = 1
        if remaining >= 5:
            for group in (margins[remaining - 2], shortened[remaining - 2],
                          prefixes[remaining - 3], prefixes[remaining - 5]):
                counts.update(group)
        margins.append(counts)
        shortened_counts = counts.copy()
        del shortened_counts[first]
        if first > 1:
            shortened_counts[first - 1] += 1
        shortened.append(shortened_counts)
        prefixes.append(prefixes[-1] + counts)
    return margins, shortened


def subcubic_rank_model(rounds, losses):
    margins, shortened = subcubic_ordinary_margins(rounds)
    ordinary = Counter()
    layers = []
    for remaining in range(2, rounds + 1):
        copies = losses if remaining == rounds else 2 * losses
        gains = margins[remaining]
        ordinary.update({value: copies * count for value, count in gains.items()})
        full_gain = sum(value * count for value, count in gains.items())
        extra = 2 ** (remaining - 2) - full_gain
        if remaining >= 3 and extra > 0:
            layers.append(LayerChoice(remaining, copies, full_gain,
                                      2 * full_gain - sum(gains.values()), extra))
    return margins, shortened, ordinary, layers


def subcubic_first_layered_rank(rounds, losses):
    """First rank with a strict benefit from the layered construction."""
    _, _, ordinary, layers = subcubic_rank_model(rounds, losses)
    if not layers:
        return None
    return sum(ordinary.values()) + min(layer.activation_rank for layer in layers) + 2


def subcubic_layer_frontier(groups, limit):
    """Find undominated cost, benefit, and plan triples."""
    frontier = [(0, 0, ())]
    for deadline, copies, unit_cost, unit_benefit in groups:
        remaining = min(copies, limit // unit_cost)
        chunk = 1
        while remaining:
            count = min(chunk, remaining)
            extra_cost = count * unit_cost
            extra_benefit = count * unit_benefit
            candidates = {cost: (benefit, plan) for cost, benefit, plan in frontier}
            for cost, benefit, plan in frontier:
                cost += extra_cost
                benefit += extra_benefit
                if cost <= limit and benefit > candidates.get(cost, (-1, ()))[0]:
                    candidates[cost] = (benefit, (*plan, (deadline, count)))

            frontier = []
            largest = -1
            for cost, (benefit, plan) in sorted(candidates.items()):
                if benefit > largest:
                    frontier.append((cost, benefit, plan))
                    largest = benefit
            remaining -= count
            chunk *= 2
    return frontier


def subcubic_layer_totals(layers):
    activation = sum(layer.copies * layer.activation_rank for layer in layers)
    capacity = sum(layer.copies * layer.extra_capacity for layer in layers)
    return activation, capacity


def subcubic_layer_omissions(layers, limit):
    groups = ((layer.remaining, layer.copies, layer.extra_capacity, layer.activation_rank)
              for layer in layers)
    return subcubic_layer_frontier(groups, limit)


def subcubic_saturation_shortfall_limit(layers, lost_rounds):
    """Largest rank shortfall that costs at most lost_rounds from full capacity."""
    _, full_capacity = subcubic_layer_totals(layers)
    if not 0 <= lost_rounds <= full_capacity:
        raise ValueError('The allowed loss must lie between zero and full layered capacity')
    _, saved, _ = subcubic_layer_omissions(layers, lost_rounds)[-1]
    return 2 * lost_rounds + saved


def subcubic_growth_polynomial(value):
    return value ** 4 - 2 * value ** 3 + value - 1


def subcubic_growth_factor_bounds(bits):
    """Enclose the ordinary growth factor by rational bisection."""
    low, high = Fraction(9, 5), Fraction(2)
    for _ in range(bits):
        mid = (low + high) / 2
        if subcubic_growth_polynomial(mid) < 0:
            low = mid
        else:
            high = mid
    return low, high


def subcubic_dyadic_cover_cost(numerator, bits, growth):
    """Evaluate the cover cost of a dyadic demand for a fixed growth factor."""
    if numerator == 1 << bits:
        return Fraction(1)
    prefix, best, price = Fraction(0), Fraction(1), Fraction(1)
    for digit in range(bits - 1, -1, -1):
        price /= growth
        if numerator & (1 << digit):
            prefix += price
        else:
            best = min(best, prefix + price)
    return min(best, prefix)


def check_subcubic_cover_peak():
    """Verify the strict grid inequalities used in the global peak proof."""
    low_r, high_r = Fraction(18667, 10000), Fraction(18668, 10000)
    if not subcubic_growth_polynomial(low_r) < 0 < subcubic_growth_polynomial(high_r):
        raise AssertionError('The cover-peak certificate must bracket the growth factor')

    peak_lower = Fraction(5, 36) - low_r ** -6
    outer_bits = 8
    outer_grid = 1 << outer_bits
    outer_slack = min(
        peak_lower + Fraction(i, outer_grid) - subcubic_dyadic_cover_cost(i + 1, outer_bits, low_r)
        for i in range(outer_grid)
        if 4 * i < 3 * outer_grid or 8 * i >= 7 * outer_grid
    )

    slope_upper = (high_r / 2) ** 3
    inner_bits = 10
    inner_grid = 1 << inner_bits
    inner_slack = min(
        1 - slope_upper * (Fraction(8, 9) - Fraction(i, inner_grid))
        - subcubic_dyadic_cover_cost(i + 1, inner_bits, low_r)
        for i in range(7 * inner_grid // 8)
    )
    if outer_slack <= Fraction(19, 10000) or inner_slack <= Fraction(3, 10000):
        raise AssertionError(('cover peak certificate slack', outer_slack, inner_slack))
    return outer_slack, inner_slack


def subcubic_max_omission_gap_bounds(losses, bits=24):
    """Enclose the maximum gap between fractional and integer packing."""
    if not isinstance(losses, int) or losses < 1 or not isinstance(bits, int) or bits < 1:
        raise ValueError('The loss count and precision must be positive integers')
    low_r, high_r = subcubic_growth_factor_bounds(bits + 8)
    lower = (Fraction(5, 36) - low_r ** -6) / (losses * high_r ** 2)
    upper = (Fraction(5, 36) - high_r ** -6) / (losses * low_r ** 2)
    return lower, upper


def subcubic_omission_profile_bounds(losses, normalized_shortfall, bits=24):
    """Enclose the fixed-loss dyadic packing coefficient A_k(x)."""
    x = Fraction(normalized_shortfall)
    if not isinstance(losses, int) or losses < 1 or not isinstance(bits, int) or bits < 1:
        raise ValueError('The loss count and precision must be positive integers')
    if not Fraction(1, 2) <= x <= 1:
        raise ValueError('The normalized shortfall must lie in [1/2, 1]')
    low_r, high_r = subcubic_growth_factor_bounds(bits + 8)
    cells = 4 * losses * (x - Fraction(1, 2))
    whole = int(cells)
    demand = 1 - (cells - whole)

    grid = demand * (1 << bits)
    low_digit = grid.numerator // grid.denominator
    high_digit = -(-grid.numerator // grid.denominator)
    low_cost = subcubic_dyadic_cover_cost(low_digit, bits, high_r)
    high_cost = subcubic_dyadic_cover_cost(high_digit, bits, low_r)

    lower = 2 / (high_r ** 2 * (high_r - 1))
    upper = 2 / (low_r ** 2 * (low_r - 1))
    lower += (whole + 1 - high_cost) / (losses * high_r ** 2)
    upper += (whole + 1 - low_cost) / (losses * low_r ** 2)
    return lower, upper


def subcubic_layer_selection(layers, budget):
    """Choose layers by activation rank, or choose omissions near saturation."""
    if not layers or budget < min(layer.activation_rank for layer in layers) + 2:
        return 0, ()
    full_activation, full_capacity = subcubic_layer_totals(layers)
    full_plan = tuple((layer.remaining, layer.copies) for layer in layers)
    if budget >= full_activation + 2 * full_capacity:
        return full_capacity, full_plan

    deficit = full_capacity - (budget - full_activation) // 2
    if budget >= full_activation and deficit - 1 < budget - 2:
        frontier = subcubic_layer_omissions(layers, deficit - 1)
        loss, saved, excluded = max(
            frontier, key=lambda item: min(full_capacity - item[0],
                                           (budget - full_activation + item[1]) // 2)
        )
        kept = dict(full_plan)
        for remaining, count in excluded:
            kept[remaining] -= count
        gain = min(full_capacity - loss, (budget - full_activation + saved) // 2)
        return gain, tuple((remaining, count) for remaining, count in kept.items() if count)

    groups = ((layer.remaining, layer.copies, layer.activation_rank, layer.extra_capacity)
              for layer in layers)
    frontier = subcubic_layer_frontier(groups, budget - 2)
    rank, capacity, plan = max(frontier, key=lambda item: min(item[1], (budget - item[0]) // 2))
    return min(capacity, (budget - rank) // 2), plan


def take_rank_margins(groups, budget):
    """Take the largest available margins, keeping their site labels."""
    groups = list(groups)
    counts_by_gain = defaultdict(list)
    for index, margins in enumerate(groups):
        for gain, count in margins.items():
            counts_by_gain[gain].append((index, count))

    spent, score = [0] * len(groups), 0
    for gain in sorted(counts_by_gain, reverse=True):
        for index, count in counts_by_gain[gain]:
            selected = min(count, budget)
            spent[index] += selected
            score += gain * selected
            budget -= selected
            if budget == 0:
                return score, spent
    return score, spent


def subcubic_rank_value(rounds, losses, cycle_rank):
    """Return the optimum in the combined family without building a plan."""
    _, _, ordinary, layers = subcubic_rank_model(rounds, losses)
    ordinary_rank = sum(ordinary.values())
    bonus, _ = subcubic_layer_selection(layers, cycle_rank - ordinary_rank)
    if bonus:
        gain = sum(value * count for value, count in ordinary.items()) + bonus
    else:
        gain, _ = take_rank_margins([ordinary], cycle_rank)
    return rounds + losses * (2 * rounds + 1) + gain


def subcubic_rank_allocation(rounds, losses, cycle_rank):
    """Optimize the combined detour construction and recover its allocation."""
    margins, shortened, ordinary, layers = subcubic_rank_model(rounds, losses)
    bonus, chosen = subcubic_layer_selection(layers, cycle_rank - sum(ordinary.values()))
    layer_types = {layer.remaining: layer for layer in layers}
    chosen_by_rounds = Counter()
    for remaining, count in chosen:
        chosen_by_rounds[remaining] += count
    layered, ordinary_sites = {}, []
    unassigned_bonus = bonus
    for block in range(losses):
        for depth in range(rounds - 1):
            for side in range(1 if depth == 0 else 2):
                site = (block, depth, side)
                remaining = rounds - depth
                if unassigned_bonus and chosen_by_rounds[remaining]:
                    layer = layer_types[remaining]
                    extra = min(unassigned_bonus, layer.extra_capacity)
                    layered[site] = layer.ordinary_gain + extra
                    unassigned_bonus -= extra
                    chosen_by_rounds[remaining] -= 1
                else:
                    ordinary_sites.append(site)
    assert unassigned_bonus == 0

    def detour(remaining, budget):
        if budget == 0:
            return None
        incoming = tuple(range(remaining - 3, 1, -1))
        center_allowed = remaining >= 5
        outgoing = incoming[2:] if center_allowed else incoming
        groups = [margins[remaining - 2], *(margins[s] for s in incoming),
                  *(margins[s] for s in outgoing)]
        if center_allowed:
            groups.append(shortened[remaining - 2])
        _, budgets = take_rank_margins(groups, budget - 1)
        budgets = iter(budgets)
        guard = detour(remaining - 2, next(budgets))
        incoming_plans = tuple(detour(s, next(budgets)) for s in incoming)
        outgoing_plans = tuple(detour(s, next(budgets)) for s in outgoing)
        center = detour(remaining - 2, next(budgets)) if center_allowed else None
        if center_allowed and center is None:
            outgoing_plans = (None,) * min(2, len(incoming)) + outgoing_plans
        return DetourPlan(guard, incoming_plans, outgoing_plans, center)

    groups = [margins[rounds - site[1]] for site in ordinary_sites]
    if bonus:
        budgets = [sum(group.values()) for group in groups]
        gain = sum(value * count for value, count in ordinary.items()) + bonus
    else:
        gain, budgets = take_rank_margins(groups, cycle_rank)
    detours = {site: detour(rounds - site[1], spent)
               for site, spent in zip(ordinary_sites, budgets) if spent}
    return rounds + losses * (2 * rounds + 1) + gain, detours, layered


def subcubic_recursive_rank_certificate(rounds, losses, cycle_rank, *, splice_centers=False,
                                        splice_depth_limit=2, layered_detours=None,
                                        ordinary_detours=None, fault_budget=None, compact=False):
    edges, blue, lost = list(pairwise(range(rounds + 1))), [0], []
    main_paths = []
    detours = [[] for _ in range(losses)]
    hosts, releases = [], []
    planned_hosts = {}
    layered_releases, layered_sources, terminal_ends = [], [], set()
    layered_detours = dict(layered_detours or ())
    layered_rank = 2 * sum(layered_detours.values())
    if layered_rank > cycle_rank:
        raise ValueError('Layered detours exceed the cycle rank')
    main_sites = [0] * max(1, rounds - 1)
    order = rounds + 1

    def link_through_relay(left, right):
        nonlocal order
        edges.extend(((order, left), (order, right)))
        blue.append(order)
        order += 1

    def queue_host(depth, host, block, plan=None):
        if ordinary_detours is not None:
            if plan is None:
                return
            planned_hosts[host] = plan
        heappush(hosts, (depth, host, block))

    def place_main_site(block, depth, side, host):
        nonlocal order
        targets = layered_detours.pop((block, depth, side), 0)
        if not targets:
            plan = ordinary_detours.get((block, depth, side)) if ordinary_detours is not None else None
            queue_host(depth, host, block, plan)
            main_sites[depth] += 1
            return
        if not (depth <= rounds - 3 and 1 <= targets <= 2 ** (rounds - depth - 2)):
            raise ValueError('Invalid number of targets for a layered detour')

        frontier = [order]
        edges.append((host, order))
        order += 1
        levels = [frontier]
        for _ in range(rounds - depth - 2):
            children = []
            for vertex in frontier:
                for _ in range(2):
                    order, arm = relay_arm(edges, blue, vertex, order, 1)
                    children.extend(arm)
            frontier = children
            levels.append(frontier)

        path = []
        for index in range(targets):
            source, terminal = order, order + 1
            order += 2
            edges.extend(((source, frontier[index]),
                          (source, frontier[(index + 1) % len(frontier)]),
                          (source, terminal)))
            blue.append(source)
            layered_sources.append(source)
            path.append(terminal)
        for left, right in pairwise(path):
            link_through_relay(left, right)
        terminal_ends.update((path[0], path[-1]))
        detours[block].append((depth, path))
        layered_releases.append((host, levels))

    for block in range(losses):
        root = order
        blue.append(root)
        lost.append(root)
        order, left = relay_arm(edges, blue, root, order + 1, rounds)
        order, right = relay_arm(edges, blue, root, order, rounds)
        main_paths.append([*reversed(left), root, *right])
        place_main_site(block, 0, 0, root)
        for depth, (a, b) in enumerate(zip(left[:-2], right[:-2]), 1):
            place_main_site(block, depth, 0, a)
            place_main_site(block, depth, 1, b)
    if layered_detours:
        raise ValueError('Unknown main-path site for a layered detour')

    ordinary_rank = cycle_rank - layered_rank
    splices = (
        subcubic_center_splice_plan(rounds, losses, ordinary_rank, splice_depth_limit,
                                   main_sites=main_sites)
        if splice_centers and ordinary_detours is None else {}
    )

    def attach_detour(depth, host, block, plan=None):
        nonlocal order
        center_depth = depth + 2
        order, parent, guard, center = subcubic_detour_center(edges, blue, host, order)
        order, incoming = relay_arm(edges, blue, center, order, rounds - center_depth)
        splice = plan.center is not None if plan else splices.get(center_depth, 0) > 0
        if splice:
            if plan is None:
                splices[center_depth] -= 1
            child_guard = attach_detour(center_depth, center, block, plan.center if plan else None)
            order, tail = relay_arm(edges, blue, child_guard, order, rounds - center_depth - 2)
            outgoing = [child_guard, *tail]
        else:
            order, outgoing = relay_arm(edges, blue, center, order, rounds - center_depth)

        detours[block].append((depth, [*reversed(incoming), center, *outgoing]))
        releases.append((host, parent, guard, center))
        if center_depth <= rounds - 2:
            queue_host(center_depth, guard, block, plan.guard if plan else None)
        for index, a in enumerate(incoming[:-2]):
            queue_host(center_depth + 1 + index, a, block, plan.incoming[index] if plan else None)
        outgoing_start = center_depth + 1
        if splice:
            # The child detour already registered the shared guard at center_depth + 2.
            outgoing = outgoing[1:]
            outgoing_start += 2
        for index, b in enumerate(outgoing[:-2]):
            queue_host(outgoing_start + index, b, block, plan.outgoing[index] if plan else None)
        return guard

    for _ in range(ordinary_rank - sum(splices.values())):
        if not hosts:
            break
        depth, host, block = heappop(hosts)
        attach_detour(depth, host, block, planned_hosts.pop(host, None))
    if any(splices.values()):
        raise AssertionError('The detours did not use the planned center attachments')

    sequence = list(range(1, rounds + 1))
    for block, main in enumerate(main_paths):
        ordered = sorted(detours[block], key=lambda item: item[0], reverse=True)
        paths = [path for _, path in ordered]
        for path in [*paths, main]:
            if sequence[-1] in terminal_ends or path[0] in terminal_ends:
                link_through_relay(sequence[-1], path[0])
            else:
                edges.append((sequence[-1], path[0]))
            sequence.extend(path)

    arrivals = {v: time for time, v in enumerate(sequence, 1)}
    waves = [(v,) for v in sequence]
    for host, parent, guard, center in releases:
        arrivals[parent] = arrivals[center] + 1
        waves[arrivals[parent] - 1] += (parent,)
        if guard not in arrivals:
            arrivals[guard] = arrivals[host] + 1
            waves[arrivals[guard] - 1] += (guard,)
    for host, levels in layered_releases:
        for offset, vertices in enumerate(levels):
            waves[arrivals[host] + offset] += tuple(vertices)

    graph, initial, support, paths = protect_seeds(
        3, edges, blue, order, lost, 0, clique_support=False,
        neutral_rank=ordinary_rank - len(releases), unprotected_blue=layered_sources,
        fault_budget=fault_budget, compact=compact
    )
    return graph, initial, mask(lost), support, paths, waves


def subcubic_optimized_rank_certificate(rounds, losses, cycle_rank):
    expected, ordinary, layered = subcubic_rank_allocation(rounds, losses, cycle_rank)
    certificate = subcubic_recursive_rank_certificate(
        rounds, losses, cycle_rank, ordinary_detours=ordinary, layered_detours=layered
    )
    if len(certificate[-1]) != expected:
        raise AssertionError('The optimized graph and rank allocation give different times')
    return certificate


def graph_bridges(graph):
    """Return the bridges of a connected, nonempty graph as pairs of vertices."""
    n = len(graph)
    if not n:
        raise ValueError('A connected nonempty graph is required')
    discovery, low, parents = [-1] * n, [-1] * n, [-1] * n
    discovery[0] = low[0] = 0
    time = 1
    stack = [(0, graph[0])]
    bridges = []
    while stack:
        vertex, pending = stack[-1]
        if not pending:
            stack.pop()
            parent = parents[vertex]
            if parent != -1:
                if low[vertex] > discovery[parent]:
                    bridges.append((parent, vertex))
                low[parent] = min(low[parent], low[vertex])
            continue
        bit = pending & -pending
        other = bit.bit_length() - 1
        stack[-1] = (vertex, pending ^ bit)
        if other == parents[vertex]:
            continue
        if discovery[other] == -1:
            parents[other] = vertex
            discovery[other] = low[other] = time
            time += 1
            stack.append((other, graph[other]))
        else:
            low[vertex] = min(low[vertex], discovery[other])
    if time != n:
        raise ValueError('A connected graph is required')
    return bridges


def subcubic_bridge_contacts(graph, bridges):
    """Choose the least number of matching sites for a bridgeless double."""
    if not bridges:
        contacts = tuple(vertex for vertex, row in enumerate(graph) if row.bit_count() < 3)[:2]
        if len(contacts) < 2:
            raise ValueError('A bridgeless double needs two sites of degree at most two')
        return contacts

    cut = [0] * len(graph)
    for a, b in bridges:
        cut[a] |= 1 << b
        cut[b] |= 1 << a
    block_index = [-1] * len(graph)
    candidates = []
    for root in range(len(graph)):
        if block_index[root] != -1:
            continue
        index = len(candidates)
        candidates.append(None)
        block_index[root] = index
        todo = [root]
        while todo:
            vertex = todo.pop()
            if graph[vertex].bit_count() < 3 and candidates[index] is None:
                candidates[index] = vertex
            for other in members(graph[vertex] & ~cut[vertex]):
                if block_index[other] == -1:
                    block_index[other] = index
                    todo.append(other)

    block_degrees = [0] * len(candidates)
    for a, b in bridges:
        block_degrees[block_index[a]] += 1
        block_degrees[block_index[b]] += 1
    contacts = tuple(candidate for candidate, degree in zip(candidates, block_degrees)
                     if degree == 1)
    if None in contacts:
        raise ValueError('A leaf bridge block has no vertex of degree at most two')
    return contacts


def subcubic_synchronous_lift(graph, *, cubic=False, extra_contact=False):
    """Return a bridgeless lift, its copy count, and the matching sites."""
    degrees = [row.bit_count() for row in graph]
    if max(degrees, default=0) > 3:
        raise ValueError('The base graph must have maximum degree at most three')
    if cubic and extra_contact:
        raise ValueError('An extra matching contact is used only in the subcubic double')
    bridges = graph_bridges(graph)
    if cubic and all(degree == 3 for degree in degrees):
        if bridges:
            raise ValueError('A cubic base with bridges has no vacant degree for matching')
        return graph, 1, ()
    if cubic and len(graph) == 1:
        return adjacency(4, combinations(range(4), 2)), 4, (0,)

    contacts = subcubic_bridge_contacts(graph, bridges)
    copies = 4 if cubic and 1 in degrees else 2
    if cubic:
        contacts = tuple(v for v, degree in enumerate(degrees) if degree < 3)
    elif extra_contact:
        used = set(contacts)
        extra = next((v for v, degree in enumerate(degrees) if degree < 3 and v not in used), None)
        if extra is None:
            raise ValueError('No unused matching contact is available')
        contacts = (*contacts, extra)
    order = len(graph)
    lifted = [row << (copy * order) for copy in range(copies) for row in graph]
    for vertex in contacts:
        links = ((0, 1),) if copies == 2 else ((0, 1), (2, 3))
        if copies == 4 and degrees[vertex] == 1:
            links = (*links, (1, 2), (3, 0))
        for left, right in links:
            a, b = left * order + vertex, right * order + vertex
            lifted[a] |= 1 << b
            lifted[b] |= 1 << a
    return tuple(lifted), copies, contacts


def copy_mask(seeds, order, copies):
    return sum(seeds << (copy * order) for copy in range(copies))


def subcubic_layered_lift_rank(rounds, losses, *, cubic=False):
    size = 2 ** (rounds - 2)
    if not cubic:
        return losses * (21 * size - 2 * rounds - 7) + 2
    budget = 4 * losses
    core_order = rounds + 1 + losses * (21 * size - 2 * rounds - 3)
    protected_core = 1 + losses * (9 * size - 2 * rounds + 1)
    order = core_order + 2 * budget + 1 + (protected_core + budget) * (2 * budget + 2)
    return 2 * order + 1


def subcubic_bridgeless_layered_certificate(rounds, losses, *, cubic=False, cycle_rank=None):
    """Use full layers and lift a designated loss of size two or four times losses."""
    if rounds < 3 or losses < 1:
        raise ValueError('Use at least three intact rounds and one designated loss per copy')
    grafts = {(block, depth, side): 2 ** (rounds - depth - 2)
              for block in range(losses) for depth in range(rounds - 2)
              for side in range(1 if depth == 0 else 2)}
    rank = 2 * sum(grafts.values()) + 2 * losses
    budget = (4 if cubic else 2) * losses
    minimum = subcubic_layered_lift_rank(rounds, losses, cubic=cubic)
    surplus = 0 if cycle_rank is None else cycle_rank - minimum
    if surplus < 0:
        raise ValueError('The requested rank is below the rank of the unpadded lift')
    padding, remainder = divmod(surplus, 4 * budget + 8 if cubic else 2)
    if cubic and remainder:
        raise ValueError('Cubic padding requires whole rank steps of four times the budget plus eight')
    base, blue, slow, _, _, waves = subcubic_recursive_rank_certificate(
        rounds, losses, rank + padding, layered_detours=grafts, fault_budget=budget
    )
    graph, copies, _ = subcubic_synchronous_lift(base, cubic=cubic, extra_contact=bool(remainder))
    order = len(base)
    lifted_waves = [tuple(copy * order + v for copy in range(copies) for v in wave)
                    for wave in waves]
    return graph, copy_mask(blue, order, copies), copy_mask(slow, order, copies), lifted_waves


def cap_subcubic_leaves(graph, blue, padding):
    """Raise the minimum degree to two, recording the extra white arrivals."""
    edges = [(v, w) for v, row in enumerate(graph) for w in members(row) if v < w]
    order = len(graph)
    white_caps = {}
    for vertex, row in enumerate(graph):
        if row.bit_count() != 1:
            continue
        if blue & (1 << vertex):
            cycle = range(order, order + 3 + padding)
            edges.extend(pairwise(cycle))
            edges.extend(((vertex, cycle.start), (cycle.stop - 1, cycle.start)))
            blue |= mask(cycle)
            order = cycle.stop
            padding = 0
        else:
            target, first, second = range(order, order + 3)
            edges.extend(((vertex, first), (vertex, second), (target, first), (target, second)))
            blue |= mask((first, second))
            white_caps[vertex] = target
            order += 3
    if padding:
        raise ValueError('Rank padding requires an initially blue leaf')
    return adjacency(order, edges), blue, white_caps


def cubic_leaf_cycle_lift(base, blue, padding):
    """Join the blue leaves and the white-leaf caps of both copies in one cycle."""
    edges = [(v, w) for v, row in enumerate(base) for w in members(row) if v < w]
    ring = list(range(len(base), len(base) + padding))
    blue |= mask(ring)
    matched = [*ring, *(v for v, row in enumerate(base) if row.bit_count() == 2)]
    order = len(base) + padding
    white_caps = {}
    for vertex, row in enumerate(base):
        if row.bit_count() != 1:
            continue
        if blue & (1 << vertex):
            ring.append(vertex)
            continue
        first, target, second = range(order, order + 3)
        order += 3
        edges.extend(((vertex, first), (vertex, second)))
        ring.extend((first, target, second))
        blue |= mask((first, second))
        matched.append(target)
        white_caps[vertex] = target
    edges.extend((v + order, w + order) for v, w in edges[:])
    edges.extend((v, v + order) for v in matched)
    ring.extend(v + order for v in ring[:])
    edges.extend(pairwise([*ring, ring[0]]))
    return adjacency(2 * order, edges), blue, white_caps


def cubic_single_loss_lift_rank(rounds, *, three_connected=False, fault_budget=2, compact=False):
    """The smallest rank in this construction, indexed by the base intact time."""
    if rounds < 3 or fault_budget < 1:
        raise ValueError('Use at least three base rounds and a positive fault budget')
    size = 2 ** (rounds - 2)
    if three_connected:
        core_order = 14 * size - rounds + 1 - (rounds == 3)
        protected_core = 6 * size - 2 * rounds + 4 - (rounds == 3)
        if compact:
            lengths = compact_private_path_lengths(fault_budget, protected_core)
            return core_order + sum(lengths) + 10
        order = (core_order + 2 * fault_budget + 1
                 + (protected_core + fault_budget) * (2 * fault_budget + 2))
        return order + 10
    if compact or fault_budget != 2:
        raise ValueError('Adjustable protection is available for the leaf cycle lift')
    if rounds == 3:
        return 142
    return 68 * size - 19 * rounds + 73


def cubic_single_loss_lift_certificate(rounds, *, cycle_rank=None, three_connected=False,
                                       fault_budget=2, compact=False):
    """Build a cubic double with one retained root and adjustable leaf-cycle protection."""
    minimum = cubic_single_loss_lift_rank(
        rounds, three_connected=three_connected, fault_budget=fault_budget, compact=compact
    )
    surplus = 0 if cycle_rank is None else cycle_rank - minimum
    if surplus < 0:
        raise ValueError('The requested rank is below the rank of the unpadded lift')
    grafts = {(0, depth, side): 2 ** (rounds - depth - 2)
              for depth in range(1, rounds - 2) for side in range(2)}
    ordinary = {(0, rounds - 2, side): DetourPlan(None, (), (), None) for side in range(2)}
    base, blue, root, _, _, waves = subcubic_recursive_rank_certificate(
        rounds, 1, 2 * sum(grafts.values()) + 2, layered_detours=grafts,
        ordinary_detours=ordinary, fault_budget=fault_budget, compact=compact
    )
    if three_connected:
        graph, blue, white_caps = cubic_leaf_cycle_lift(base, blue, surplus)
    else:
        capped, blue, white_caps = cap_subcubic_leaves(base, blue, surplus)
        graph, _, _ = subcubic_synchronous_lift(capped, cubic=True)
    order = len(graph) // 2
    capped_waves = [list(wave) for wave in waves] + [[]]
    for index, wave in enumerate(waves, 1):
        capped_waves[index].extend(white_caps[v] for v in wave if v in white_caps)
    lifted_waves = [tuple(copy * order + v for copy in range(2) for v in wave)
                    for wave in capped_waves]
    return graph, copy_mask(blue, order, 2) ^ (root << order), root, lifted_waves


def subcubic_nine_round_chain(losses):
    block, block_blue, size, entry, tail = SINGLE['subcubic_two_round_block']()
    seed, first, prefix = range(losses * size, losses * size + 3)
    edges, blue, deliberately_lost = [(seed, first), (first, prefix)], [seed], []
    order = prefix + 1
    for copy in range(losses):
        start = copy * size
        deliberately_lost.append(start)
        edges.extend((start + a, start + b) for a, b in block)
        blue.extend(start + v for v in block_blue)
        edges.extend(((order, prefix), (order, start + entry)))
        blue.append(order)
        order += 1
        prefix = start + tail
    return edges, blue, deliberately_lost, seed, prefix, order


def subcubic_two_round_certificate(losses):
    edges, blue, lost, _, _, order = subcubic_nine_round_chain(losses)
    return adjacency(order, edges), mask(blue), mask(lost)


def cubic_fourteen_round_certificate(cycle_rank=16):
    """Join two cubic six-round blocks after a common two-round start."""
    if cycle_rank < 16:
        raise ValueError('This construction requires cycle rank at least sixteen')
    edges = [(0, 1), (0, 2), (0, 8), (1, 3), (1, 4), (2, 5), (2, 9), (3, 8),
             (3, 10), (4, 7), (4, 12), (5, 11), (5, 28), (6, 9), (6, 11), (6, 28),
             (7, 10), (7, 11), (8, 29), (9, 15), (10, 26), (12, 13), (12, 14),
             (13, 14), (13, 15), (14, 25), (15, 29), (16, 17), (16, 18), (16, 24),
             (17, 19), (17, 20), (18, 21), (18, 25), (19, 24), (19, 26), (20, 23),
             (20, 28), (21, 22), (21, 27), (22, 25), (22, 27), (23, 26), (23, 27), (24, 29)]
    order = 2 * (cycle_rank - 1)
    SINGLE['expand_cubic_edge_pair'](edges, 30, (8, 29), (10, 26), cycle_rank - 16)
    blue = mask((0, 1, 8, 9, 10, 11, 14, 15, 16, 17, 24, 25, 26, 27, 28, 29, *range(30, order)))
    return adjacency(order, edges), blue, mask((0, 16))


def cubic_two_round_chain_certificate(losses, cycle_rank=None):
    """Use one designated loss per block in a three-connected cubic chain."""
    if losses < 1:
        raise ValueError('The chain requires at least one designated loss')
    minimum_rank = 9 if losses == 1 else 8 * losses + 2
    rank = minimum_rank if cycle_rank is None else cycle_rank
    if rank < minimum_rank:
        raise ValueError('The requested rank is below the rank of this construction')

    graph, blue, _ = SINGLE['cubic_eight_round_certificate']()
    edges = [(v, w) for v, row in enumerate(graph) for w in members(row) if v < w]
    lost = 1
    waves = [(13,), (12,), (4,), (7,), (3,), (0,), (2,), (5, 6)]
    padding = ((8, 14), (9, 15))
    if losses > 1:
        block_edges = [(v, w) for v, w in edges if w < 12]
        block_blue = blue & ((1 << 12) - 1)
        SINGLE['expand_cubic_edge_pair'](edges, 16, *padding, 1)
        graph = adjacency(18, edges)
        blue |= mask((16, 17))
        hub, tail = 16, (5, 6)
        prism = SINGLE['cubic_padding_graph'](6)
        for _ in range(losses - 1):
            graph, labels = SINGLE['replace_cubic_vertex'](graph, hub, prism)
            blue |= mask(labels[1:])
            # Port 1 stays in the blue set. Vertex 4 becomes the relay.
            hub, relay = labels[1], labels[4]
            start = len(graph)
            edges = [(v, w) for v, row in enumerate(graph) for w in members(row)
                     if v < w and relay not in (v, w) and (v, w) != tail]
            edges.extend(((tail[0], relay), (tail[1], relay), (relay, start + 4)))
            edges.extend(zip(members(graph[relay]), (start + 8, start + 9, start + 10)))
            edges.extend((start + v, start + w) for v, w in block_edges)
            graph = adjacency(start + 12, edges)
            blue |= block_blue << start
            lost |= 1 << start
            tail = (start + 5, start + 6)
            waves.extend(tuple(start + v for v in wave) for wave in ((4,), (7,), (3,), (0,), (2,), (5, 6)))
        contact = next(w for w in members(graph[8]) if w >= 16)
        padding = ((8, contact), (10, 15))
    order = 2 * (rank - 1)
    SINGLE['expand_cubic_edge_pair'](edges, len(graph), *padding, rank - minimum_rank)
    blue |= mask(range(len(graph), order))
    return adjacency(order, edges), blue, lost, waves


def compact_cubic_two_round_chain_certificate(losses, cycle_rank=None):
    """Join the blue ports around a cycle while relays delimit the delayed waves."""
    if losses < 1:
        raise ValueError('The chain requires at least one designated loss')
    order = 13 * losses + 3 + (losses % 2 == 0)
    minimum_rank = order // 2 + 1
    rank = minimum_rank if cycle_rank is None else cycle_rank
    if rank < minimum_rank:
        raise ValueError('The requested rank is below the rank of this construction')
    if losses == 1:
        return cubic_two_round_chain_certificate(losses, rank)

    first, blue, _ = SINGLE['cubic_eight_round_certificate']()
    original_edges = [(v, w) for v, row in enumerate(first) for w in members(row) if v < w]
    block_edges = [(v, w) for v, w in original_edges if w < 12 and (v, w) != (5, 6)]
    block_blue = blue & ((1 << 12) - 1)
    edges = [(v, w) for v, w in original_edges if (v, w) not in ((5, 6), (8, 14), (10, 15))]
    edges.extend(((5, 16), (6, 16)))
    blue |= 1 << 16
    lost = 1
    waves = [(13,), (12,), (4,), (7,), (3,), (0,), (2,), (5, 6)]
    starts = range(17, 17 + 13 * (losses - 1), 13)
    relay, cycle_port = 16, 14
    for start in starts:
        edges.extend(((relay, start + 4), (cycle_port, start + 9)))
        edges.extend((start + v, start + w) for v, w in block_edges)
        blue |= block_blue << start
        lost |= 1 << start
        waves.extend(tuple(start + v for v in wave) for wave in ((4,), (7,), (3,), (0,), (2,), (5, 6)))
        if start == starts[-1]:
            edges.append((start + 5, start + 6))
        else:
            relay = start + 12
            edges.extend(((start + 5, relay), (start + 6, relay)))
            blue |= 1 << relay
        cycle_port = start + 10
    edges.append((10, cycle_port))

    spare_ports = [start + 8 for start in starts]
    if losses % 2:
        first_contact = spare_ports[0]
        edges.extend(((8, first_contact), (15, spare_ports[1])))
        spare_ports = spare_ports[2:]
    else:
        first_contact = order - 1
        edges.extend(((8, first_contact), (15, first_contact), (spare_ports[0], first_contact)))
        blue |= 1 << first_contact
        spare_ports = spare_ports[1:]
    edges.extend(zip(spare_ports[::2], spare_ports[1::2]))

    SINGLE['expand_cubic_edge_pair'](edges, order, (8, first_contact), (10, cycle_port), rank - minimum_rank)
    final_order = 2 * (rank - 1)
    blue |= mask(range(order, final_order))
    return adjacency(final_order, edges), blue, lost, waves


def check_compact_cubic_chain_contacts(original_edges, original_blue):
    """Replay the affected blocks for each type of blue contact."""
    opening = (16, [(v, w) for v, w in original_edges
                    if (v, w) not in ((5, 6), (8, 14), (10, 15))], original_blue)
    block_blue = original_blue & ((1 << 12) - 1)
    later = [(12, [(v, w) for v, w in original_edges
                   if w < 12 and (keep_tail or (v, w) != (5, 6))], block_blue)
             for keep_tail in (False, True)]
    for layout, seeds in ((opening, (1, 9, 11)), *((block, (1, 11)) for block in later)):
        order, edges, blue = layout
        graph = adjacency(order, edges)
        for seed in seeds:
            if completion_time(graph, blue ^ (1 << seed)) > order:
                raise AssertionError(('compact chain internal loss', layout, seed))

    contacts = [(opening, a, right, b) for right in later
                for a, b in ((14, 9), (10, 10), (8, 8), (15, 8))]
    contacts.extend((left, a, right, b) for left in later for right in later
                    for a, b in ((10, 9), (8, 8)))
    for (order, left_edges, left_blue), a, (size, right_edges, right_blue), b in contacts:
        edges = [*left_edges, *((order + v, order + w) for v, w in right_edges), (a, order + b)]
        graph = adjacency(order + size, edges)
        blue = left_blue | (right_blue << order)
        for seed in (a, order + b):
            if completion_time(graph, blue ^ (1 << seed)) > len(graph):
                raise AssertionError(('compact chain port loss', a, b, seed))

    for size, edges, blue in later:
        hub = 16 + size
        graph = adjacency(hub + 1, [*opening[1], *((16 + v, 16 + w) for v, w in edges),
                                    (8, hub), (15, hub), (24, hub)])
        if completion_time(graph, original_blue | (blue << 16)) > len(graph):
            raise AssertionError('compact chain hub loss')


def check_cubic_chain_loss_patterns(certificate, losses, rank=None):
    graph, blue, designated, _ = certificate(losses, rank)
    seeds = tuple(members(designated))
    for count in range(losses + 1):
        times = []
        for subset in combinations(seeds, count):
            omitted = mask(subset)
            longest = max((sum(1 for _ in run) for failed, run in
                           groupby(bool(omitted & (1 << seed)) for seed in seeds) if failed), default=0)
            actual = completion_time(graph, blue ^ omitted)
            if actual != 2 + 6 * longest:
                raise AssertionError(('cubic chain loss pattern', losses, subset, actual))
            times.append(actual)
        gaps = losses - count + 1
        balanced = (count + gaps - 1) // gaps
        if min(times) != 2 + 6 * balanced or max(times) != 2 + 6 * count:
            raise AssertionError(('cubic chain pattern extremes', losses, count))


def cubic_killing_pairs(graph, blue):
    """Replay all two-seed deletions, with one bit per deletion in each vertex state."""
    seeds = tuple(members(blue))
    pairs = list(combinations(seeds, 2))
    all_cases = (1 << len(pairs)) - 1
    omitted = [0] * len(graph)
    for i, (a, b) in enumerate(pairs):
        case = 1 << i
        omitted[a] |= case
        omitted[b] |= case
    state = [0] * len(graph)
    for v in seeds:
        state[v] = all_cases ^ omitted[v]
    neighbors = [tuple(members(row)) for row in graph]
    while True:
        after = state.copy()
        for v, (a, b, c) in enumerate(neighbors):
            after[a] |= state[v] & state[b] & state[c]
            after[b] |= state[v] & state[a] & state[c]
            after[c] |= state[v] & state[a] & state[b]
        if after == state:
            break
        state = after
    successful = all_cases
    for cases in state:
        successful &= cases
    return {pairs[i] for i in members(all_cases ^ successful)}


def compact_cubic_chain_killing_pair_formula(losses, padded):
    """List the predicted labelled pairs for a compact chain with at least two blocks."""
    starts = range(17, 17 + 13 * (losses - 1), 13)
    pairs = {(0, 1), (0, 9)}
    pairs.update((start, start + 1) for start in starts)
    pairs.update((left, right + 9) for left, right in pairwise(starts))
    spare_pairs = starts[2 if losses % 2 else 1:]
    pairs.update((left + 1, right + 8) for left, right in zip(spare_pairs[::2], spare_pairs[1::2]))
    if not padded:
        pairs.update(((1, 25), (9, 25)) if losses % 2 else ((8, 15),))
    return pairs


def check_cubic_chain_root_forts(graph, blue, designated):
    for root in members(designated):
        fort = mask(root + offset for offset in (0, 1, 2, 3, 5, 6, 7))
        if (blue & fort != mask((root, root + 1))
                or any((row & fort).bit_count() == 1 for v, row in enumerate(graph) if not fort & (1 << v))):
            raise AssertionError(('cubic chain root fort', root))


def check_compact_cubic_chain_killing_pairs():
    tested = 0
    for losses in range(2, 32):
        minimum_rank = (13 * losses + 4) // 2 + 1
        for extra in range(3):
            graph, blue, lost, _ = compact_cubic_two_round_chain_certificate(losses, minimum_rank + extra)
            check_cubic_chain_root_forts(graph, blue, lost)
            actual = cubic_killing_pairs(graph, blue)
            expected = compact_cubic_chain_killing_pair_formula(losses, extra > 0)
            if actual != expected:
                raise AssertionError(('compact cubic chain killing pairs', losses, extra,
                                      sorted(actual - expected), sorted(expected - actual)))
            tested += blue.bit_count() * (blue.bit_count() - 1) // 2
    return tested


def bipartite_cubic_chain_certificate(blocks, cycle_rank=None):
    """Lift the compact chain and add two blue vertices for an even rank."""
    even_rank = cycle_rank is not None and cycle_rank % 2 == 0
    base_rank = None if cycle_rank is None else (cycle_rank + 1) // 2
    if blocks == 1:
        base_rank = 10 if base_rank is None else base_rank
        if base_rank < 10:
            raise ValueError('The one-block cover needs at least one padding column')
    graph, blue, lost, waves = compact_cubic_two_round_chain_certificate(blocks, base_rank)
    edges = [(v, w) for v, row in enumerate(graph) for w in members(row) if v < w]
    if even_rank:
        anchor = 9
        contact = 15 if blocks > 1 else next(v for v in members(graph[anchor]) if v >= 16)
        edges.remove((anchor, contact))
    lifted_edges = [(2 * v + sheet, 2 * w + 1 - sheet) for v, w in edges for sheet in (0, 1)]
    order = 2 * len(graph)
    seeds = mask(2 * v + sheet for v in members(blue) for sheet in (0, 1))
    if even_rank:
        x, y = order, order + 1
        lifted_edges.extend(((2 * anchor, y), (2 * contact, y),
                             (2 * anchor + 1, x), (2 * contact + 1, x), (x, y)))
        seeds |= mask((x, y))
        order += 2
    deleted = mask(2 * v + sheet for v in members(lost) for sheet in (0, 1))
    lifted_waves = [tuple(2 * v + sheet for v in wave for sheet in (0, 1)) for wave in waves]
    return adjacency(order, lifted_edges), seeds, deleted, lifted_waves


def cyclic_cubic_chain_lift(certificate, sheets, *, reversed_edge=None):
    graph, blue, lost, waves = certificate

    def copies(vertices):
        return (sheets * v + sheet for v in vertices for sheet in range(sheets))

    base_edges = ((v, w, -1 if (v, w) == reversed_edge else 1)
                  for v, row in enumerate(graph) for w in members(row) if v < w)
    lifted = adjacency(sheets * len(graph), ((sheets * v + sheet, sheets * w + (sheet + shift) % sheets)
                                            for v, w, shift in base_edges for sheet in range(sheets)))
    return lifted, mask(copies(members(blue))), mask(copies(members(lost))), [tuple(copies(wave)) for wave in waves]


def three_sheet_cubic_chain_certificate(blocks, cycle_rank=None):
    """Lift each increasing base edge by the shift of one modulo three."""
    if cycle_rank is not None and cycle_rank % 3 != 1:
        raise ValueError('The three-sheet cover has cycle rank one modulo three')
    base_rank = None if cycle_rank is None else (cycle_rank + 2) // 3
    if blocks == 1:
        base_rank = 11 if base_rank is None else base_rank
        if base_rank < 11:
            raise ValueError('The one-block three-sheet cover needs two padding columns')
    return cyclic_cubic_chain_lift(compact_cubic_two_round_chain_certificate(blocks, base_rank), 3)


PRISM_RANK_EDGE = (9, 17)


def four_sheet_cubic_chain_certificate(blocks, cycle_rank=None):
    """Lift the prism chain and add up to three columns at its opening."""
    if blocks < 2:
        raise ValueError('The four-sheet construction needs at least two blocks')
    minimum_rank = 32 * blocks + 5
    rank = minimum_rank + 4 if cycle_rank is None else cycle_rank
    if rank < minimum_rank:
        raise ValueError('The four-sheet construction requires cycle rank at least 32 * blocks + 5')
    base_rank, extra = divmod(rank + 3, 4)
    reversed_edge = (0, 1) if rank - extra == minimum_rank else None
    base = cubic_two_round_chain_certificate(blocks, base_rank)
    cover = cyclic_cubic_chain_lift(base, 4, reversed_edge=reversed_edge)
    return bipartite_prism_rank_ladder(cover, 4, extra)


def bipartite_prism_rank_ladder(certificate, sheets, extra):
    if not extra:
        return certificate

    graph, blue, lost, waves = certificate
    a, b = PRISM_RANK_EDGE
    a0, a2, b1, b3 = sheets * a, sheets * a + 2, sheets * b + 1, sheets * b + 3
    removed = {(a0, b1), (a2, b3)}
    edges = [(v, w) for v, row in enumerate(graph) for w in members(row) if v < w and (v, w) not in removed]
    order = len(graph)
    upper = [order + 2 * i + (1 - i % 2) for i in range(extra)]
    lower = [v ^ 1 for v in upper]
    edges.extend(zip(upper, lower))
    edges.extend(pairwise(upper))
    edges.extend(pairwise(lower))
    upper_end, lower_end = (a2, b1) if extra % 2 else (b1, a2)
    edges.extend(((a0, upper[0]), (b3, lower[0]), (upper_end, upper[-1]), (lower_end, lower[-1])))
    final_order = order + 2 * extra
    return adjacency(final_order, edges), blue | mask(range(order, final_order)), lost, waves


def five_sheet_cubic_chain_certificate(blocks, cycle_rank=None):
    """Lift the prism chain to five sheets and fill the ranks between covers."""
    if blocks < 2:
        raise ValueError('The five-sheet construction needs at least two blocks')
    minimum_rank = 40 * blocks + 6
    rank = minimum_rank if cycle_rank is None else cycle_rank
    if rank < minimum_rank:
        raise ValueError('The five-sheet construction requires cycle rank at least 40 * blocks + 6')
    base_rank, extra = divmod(rank + 4, 5)
    reversed_edge = (0, 1) if rank - extra == minimum_rank else None
    base = cubic_two_round_chain_certificate(blocks, base_rank)
    graph, blue, lost, waves = cyclic_cubic_chain_lift(base, 5, reversed_edge=reversed_edge)
    if not extra:
        return graph, blue, lost, waves

    a, b = PRISM_RANK_EDGE
    edges = [(v, w) for v, row in enumerate(graph) for w in members(row) if v < w]
    order = len(graph)
    SINGLE['expand_cubic_edge_pair'](edges, order, (5 * a, 5 * b + 1), (5 * a + 2, 5 * b + 3), extra)
    final_order = order + 2 * extra
    return adjacency(final_order, edges), blue | mask(range(order, final_order)), lost, waves


def cubic_loss_deadlines(graph, blue, budget):
    """Compute maximum parallel times for each loss budget, with None for a stall."""
    def minimal(terms):
        if 0 in terms:
            return (0,)
        result = []
        for term in terms:
            submask = (term - 1) & term
            while submask and submask not in terms:
                submask = (submask - 1) & term
            if not submask:
                result.append(term)
        return tuple(sorted(result))

    @lru_cache(maxsize=32768)
    def conjoin(left, right):
        if left == (0,):
            return right
        if right == (0,):
            return left
        return minimal({a | b for a in left for b in right if (a | b).bit_count() <= budget})

    @lru_cache(maxsize=32768)
    def disjoin(left, middle, right):
        return minimal(set(chain(left, middle, right)))

    neighbors = [tuple(members(row)) for row in graph]
    sources = [[(u, *(w for w in neighbors[u] if w != v)) for u in row]
               for v, row in enumerate(neighbors)]
    state = [((1 << v,) if budget else ()) if blue & (1 << v) else (0,) for v in range(len(graph))]
    deadlines = [None] * (budget + 1)
    for round_number in range(len(graph) + 1):
        first_white = min((term.bit_count() for term in chain.from_iterable(state)), default=budget + 1)
        for size in range(first_white):
            if deadlines[size] is None:
                deadlines[size] = round_number
        if first_white > budget:
            break
        after = []
        for still_white, candidates in zip(state, sources):
            for u, a, b in candidates:
                if not still_white:
                    break
                # A force from u is blocked if any of u, a or b is white.
                still_white = conjoin(still_white, disjoin(state[u], state[a], state[b]))
            after.append(still_white)
        if after == state:
            break
        state = after
    return tuple(deadlines)


def check_bipartite_cubic_chain_deadlines():
    cases = 0
    for blocks in range(1, 28):
        minimum_base_rank = (13 * blocks + 4) // 2 + 1
        for padding in range(int(blocks == 1), 6):
            odd_rank = 2 * (minimum_base_rank + padding) - 1
            if blocks >= 4:
                first_spare = 17 + 13 * (1 + blocks % 2)
                next_start = first_spare + 13
                triple = mask((2 * (first_spare + 8), 2 * next_start + 1, 2 * (next_start + 1) + 1))
                triple_time = 11
            elif blocks == 3 and padding == 0:
                triple = mask((16, 35, 37))
                triple_time = 11
            else:
                triple = mask((0, 1, 3))
                triple_time = 10
            for rank in (odd_rank, odd_rank + 1):
                graph, blue, lost, waves = bipartite_cubic_chain_certificate(blocks, rank)
                if (len(graph) // 2 + 1 != rank or len(waves) != 6 * blocks + 2 or lost.bit_count() != 2 * blocks
                        or any(row.bit_count() != 3 or any((v - w) % 2 == 0 for w in members(row))
                               for v, row in enumerate(graph))):
                    raise AssertionError(('bipartite chain metadata', blocks, rank))
                check_arrival_waves(graph, blue ^ lost, waves)
                deadlines = cubic_loss_deadlines(graph, blue, 3)
                if deadlines != (2, 5, 8, triple_time):
                    raise AssertionError(('bipartite chain loss deadlines', blocks, rank, deadlines))
                for actual_loss, expected in ((1, 5), (3, 8), (triple, triple_time)):
                    if completion_time(graph, blue ^ actual_loss) != expected:
                        raise AssertionError(('bipartite chain deadline witness', blocks, rank, actual_loss))
                cases += 1
    return cases


def cubic_two_fault_gap_certificate(cycle_rank=10):
    """Give a two-fault-tolerant cubic witness with unrestricted time nine."""
    if cycle_rank < 10 or cycle_rank == 11:
        raise ValueError('This layout is available at rank ten and from rank twelve')
    edges = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 4), (2, 5), (3, 4), (3, 6),
             (4, 7), (5, 6), (5, 8), (6, 9), (7, 10), (7, 11), (8, 10), (8, 12),
             (9, 13), (9, 14), (10, 13), (11, 12), (11, 15), (12, 16), (13, 14),
             (14, 17), (15, 16), (15, 17), (16, 17)]
    order = 2 * (cycle_rank - 1)
    SINGLE['expand_cubic_edge_pair'](edges, 18, (5, 6), (11, 12), cycle_rank - 10)
    blue = mask((2, 4, 5, 6, 9, 11, 12, 13, 15, 16, *range(18, order)))
    return adjacency(order, edges), blue, mask((9, 15)), mask((2, 15, 16))


def subcubic_mixed_rank_certificate(losses, cycle_rank):
    large = min(losses, max(0, (cycle_rank - losses) // 3))
    small = min(losses - large, cycle_rank - 4 * large)
    edges, blue, lost, seed, endpoint, order = subcubic_nine_round_chain(large)
    for block in range(losses - large):
        order, endpoint, _ = append_subcubic_arm_block(edges, blue, lost, endpoint, order,
                                                       block < small)
    padded = append_subcubic_blue_cycles(edges, seed, order, cycle_rank - 4 * large - small,
                                          losses)
    blue.extend(range(order, padded))
    return adjacency(padded, edges), mask(blue), mask(lost)


def two_round_certificate(degree, losses):
    block, block_blue, size, targets, tail, splice = SINGLE['quadratic_degree_block'](
        degree, continue_at_tail=True
    )
    seed, first, prefix = range(losses * size, losses * size + 3)
    edges, blue, deliberately_lost = [(seed, first), (first, prefix)], [seed], []
    order = prefix + 1
    for copy in range(losses):
        start = copy * size
        deliberately_lost.append(start)
        edges.extend((start + a, start + b) for a, b in block)
        blue.extend(start + v for v in block_blue)
        chain = [start + v for v in targets]
        junction = None if splice is None else tuple(start + v for v in splice)
        for left, right in SINGLE['quadratic_relay_links'](prefix, chain, junction):
            edges.extend(((order, left), (order, right)))
            blue.append(order)
            order += 1
        prefix = start + tail
    graph, initial, support, paths = protect_seeds(
        degree, edges, blue, order, deliberately_lost, seed
    )
    return graph, initial, mask(deliberately_lost), support, paths


def check_connected(graph, degree):
    reached, frontier = 0, 1
    while frontier:
        reached |= frontier
        neighbors = 0
        for vertex in members(frontier):
            neighbors |= graph[vertex]
        frontier = neighbors & ~reached
    if reached.bit_count() != len(graph) or max(row.bit_count() for row in graph) != degree:
        raise AssertionError(('connectivity or degree', degree, len(graph)))


def check_all_losses(graph, blue, limit):
    seeds = list(members(blue))
    checked = 0
    for size in range(1, limit + 1):
        for deleted in combinations(seeds, size):
            if completion_time(graph, blue ^ mask(deleted)) > len(graph):
                raise AssertionError(('loss failed', deleted))
            checked += 1
    return checked


def check_no_two_edge_cut(graph):
    without_edge = list(graph)
    for u, row in enumerate(graph):
        for offset in members(row >> (u + 1)):
            v = u + 1 + offset
            without_edge[u] ^= 1 << v
            without_edge[v] ^= 1 << u
            if graph_bridges(without_edge):
                raise AssertionError(('two-edge cut', u, v))
            without_edge[u] = graph[u]
            without_edge[v] = graph[v]


def check_robust_samples(graph, blue, slow, support, paths, degree, rounds, losses, *,
                         clique_support=True):
    check_connected(graph, degree)
    if completion_time(graph, blue) != rounds or completion_time(graph, blue ^ support) <= len(graph):
        raise AssertionError(('intact or killing time', degree, rounds, losses))
    support_time = max(completion_time(graph, blue ^ support ^ (1 << retained))
                       for retained in members(support))
    expected = rounds if clique_support and losses <= degree else max(rounds, losses)
    if support_time != expected:
        raise AssertionError(('restricted deadline', support_time, expected))
    if any(completion_time(graph, blue ^ (1 << lost)) != rounds for lost in members(support)):
        raise AssertionError(('single support loss deadline', degree, rounds, losses))

    # Exercise both clustered deletions and mixed failures across the private paths.
    seeds = list(members(blue))
    rng = Random(3157)
    checks = [slow, mask(paths[0][:losses]), mask(paths[-1][-losses:])]
    for path in (paths[0], paths[-1]):
        protected = graph[path[0]] ^ (1 << path[1])
        checks.append(protected | mask(path[:losses - 1]))
    checks.append(mask([*list(members(slow))[:losses // 2],
                        *list(members(support))[:losses - losses // 2]]))
    for _ in range(12):
        size = rng.randint(1, losses)
        checks.append(mask(rng.sample(seeds, size)))
    for deletion in checks:
        if completion_time(graph, blue ^ deletion) > len(graph):
            raise AssertionError(('sampled loss failed', degree, rounds, losses, deletion))
    return len(checks)


def check_ranked_one_round_example(graph, blue, slow, rank, expected):
    actual_rank = sum(row.bit_count() for row in graph) // 2 - len(graph) + 1
    intact, delayed, _ = check_cycle_rank_trace(graph, blue, slow, rank)
    if (intact, delayed, actual_rank) != (1, expected, rank):
        raise AssertionError(('ranked one-round delay', slow.bit_count(), rank,
                              delayed, expected, actual_rank))


def check_arrival_waves(graph, remaining_blue, additions):
    _, arrivals = trace(graph, remaining_blue)
    waves = [set() for _ in additions]
    for vertex, arrival in enumerate(arrivals):
        if arrival > 0:
            waves[arrival - 1].add(vertex)
    if waves != [set(vertices) for vertices in additions]:
        raise AssertionError('Arrival sequence differs from the certificate')


def main():
    exhaustive = sampled = 0
    check_branched_forest_extremizers()
    rank_extremizers = {(2, rank): time for rank, time in
                        enumerate((12, 15, 18, 18, 19, 20, 20, 23, 23))}
    rank_extremizers.update({(2, 100): 161, (2, 101): 164,
                             (3, 3): 26, (3, 4): 26, (3, 5): 27, (3, 6): 28,
                             (3, 7): 28, (3, 8): 31, (3, 9): 31,
                             (4, 7): 36, (4, 8): 36, (4, 11): 42, (5, 35): 83})
    observed_extremizers = {}
    low_rank_cases = ((2, 1, 0, 4), (2, 1, 1, 4), (2, 1, 2, 4),
                      (2, 1, 3, 4), (2, 1, 4, 4), (2, 1, 6, 5), (2, 1, 7, 6),
                      (2, 1, 15, 10), (2, 1, 16, 10), (2, 1, 35, 20), (2, 1, 100, 52),
                      (2, 2, 0, 4), (2, 2, 1, 4), (2, 2, 2, 4), (2, 2, 3, 4), (2, 2, 4, 4),
                      (2, 3, 3, 4), (2, 3, 4, 4), (2, 3, 5, 4),
                      (2, 4, 3, 4), (2, 4, 4, 4),
                      (3, 3, 2, 4), (3, 2, 7, 5), (4, 2, 2, 4),
                      (7, 5, 3, 4), (9, 3, 5, 4), (8, 3, 16, 7))
    for t, k, rank, cap in low_rank_cases:
        graph, blue, slow, support, paths, additions = low_rank_recovery_certificate(
            t, k, rank, degree=cap
        )
        degree = max(row.bit_count() for row in graph)
        if degree > cap:
            raise AssertionError(('low-rank degree cap', t, k, rank, cap, degree))
        sampled += check_robust_samples(graph, blue, slow, support, paths, degree, t, k,
                                        clique_support=False)
        actual_rank = sum(row.bit_count() for row in graph) // 2 - len(graph) + 1
        blocks = min(k, rank)
        extra = min((rank - blocks) // 2, blocks * (cap - 3))
        expected = t + k * (2 * t + 1) + blocks * (2 * t - 1) + extra
        intact, delayed, _ = check_cycle_rank_trace(graph, blue, slow, rank)
        if (intact, delayed, actual_rank) != (t, expected, rank):
            raise AssertionError(('low-rank recovery', t, k, rank, delayed, actual_rank))
        check_arrival_waves(graph, blue ^ slow, additions)
        if t == 2 and (k, rank) in rank_extremizers:
            observed_extremizers[k, rank] = delayed
        if (t, k, rank) in ((2, 1, 2), (2, 2, 1)):
            exhaustive += check_all_losses(graph, blue, k)
        print('Low-rank recovery:', t, k, rank, len(graph), delayed)

    deep_cases = ((3, 1, 0, 4), (3, 1, 1, 4), (3, 1, 2, 4), (3, 1, 4, 5),
                  (3, 2, 1, 4), (3, 2, 6, 6), (4, 2, 7, 6), (6, 1, 9, 12),
                  (5, 3, 15, 7), (4, 3, 17, 5))
    for t, k, rank, cap in deep_cases:
        graph, blue, slow, support, paths, additions = deep_detour_recovery_certificate(t, k, rank, cap)
        degree = max(row.bit_count() for row in graph)
        if degree > cap:
            raise AssertionError(('deep-detour degree cap', t, k, rank, cap, degree))
        sampled += check_robust_samples(graph, blue, slow, support, paths, degree, t, k,
                                        clique_support=False)
        actual_rank = sum(row.bit_count() for row in graph) // 2 - len(graph) + 1
        shallow = min(k, rank)
        deep = min(rank - shallow, shallow * (cap - 3))
        expected = t + k * (2 * t + 1) + shallow * (2 * t - 1) + deep * (2 * t - 3)
        intact, delayed, _ = check_cycle_rank_trace(graph, blue, slow, rank)
        if (intact, delayed, actual_rank) != (t, expected, rank):
            raise AssertionError(('deep-detour recovery', t, k, rank, delayed, actual_rank))
        check_arrival_waves(graph, blue ^ slow, additions)
        if (t, k, rank) == (3, 1, 2):
            exhaustive += check_all_losses(graph, blue, k)
        print('Deep-detour recovery:', t, k, rank, cap, len(graph), delayed)

    shared_cases = ((2, 2, 1, 0), (2, 2, 2, 1), (2, 2, 5, 2), (2, 2, 6, 2),
                    (2, 2, 7, 2), (2, 2, 8, 2),
                    (2, 2, 100, 2), (2, 2, 101, 2),
                    (2, 3, 6, 3), (2, 3, 7, 3), (2, 3, 8, 3), (2, 3, 9, 3),
                    (2, 4, 7, 4), (2, 4, 8, 4), (2, 4, 11, 4), (2, 5, 35, 5),
                    (3, 3, 23, 0), (7, 4, 46, 0))
    for t, k, rank, detours in shared_cases:
        graph, blue, slow, support, paths, additions, degree = shared_center_recovery_certificate(
            t, k, rank, detours=detours
        )
        sampled += check_robust_samples(graph, blue, slow, support, paths, degree, t, k,
                                        clique_support=False)
        intact, delayed, _ = check_cycle_rank_trace(graph, blue, slow, rank)
        actual_rank = sum(row.bit_count() for row in graph) // 2 - len(graph) + 1
        centers = (rank - detours + 1) // 2
        expected = t + (2 * t - 1) * (centers + detours) + 2 * t + 2 + (k - 2) * (2 * t + 1)
        if (intact, delayed, actual_rank) != (t, expected, rank):
            raise AssertionError(('shared-center recovery', t, k, rank, delayed, actual_rank))
        check_arrival_waves(graph, blue ^ slow, additions)
        if t == 2 and (k, rank) in rank_extremizers:
            observed_extremizers[k, rank] = max(observed_extremizers.get((k, rank), 0), delayed)
        if (t, k, rank) == (2, 2, 1):
            exhaustive += check_all_losses(graph, blue, k)
        print('Shared-center recovery:', t, k, rank, detours, len(graph), delayed)

    if observed_extremizers != rank_extremizers:
        raise AssertionError(('two-round rank extrema', observed_extremizers, rank_extremizers))

    for k, rank in ((1, 1), (1, 2), (1, 3), (2, 1), (2, 2), (2, 3), (2, 4), (3, 1),
                    (3, 2), (3, 3), (3, 4), (3, 5), (4, 3), (4, 4), (4, 5), (4, 6),
                    (5, 1), (5, 3), (5, 5), (7, 7), (7, 8), (7, 9)):
        graph, blue, slow, support, paths, waves = subcubic_low_rank_certificate(k, rank)
        sampled += check_robust_samples(graph, blue, slow, support, paths, 3, 2, k,
                                        clique_support=False)
        intact, delayed, _ = check_cycle_rank_trace(graph, blue, slow, rank)
        actual_rank = sum(row.bit_count() for row in graph) // 2 - len(graph) + 1
        if (intact, delayed, actual_rank) != (2, 2 + 5 * k + min(rank, k), rank):
            raise AssertionError(('subcubic low-rank recovery', k, rank, intact, delayed, actual_rank))
        check_arrival_waves(graph, blue ^ slow, waves)
        if k <= 2:
            exhaustive += check_all_losses(graph, blue, k)
        print('Subcubic low-rank recovery:', k, rank, len(graph), delayed)

    for k, rank, expected in ((1, 4, 9), (2, 5, 15), (2, 7, 15), (2, 8, 16), (3, 6, 21),
                              (3, 9, 22), (3, 12, 23), (4, 7, 27), (4, 25, 30), (7, 10, 45)):
        graph, blue, slow = subcubic_mixed_rank_certificate(k, rank)
        check_connected(graph, 3)
        intact, delayed, _ = check_cycle_rank_trace(graph, blue, slow, rank)
        actual_rank = sum(row.bit_count() for row in graph) // 2 - len(graph) + 1
        if (slow.bit_count(), intact, delayed, actual_rank) != (k, 2, expected, rank):
            raise AssertionError(('subcubic mixed-rank recovery', k, rank, intact, delayed, actual_rank))
        print('Subcubic mixed-rank recovery:', k, rank, len(graph), delayed)

    for t, k, rank, expected in ((3, 1, 1, 13), (3, 3, 3, 33), (4, 2, 2, 32),
                                 (4, 2, 4, 32), (5, 3, 1, 45), (6, 5, 3, 98),
                                 (8, 2, 1, 55)):
        graph, blue, slow, support, paths, waves = subcubic_low_rank_certificate(k, rank, rounds=t)
        sampled += check_robust_samples(graph, blue, slow, support, paths, 3, t, k,
                                        clique_support=False)
        intact, delayed, _ = check_cycle_rank_trace(graph, blue, slow, rank)
        actual_rank = sum(row.bit_count() for row in graph) // 2 - len(graph) + 1
        if (intact, delayed, actual_rank) != (t, expected, rank):
            raise AssertionError(('subcubic long recovery', t, k, rank, intact, delayed, actual_rank))
        check_arrival_waves(graph, blue ^ slow, waves)
        if (t, k) == (3, 1):
            exhaustive += check_all_losses(graph, blue, k)
        print('Subcubic long recovery:', t, k, rank, len(graph), delayed)

    for t, k, rank, expected in ((3, 1, 2, 14), (3, 2, 3, 24), (3, 2, 6, 27), (3, 3, 4, 34),
                                 (4, 1, 2, 21), (4, 1, 3, 24), (4, 2, 3, 35),
                                 (4, 1, 6, 27), (5, 1, 3, 33), (5, 1, 8, 44), (5, 1, 12, 48),
                                 (6, 1, 3, 42), (6, 2, 4, 64), (6, 2, 5, 71), (6, 2, 47, 166),
                                 (7, 2, 5, 86), (8, 3, 5, 120), (8, 2, 6, 112), (8, 1, 80, 281),
                                 (9, 3, 7, 163), (10, 3, 8, 199), (11, 3, 8, 222),
                                 (12, 3, 9, 264), (13, 3, 9, 289),
                                 (12, 1, 4, 113), (16, 1, 5, 182), (20, 1, 6, 267),
                                 (16, 2, 7, 273), (20, 2, 8, 382),
                                 (8, 1, 4, 69), (12, 1, 5, 130), (16, 1, 6, 207),
                                 (12, 2, 7, 197), (16, 2, 8, 298)):
        graph, blue, slow, support, paths, waves = subcubic_recursive_rank_certificate(t, k, rank)
        sampled += check_robust_samples(graph, blue, slow, support, paths, 3, t, k,
                                        clique_support=False)
        intact, delayed, _ = check_cycle_rank_trace(graph, blue, slow, rank)
        actual_rank = sum(row.bit_count() for row in graph) // 2 - len(graph) + 1
        if (intact, delayed, actual_rank) != (t, expected, rank):
            raise AssertionError(('subcubic recursive recovery', t, k, rank, intact, delayed, actual_rank))
        check_arrival_waves(graph, blue ^ slow, waves)
        if (t, k, rank) == (4, 2, 3):
            exhaustive += check_all_losses(graph, blue, k)
        print('Subcubic recursive recovery:', t, k, rank, len(graph), delayed)

    for t, k, rank, expected, gain in ((5, 1, 7, 44, 1), (5, 1, 12, 49, 1),
                                       (10, 2, 14, 248, 2), (10, 2, 24, 358, 2),
                                       (21, 1, 7, 316, 1), (37, 2, 13, 1073, 1),
                                       (27, 1, 8, 463, 1), (42, 2, 14, 1304, 2),
                                       (51, 1, 12, 1291, 1),
                                       (12, 3, 27, 555, 3), (7, 1, 44, 157, 2),
                                       (8, 1, 44, 248, 3)):
        baseline, baseline_blue, baseline_loss, _, _, _ = subcubic_recursive_rank_certificate(
            t, k, rank
        )
        graph, blue, slow, support, paths, waves = subcubic_recursive_rank_certificate(
            t, k, rank, splice_centers=True
        )
        sampled += check_robust_samples(graph, blue, slow, support, paths, 3, t, k,
                                        clique_support=False)
        intact, delayed, _ = check_cycle_rank_trace(graph, blue, slow, rank)
        actual_rank = sum(row.bit_count() for row in graph) // 2 - len(graph) + 1
        actual_gain = delayed - completion_time(baseline, baseline_blue ^ baseline_loss)
        if (intact, delayed, actual_rank, actual_gain) != (t, expected, rank, gain):
            raise AssertionError(('subcubic center splice', t, k, rank, intact, delayed,
                                  actual_rank, actual_gain))
        check_arrival_waves(graph, blue ^ slow, waves)
        if (t, k, rank) == (5, 1, 7):
            exhaustive += check_all_losses(graph, blue, k)
        print('Subcubic center splice:', t, k, rank, len(graph), delayed, 'gain:', actual_gain)

    for t, k, rank, expected, gain in ((5, 1, 13, 49, 0), (6, 1, 13, 78, 1),
                                       (6, 1, 23, 89, 2), (7, 2, 25, 203, 1),
                                       (8, 1, 46, 258, 8), (9, 1, 100, 499, 30)):
        _, _, _, _, _, previous_waves = subcubic_recursive_rank_certificate(
            t, k, rank, splice_centers=True
        )
        graph, blue, slow, support, paths, waves = subcubic_recursive_rank_certificate(
            t, k, rank, splice_centers=True, splice_depth_limit=None
        )
        check_connected(graph, 3)
        intact, delayed, _ = check_cycle_rank_trace(graph, blue, slow, rank)
        actual_rank = sum(row.bit_count() for row in graph) // 2 - len(graph) + 1
        actual_gain = delayed - len(previous_waves)
        if (intact, delayed, actual_rank, actual_gain) != (t, expected, rank, gain):
            raise AssertionError(('subcubic repeated center splices', t, k, rank, intact,
                                  delayed, actual_rank, actual_gain))
        check_arrival_waves(graph, blue ^ slow, waves)
        if (t, k, rank) == (7, 2, 25):
            sampled += check_robust_samples(graph, blue, slow, support, paths, 3, t, k,
                                            clique_support=False)
        print('Subcubic repeated center splices:', t, k, rank, len(graph), delayed,
              'gain:', actual_gain)

    full_layered_block = {(0, depth, side): 2 ** (3 - depth) for depth in range(3)
                          for side in range(1 if depth == 0 else 2)}
    for t, k, rank, expected, grafts in (
        (3, 1, 2, 11, {(0, 0, 0): 1}),
        (5, 1, 42, 38, full_layered_block),
        (5, 2, 26, 68, {(0, 0, 0): 4, (0, 1, 0): 2, (1, 1, 1): 3}),
        (6, 2, 49, 116, {(0, 0, 0): 10, (0, 1, 0): 2, (1, 0, 0): 4}),
    ):
        graph, blue, slow, support, paths, waves = subcubic_recursive_rank_certificate(
            t, k, rank, splice_centers=True, splice_depth_limit=None, layered_detours=grafts
        )
        sampled += check_robust_samples(graph, blue, slow, support, paths, 3, t, k,
                                        clique_support=False)
        intact, delayed, _ = check_cycle_rank_trace(graph, blue, slow, rank)
        actual_rank = sum(row.bit_count() for row in graph) // 2 - len(graph) + 1
        if (intact, delayed, actual_rank) != (t, expected, rank):
            raise AssertionError(('subcubic layered detours', t, k, rank, intact,
                                  delayed, actual_rank))
        check_arrival_waves(graph, blue ^ slow, waves)
        if k == 1 and t == 3:
            exhaustive += check_all_losses(graph, blue, k)
        if k == 2:
            sources = [v for v in members(blue ^ slow)
                       if graph[v].bit_count() == 3 and not graph[v] & blue]
            if len(sources) != sum(grafts.values()):
                raise AssertionError('Layered terminal sources were not identified')
            failures = (mask(sources[:2]), mask(sources[-2:]),
                        (1 << sources[0]) | (slow & -slow))
            for deletion in failures:
                if completion_time(graph, blue ^ deletion) > len(graph):
                    raise AssertionError(('layered terminal source loss', deletion))
            sampled += len(failures)
        print('Subcubic layered detours:', t, k, rank, len(graph), delayed)

    for t, k, rank, expected in ((2, 1, 0, 7), (3, 2, 4, 25), (6, 1, 23, 89),
                                 (7, 2, 25, 203), (9, 1, 100, 499)):
        graph, blue, slow, _, _, waves = subcubic_optimized_rank_certificate(t, k, rank)
        check_connected(graph, 3)
        intact, delayed, _ = check_cycle_rank_trace(graph, blue, slow, rank)
        actual_rank = sum(row.bit_count() for row in graph) // 2 - len(graph) + 1
        if (intact, delayed, actual_rank) != (t, expected, rank):
            raise AssertionError(('subcubic optimized detours', t, k, rank, intact,
                                  delayed, actual_rank))
        check_arrival_waves(graph, blue ^ slow, waves)
        print('Subcubic optimized detours:', t, k, rank, delayed)

    for t, rank, expected, layered_count in ((13, 5345, 6654, 0), (13, 5346, 6655, 2009),
                                              (14, 6997, 12412, 0), (14, 6998, 12413, 2009)):
        time, _, layered = subcubic_rank_allocation(t, 1, rank)
        if (time, sum(layered.values())) != (expected, layered_count):
            raise AssertionError(('subcubic rank allocation', t, rank, time, layered))
        print('Subcubic rank allocation:', t, rank, time, 'layered targets:', layered_count)

    if subcubic_first_layered_rank(12, 3) is not None:
        raise AssertionError('Layering at deadline twelve cannot improve the ordinary optimum')
    for t, k, rank, expected in ((13, 2, 7251, 13296), (14, 2, 10555, 24811),
                                  (15, 1, 10082, 23161), (20, 3, 455151, 1574145),
                                  (60, 1, 10502302759001520, 36598365714832758)):
        threshold = subcubic_first_layered_rank(t, k)
        before = subcubic_rank_value(t, k, rank - 1)
        after = subcubic_rank_value(t, k, rank)
        if (threshold, before, after) != (rank, expected - 1, expected):
            raise AssertionError(('subcubic first layered rank', t, k, threshold, before, after))
        print('Subcubic first layered rank:', t, k, threshold, after)

    for n, cases in ((17, ((3, 4, 68676), (1, 1, 83441))),
                     (23, ((3, 4, 2787739), (1, 1, 3359543))),
                     (29, ((3, 4, 114003691), (1, 1, 138742935)))):
        t = n + 2
        _, _, ordinary, _ = subcubic_rank_model(t, 1)
        rank = sum(ordinary.values())
        baseline = subcubic_rank_value(t, 1, rank)
        for numerator, denominator, expected in cases:
            excess = numerator * 2 ** (n + 1) // denominator
            gain = subcubic_rank_value(t, 1, rank + excess) - baseline
            deficit = excess // 2 - gain
            if deficit != expected:
                raise AssertionError(('subcubic layered deficit', n, excess, deficit))
            print('Subcubic layered deficit:', n, excess, deficit)

    for t, k in ((13, 1), (14, 2), (28, 1), (60, 3)):
        _, _, ordinary, layers = subcubic_rank_model(t, k)
        activation, capacity = subcubic_layer_totals(layers)
        saturated_rank = k * (6 * 2 ** (t - 2) - 6864)
        if sum(ordinary.values()) + activation + 2 * capacity != saturated_rank:
            raise AssertionError(('subcubic saturation rank', t, k, saturated_rank))
        saturated = subcubic_rank_value(t, k, saturated_rank)
        for shortfall, expected in ((1, 1), (79, 40), (81, 40), (3519, 40)):
            actual = saturated - subcubic_rank_value(t, k, saturated_rank - shortfall)
            if actual != expected:
                raise AssertionError(('subcubic saturation plateau', t, k, shortfall, actual))
        print('Subcubic saturation plateau:', t, k, saturated_rank, saturated)

    for t, k in ((13, 2), (14, 1), (14, 4), (60, 4)):
        _, _, _, layers = subcubic_rank_model(t, k)
        activation, capacity = subcubic_layer_totals(layers)
        full_budget = activation + 2 * capacity
        count = k if t == 13 else 2 * k
        for number in range(1, min(8, count) + 1):
            loss = 40 * number
            first = 3519 * number - 3440
            last = 3519 * number
            if subcubic_saturation_shortfall_limit(layers, loss - 1) != first - 1:
                raise AssertionError(('subcubic plateau start', t, k, loss, first))
            if subcubic_saturation_shortfall_limit(layers, loss) != last:
                raise AssertionError(('subcubic plateau end', t, k, loss, last))
            for gap in (first, last):
                gain, _ = subcubic_layer_selection(layers, full_budget - gap)
                if capacity - gain != loss:
                    raise AssertionError(('subcubic staircase value', t, k, gap, capacity - gain))
        print('Subcubic saturation staircase:', t, k, min(8, count), 'plateaus')

    for k in (1, 3, 8):
        for cell in (0, 2 * k - 1):
            base = Fraction(1, 2) + Fraction(cell, 4 * k)
            flat = subcubic_omission_profile_bounds(k, base, bits=30)
            below = subcubic_omission_profile_bounds(k, base + Fraction(1, 48 * k), bits=30)
            edge = subcubic_omission_profile_bounds(k, base + Fraction(1, 36 * k), bits=30)
            above = subcubic_omission_profile_bounds(k, base + Fraction(1, 32 * k), bits=30)
            coarse = subcubic_omission_profile_bounds(k, base + Fraction(1, 32 * k), bits=14)
            if not (flat == below and max(flat[0], edge[0]) <= min(flat[1], edge[1])
                    and flat[1] < above[0] and coarse[0] <= above[0] <= above[1] <= coarse[1]):
                raise AssertionError(('subcubic packing profile', k, cell))
        print('Subcubic packing profile:', k, 'first and last cell thresholds verified')

    outer, inner = check_subcubic_cover_peak()
    print('Subcubic cover peak certificate slacks:', float(outer), float(inner))
    low_r, high_r = subcubic_growth_factor_bounds(56)
    for k in (1, 3, 8):
        expected = subcubic_max_omission_gap_bounds(k, bits=48)
        for cell in (0, 2 * k - 1):
            for shift in (-1, 0, 1):
                theta = Fraction(5, 36) + Fraction(shift, 512)
                x = Fraction(1, 2) + (cell + theta) / (4 * k)
                low, high = subcubic_omission_profile_bounds(k, x, bits=48)
                lower = 2 / (high_r ** 2 * (high_r - 1)) + 4 * (x - Fraction(1, 2)) / high_r ** 2
                upper = 2 / (low_r ** 2 * (low_r - 1)) + 4 * (x - Fraction(1, 2)) / low_r ** 2
                gap = (lower - high, upper - low)
                if shift == 0:
                    if max(expected[0], gap[0]) > min(expected[1], gap[1]):
                        raise AssertionError(('subcubic maximum packing gap', k, cell, gap))
                elif gap[1] >= expected[0]:
                    raise AssertionError(('subcubic packing gap near peak', k, cell, shift))
        print('Subcubic maximum packing gap:', k, float(expected[0]), float(expected[1]))

    for t, h, cubic, padding in ((3, 1, False, 0), (3, 1, False, 1), (4, 1, False, 5),
                                  (3, 1, True, 0), (4, 1, True, 24)):
        rank = subcubic_layered_lift_rank(t, h, cubic=cubic) + padding
        graph, blue, slow, waves = subcubic_bridgeless_layered_certificate(
            t, h, cubic=cubic, cycle_rank=rank
        )
        copies = 4 if cubic else 2
        losses = copies * h
        expected = t + h * (2 * t - 1 + 3 * 2 ** (t - 2))
        degrees = [row.bit_count() for row in graph]
        if (graph_bridges(graph) or min(degrees) < (3 if cubic else 2) or max(degrees) > 3
                or sum(degrees) // 2 - len(graph) + 1 != rank
                or slow.bit_count() != losses or completion_time(graph, blue) != t
                or len(waves) != expected):
            raise AssertionError(('bridgeless layered lift', t, h, cubic, rank))
        check_arrival_waves(graph, blue ^ slow, waves)
        seeds = list(members(blue))
        concentrated = mask([v for v in seeds if v < len(graph) // copies][:losses])
        scattered = mask(Random(273).sample(seeds, losses))
        for deletion in (concentrated, scattered):
            if completion_time(graph, blue ^ deletion) > len(graph):
                raise AssertionError(('arbitrary lift fault', t, h, cubic, deletion))
        print('Subcubic bridgeless lift:', t, losses, rank, expected, 'cubic:', cubic)

    for three_connected, cases in (
        (False, ((3, 0), (4, 0), (4, 1), (5, 0), (8, 0))),
        (True, ((3, 0), (3, 1), (4, 8), (5, 0), (8, 3))),
    ):
        for t, padding in cases:
            rank = cubic_single_loss_lift_rank(t, three_connected=three_connected) + padding
            graph, blue, slow, waves = cubic_single_loss_lift_certificate(
                t, cycle_rank=rank, three_connected=three_connected
            )
            expected = 3 * t + 2 ** (t - 1)
            if (graph_bridges(graph) or any(row.bit_count() != 3 for row in graph)
                    or len(graph) // 2 + 1 != rank or slow.bit_count() != 1 or not blue & slow
                    or completion_time(graph, blue) != t + 2 or len(waves) != expected):
                raise AssertionError(('cubic single-loss lift', t, rank, three_connected))
            check_arrival_waves(graph, blue ^ slow, waves)
            if t <= 5:
                limit = 2 if three_connected and t == 3 and padding == 0 else 1
                exhaustive += check_all_losses(graph, blue, limit)
            if three_connected and t <= 5:
                check_no_two_edge_cut(graph)
            print('Cubic single-loss lift:', t + 2, rank, expected, '3-connected:', three_connected)

    for rank in (16, 17, 26):
        graph, blue, lost = cubic_fourteen_round_certificate(rank)
        if (any(row.bit_count() != 3 for row in graph) or len(graph) // 2 + 1 != rank
                or completion_time(graph, blue) != 2):
            raise AssertionError(('cubic two-loss chain', rank))
        check_no_two_edge_cut(graph)
        check_arrival_waves(graph, blue ^ lost, [
            (13,), (12,), (4,), (7,), (3,), (0,), (2,), (5, 6),
            (20,), (23,), (19,), (16,), (18,), (21, 22),
        ])
        exhaustive += check_all_losses(graph, blue, 1)
        print('Cubic fourteen-round two-loss chain:', rank, len(graph))

    block, original_blue, _ = SINGLE['cubic_eight_round_certificate']()
    block_edges = [(v, w) for v, row in enumerate(block) for w in members(row) if v < w]
    for order, losses in ((16, (1, 10, 11)), (12, (1, 11))):
        for keep_tail_edge in (False, True):
            local = adjacency(order, [(v, w) for v, w in block_edges
                                      if w < order and (keep_tail_edge or (v, w) != (5, 6))])
            for seed in losses:
                if completion_time(local, (original_blue & ((1 << order) - 1)) ^ (1 << seed)) > order:
                    raise AssertionError(('local cubic chain recovery', order, seed))
    for losses, rank in ((1, 9), (1, 12), (2, 18), (3, 27), (5, 42), (12, 103)):
        graph, blue, lost, waves = cubic_two_round_chain_certificate(losses, rank)
        if (any(row.bit_count() != 3 for row in graph) or len(graph) // 2 + 1 != rank
                or completion_time(graph, blue) != 2 or lost.bit_count() != losses
                or len(waves) != 2 + 6 * losses):
            raise AssertionError(('cubic chain metadata', losses, rank))
        check_no_two_edge_cut(graph)
        check_arrival_waves(graph, blue ^ lost, waves)
        check_cubic_chain_root_forts(graph, blue, lost)
        exhaustive += check_all_losses(graph, blue, 1)
        print('Cubic two-round chain:', losses, rank, len(waves))

    check_compact_cubic_chain_contacts(block_edges, original_blue)
    for losses, rank in ((1, 9), (2, 16), (3, 22), (4, 29), (5, 37), (12, 81), (24, 159)):
        graph, blue, lost, waves = compact_cubic_two_round_chain_certificate(losses, rank)
        if (any(row.bit_count() != 3 for row in graph) or len(graph) // 2 + 1 != rank
                or completion_time(graph, blue) != 2 or lost.bit_count() != losses
                or lost & blue != lost or len(waves) != 2 + 6 * losses):
            raise AssertionError(('compact cubic chain metadata', losses, rank))
        check_no_two_edge_cut(graph)
        check_arrival_waves(graph, blue ^ lost, waves)
        exhaustive += check_all_losses(graph, blue, 1)
        print('Compact cubic two-round chain:', losses, rank, len(waves))

    for certificate, padded_rank in ((cubic_two_round_chain_certificate, 81),
                                     (compact_cubic_two_round_chain_certificate, 67)):
        for losses in range(1, 10):
            check_cubic_chain_loss_patterns(certificate, losses)
        check_cubic_chain_loss_patterns(certificate, 9, padded_rank)
    print('Cubic chain designated loss patterns: 3068 subsets')
    print('Compact cubic chain killing pairs:', check_compact_cubic_chain_killing_pairs(), 'two-seed cases')
    print('Bipartite cubic chain loss deadlines:', check_bipartite_cubic_chain_deadlines(), 'finite cases')

    for rank in (10, 12, 13, 22):
        graph, blue, lost, support = cubic_two_fault_gap_certificate(rank)
        if (any(row.bit_count() != 3 for row in graph) or len(graph) // 2 + 1 != rank
                or completion_time(graph, blue) != 2):
            raise AssertionError(('cubic two-fault gap graph', rank))
        check_no_two_edge_cut(graph)
        check_arrival_waves(graph, blue ^ lost, [
            (8,), (10,), (7,), (15,), (17,), (14,), (9,), (3,), (0, 1),
        ])
        times = [completion_time(graph, blue ^ mask(pair))
                 for pair in combinations(members(blue), 2)]
        restricted = max(completion_time(graph, blue ^ mask(pair))
                         for pair in combinations(members(support), 2))
        if max(times) != 9 or restricted != 3 or completion_time(graph, blue ^ support) <= len(graph):
            raise AssertionError(('cubic two-fault support', rank))
        exhaustive += len(times)
        print('Cubic six-round gap with two-fault tolerance:', rank, len(graph))

    rng = Random(421)
    for t, budget, padding, compact in (
        (3, 1, 0, False), (3, 4, 1, False), (4, 7, 0, False), (5, 12, 3, False),
        (3, 1, 0, True), (3, 2, 0, True), (3, 3, 2, True), (4, 4, 1, True), (6, 20, 0, True),
    ):
        options = dict(three_connected=True, fault_budget=budget, compact=compact)
        rank = cubic_single_loss_lift_rank(t, **options) + padding
        graph, blue, slow, waves = cubic_single_loss_lift_certificate(t, cycle_rank=rank, **options)
        if (graph_bridges(graph) or any(row.bit_count() != 3 for row in graph)
                or len(graph) // 2 + 1 != rank or completion_time(graph, blue) != t + 2
                or len(waves) != 3 * t + 2 ** (t - 1)):
            raise AssertionError(('cubic leaf cycle with adjustable protection', t, budget, rank))
        check_arrival_waves(graph, blue ^ slow, waves)
        seeds = list(members(blue))
        for lost_seeds in (seeds[:budget], seeds[-budget:], rng.sample(seeds, budget)):
            if completion_time(graph, blue ^ mask(lost_seeds)) > len(graph):
                raise AssertionError(('cubic leaf cycle fault budget', t, budget, lost_seeds))
        if compact and t == 3:
            check_no_two_edge_cut(graph)
            if budget <= 2:
                exhaustive += check_all_losses(graph, blue, budget)
        if compact and (t, budget, padding) == (6, 20, 0):
            killing = mask((328, 332, 334, 337, 341, 343, 348, 350, 352, 354, 1511,
                            1513, 1515, 1519, 1522, 1524, 1528, 1530, 1531, 1535, 1539))
            if (killing.bit_count() != 21 or killing & (slow | ~blue)
                    or completion_time(graph, blue ^ killing) <= len(graph)):
                raise AssertionError('Missing the 21-seed killing loss in the compact witness')
        print('Cubic leaf cycle protection:', t + 2, rank, budget, len(waves), 'compact:', compact)

    for rank in (4, 5, 12):
        edges, blue, start, support = SINGLE['subcubic_nine_round_certificate']()
        order = append_subcubic_blue_cycles(edges, 13, start, rank - 4, 1)
        graph = adjacency(order, edges)
        blue |= mask(range(start, order))
        check_connected(graph, 3)
        intact, delayed, _ = check_cycle_rank_trace(graph, blue, 1, rank)
        actual_rank = len(edges) - order + 1
        if (intact, delayed, actual_rank) != (2, 9, rank):
            raise AssertionError(('subcubic nine-round rank', rank, intact, delayed, actual_rank))
        if completion_time(graph, blue ^ support) <= order:
            raise AssertionError(('subcubic nine-round killing support', rank))
        exhaustive += check_all_losses(graph, blue, 1)
        print('Subcubic nine-round recovery:', rank, order, delayed)

    for t in (1, 2, 4, 7):
        for k in (1, 2, 3, 4, 6):
            graph, blue, slow, support = path_certificate(t, k)
            check_connected(graph, 2)
            observed = (completion_time(graph, blue), completion_time(graph, blue ^ slow))
            if observed != (t, t + k * (2 * t + 1)):
                raise AssertionError((t, k, observed))
            if completion_time(graph, blue ^ support) <= len(graph):
                raise AssertionError(('path support survives', t, k))
            exhaustive += check_all_losses(graph, blue, k)

    for t, k in ((0, 1), (0, 3), (1, 1), (1, 2), (2, 3), (4, 4), (5, 6)):
        graph, blue, slow, support = cycle_certificate(t, k)
        check_connected(graph, 2)
        observed = (completion_time(graph, blue), completion_time(graph, blue ^ slow))
        if observed != (t, t * (k + 1) + (k + 1) // 2):
            raise AssertionError(('cycle delay', t, k, observed))
        if completion_time(graph, blue ^ support) <= len(graph):
            raise AssertionError(('cycle support survives', t, k))
        exhaustive += check_all_losses(graph, blue, k)

    sparse_cases = ((1, 0), (1, 1), (1, 2), (1, 13), (2, 1), (2, 2), (2, 4),
                    (2, 8), (2, 9), (2, 10), (2, 35), (3, 10), (3, 11), (5, 9),
                    (5, 36), (8, 1), (8, 2), (8, 20), (8, 21), (8, 47))
    for k, rank in sparse_cases:
        graph, blue, slow, support, paths, degree = sparse_one_round_certificate(k, rank)
        sampled += check_robust_samples(graph, blue, slow, support, paths, degree, 1, k,
                                        clique_support=False)
        expected = one_round_cycle_rank_time(k, rank)
        check_ranked_one_round_example(graph, blue, slow, rank, expected)
        if k <= 2 and rank <= 4:
            exhaustive += check_all_losses(graph, blue, k)
        print('Sparse one-round family:', rank, k, len(graph), expected)

    rng = Random(247)
    for k, rank in ((1, 1), (2, 2), (8, 6)):
        graph, blue, slow, support = subcubic_rank_certificate(k, rank)
        check_connected(graph, 3)
        check_ranked_one_round_example(graph, blue, slow, rank, 1 + 3 * k)
        if completion_time(graph, blue ^ support) <= len(graph):
            raise AssertionError(('subcubic ranked killing loss', k, rank))
        if k <= 2:
            exhaustive += check_all_losses(graph, blue, k)
        seeds = tuple(members(blue))
        for _ in range(12):
            lost = mask(rng.sample(seeds, k))
            if completion_time(graph, blue ^ lost) > len(graph):
                raise AssertionError(('subcubic ranked sample', k, rank, lost))
            sampled += 1
        print('Subcubic one-round rank:', rank, k, len(graph), 1 + 3 * k)

    joint_cases = (
        (4, 1, 0, 4), (4, 1, 17, 5), (4, 4, 3, 14), (4, 4, 8, 17), (4, 4, 23, 17),
        (5, 4, 7, 16), (5, 4, 8, 17), (5, 4, 12, 17), (5, 4, 13, 18),
        (5, 4, 15, 18), (5, 4, 17, 18), (5, 4, 18, 19), (5, 4, 25, 19),
        (5, 5, 14, 21), (5, 5, 15, 22), (5, 5, 20, 23),
        (6, 2, 8, 9), (6, 2, 9, 10), (6, 2, 11, 11), (6, 2, 20, 11),
        (6, 4, 12, 17), (6, 4, 13, 18), (6, 4, 15, 19), (6, 4, 19, 19),
        (6, 4, 20, 20), (6, 4, 22, 21),
        (7, 5, 14, 21), (7, 5, 17, 23), (7, 5, 19, 24), (7, 5, 23, 24),
        (7, 5, 24, 25), (7, 5, 28, 27),
        (8, 7, 25, 33), (8, 7, 29, 33), (8, 7, 30, 34), (8, 7, 36, 37),
        (8, 7, 41, 38), (8, 7, 46, 40), (8, 7, 47, 41),
        (9, 2, 16, 13), (9, 2, 17, 14), (9, 2, 22, 14),
        (9, 4, 15, 19), (9, 4, 21, 22), (9, 4, 22, 22), (12, 5, 30, 29),
        (9, 3, 23, 18), (9, 3, 24, 18), (9, 3, 25, 18), (9, 3, 26, 19),
        (11, 5, 48, 35), (11, 5, 49, 35), (11, 5, 51, 36), (11, 5, 52, 36),
        (11, 5, 53, 37), (17, 7, 113, 71), (17, 7, 114, 72), (17, 7, 116, 73),
        (12, 4, 31, 25), (12, 4, 32, 26), (12, 4, 45, 32), (12, 4, 46, 33),
    )
    for cap, k, rank, expected in joint_cases:
        graph, blue, slow, support, paths, degree = bounded_rank_certificate(cap, k, rank)
        if degree > cap:
            raise AssertionError(('joint degree cap', cap, degree, k, rank))
        check_ranked_one_round_example(graph, blue, slow, rank, expected)
        sampled += check_robust_samples(graph, blue, slow, support, paths, degree, 1, k,
                                        clique_support=False)
        print('Joint one-round witness:', cap, rank, k, len(graph), expected)

    for d, k in ((5, 4), (6, 3), (6, 4), (6, 7), (7, 4), (7, 5),
                 (8, 3), (8, 6), (8, 7), (12, 8)):
        rank = (2 * d - 1) * (k // 2) + 2 * (k % 2)
        graph, blue, slow, support, paths, degree = assemble_one_round_certificate(
            k, rank, k % 2, (d - 2,) * (k // 2)
        )
        if degree != d:
            raise AssertionError(('one-round threshold degree', d, k, rank, degree))
        expected = sharp_one_round_time(d, k)
        check_ranked_one_round_example(graph, blue, slow, rank, expected)
        sampled += check_robust_samples(graph, blue, slow, support, paths, degree, 1, k,
                                        clique_support=False)
        print('Rank threshold for degree-only maximum:', d, rank, k, expected)

    for d, k in ((4, 2), (5, 3), (7, 4), (4, 6)):
        graph, blue, slow, support, paths, n = one_round_certificate(d, k)
        sampled += check_robust_samples(graph, blue, slow, support, paths, d, 1, k)
        if (n, completion_time(graph, blue ^ slow)) != (k * (d - 1) // 2, n + 1 + k // 2):
            raise AssertionError(('one-round delay', d, k, n))
        if (d, k) == (4, 2):
            exhaustive += check_all_losses(graph, blue, k)
        print('One-round family:', d, k, len(graph), n + 1 + k // 2)

    sharp_cases = ((4, 1), (4, 2), (4, 3), (4, 6), (5, 3), (6, 3), (6, 7),
                   (7, 2), (7, 3), (8, 3), (8, 4), (9, 5), (12, 2))
    for d, k in sharp_cases:
        graph, blue, slow, support, paths = sharp_one_round_certificate(d, k)
        sampled += check_robust_samples(graph, blue, slow, support, paths, d, 1, k)
        expected = sharp_one_round_time(d, k)
        if completion_time(graph, blue ^ slow) != expected:
            raise AssertionError(('sharp one-round deadline', d, k, expected))
        if (d, k) == (4, 2):
            exhaustive += check_all_losses(graph, blue, 2)
        print('Sharp one-round family:', d, k, len(graph), expected)

    for d, t, k in ((4, 2, 2), (5, 2, 3), (4, 3, 2), (5, 3, 3), (4, 2, 5)):
        graph, blue, slow, support, paths, early = layered_certificate(d, t, k)
        sampled += check_robust_samples(graph, blue, slow, support, paths, d, t, k)
        leaves = k * d * (d - 1)**(t - 2)
        expected = d * leaves // 2 - (leaves + d - 3) // (d - 2)
        late, arrivals = trace(graph, blue ^ slow)
        if early != expected or not early + 3 <= late <= len(graph):
            raise AssertionError(('layered delay', d, t, k, early, late))
        observed = sorted(r for r in arrivals if 1 <= r <= early + 3)
        if observed != list(range(1, early + 4)):
            raise AssertionError(('serial prefix', d, t, k))
        print('Layered family:', d, t, k, len(graph), late)

    for k in (1, 2, 3, 8, 32):
        graph, blue, slow = subcubic_two_round_certificate(k)
        check_connected(graph, 3)
        intact = completion_time(graph, blue)
        late, arrivals = trace(graph, blue ^ slow)
        if (slow.bit_count(), intact, late) != (k, 2, 2 + 7 * k):
            raise AssertionError(('subcubic two-round delay', k, intact, late))
        local_rounds = (5, 4, 5, 6, 3, 1, 7, 2)
        for copy in range(k):
            start = 12 * copy
            expected = tuple(2 + 7 * copy + r for r in local_rounds)
            if tuple(arrivals[start:start + 8]) != expected:
                raise AssertionError(('subcubic block delays', k, copy, expected))
        _, _, revisits = check_cycle_rank_trace(graph, blue, slow, 4 * k)
        if revisits == 0:
            raise AssertionError(('subcubic trail should revisit a contracted subtree', k))
        print('Subcubic two-round family:', k, len(graph), late, 'trail revisits:', revisits)

    for d, k in ((4, 2), (4, 5), (5, 3), (6, 2), (7, 3), (8, 2), (6, 7)):
        graph, blue, slow, support, paths = two_round_certificate(d, k)
        sampled += check_robust_samples(graph, blue, slow, support, paths, d, 2, k)
        expected = 2 + k * (SINGLE['quadratic_degree_time'](d) - 2)
        upper = 2 + (13 * k if d == 4 else k * (d**2 + 11) // 2)
        if completion_time(graph, blue ^ slow) != expected or expected > upper:
            raise AssertionError(('concatenated two-round delay', d, k, expected, upper))
        print('Concatenated two-round family:', d, k, len(graph), expected, upper)

    print('Exhaustive losses on degree-two, sparse-cycle and small one-round examples:', exhaustive)
    print('Recoverable losses checked against the cycle upper bound:', check_small_cycles())
    print('Recoverable losses checked against the subcubic one-round bound:',
          check_small_subcubic_one_round())
    print('Sampled losses on the protected examples:', sampled)


if __name__ == '__main__':
    main()
