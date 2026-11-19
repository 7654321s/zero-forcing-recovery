"""Replay extremal recovery examples for several lost initial blue vertices."""

from heapq import heappop, heappush
from itertools import combinations, pairwise
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


def protect_seeds(degree, edges, blue, order, deliberately_lost, seed, *, clique_support=True,
                  neutral_rank=0):
    """Add private blue paths and a connected minimum killing support."""
    losses = len(deliberately_lost)
    support = range(order, order + losses + 1)
    order = support.stop
    support_pairs = (combinations(support, 2) if clique_support and losses <= degree
                     else pairwise(support))
    attachment = order
    for left, right in support_pairs:
        edges.extend(((order, left), (order, right)))
        blue.append(order)
        order += 1
    if degree != 3:
        edges.append((seed, attachment))

    paths = []
    unprotected = set(deliberately_lost)
    for vertex in blue[:]:
        if vertex not in unprotected:
            path = range(order, order + 2 * losses + 2)
            edges.append((vertex, path[0]))
            edges.extend(pairwise(path))
            if degree == 3 and vertex == attachment:
                edges.append((seed, path[-1]))
            blue.extend(path)
            paths.append(tuple(path))
            order = path.stop
    if neutral_rank:
        start = order
        order = append_subcubic_blue_cycles(edges, paths[0][-1], order, neutral_rank, losses)
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


def subcubic_recursive_rank_certificate(rounds, losses, cycle_rank, *, splice_centers=False):
    edges, blue, lost = list(pairwise(range(rounds + 1))), [0], []
    main_paths = []
    detours = [[] for _ in range(losses)]
    hosts, releases = [], []
    order = rounds + 1
    for block in range(losses):
        root = order
        blue.append(root)
        lost.append(root)
        order, left = relay_arm(edges, blue, root, order + 1, rounds)
        order, right = relay_arm(edges, blue, root, order, rounds)
        main_paths.append([*reversed(left), root, *right])
        heappush(hosts, (0, root, block))
        for depth, (a, b) in enumerate(zip(left[:-2], right[:-2]), 1):
            heappush(hosts, (depth, a, block))
            heappush(hosts, (depth, b, block))

    def record_detour(block, depth, host, parent, guard, center, incoming, outgoing,
                      *, shortened_outgoing=False):
        detours[block].append((depth, [*reversed(incoming), center, *outgoing]))
        releases.append((host, parent, guard, center))
        center_depth = depth + 2
        if center_depth <= rounds - 2:
            heappush(hosts, (center_depth, guard, block))
        for arm_depth, a in enumerate(incoming[:-2], center_depth + 1):
            heappush(hosts, (arm_depth, a, block))
        outgoing_start = center_depth + 1
        if shortened_outgoing:
            # The other detour already registered its guard at depth four.
            outgoing = outgoing[1:]
            outgoing_start += 2
        for arm_depth, b in enumerate(outgoing[:-2], outgoing_start):
            heappush(hosts, (arm_depth, b, block))

    splices = min(losses, max(0, cycle_rank - 6 * losses)) if splice_centers and rounds >= 5 else 0
    for _ in range(cycle_rank - splices):
        if not hosts:
            break
        depth, host, block = heappop(hosts)
        center_depth = depth + 2
        order, parent, guard, center = subcubic_detour_center(edges, blue, host, order)
        order, incoming = relay_arm(edges, blue, center, order, rounds - center_depth)
        splice = depth == 0 and block < splices
        if splice:
            order, child_parent, child_guard, child_center, left, right = subcubic_detour(
                edges, blue, center, order, rounds - 4
            )
            record_detour(block, 2, center, child_parent, child_guard, child_center, left, right)
            order, tail = relay_arm(edges, blue, child_guard, order, rounds - 4)
            outgoing = [child_guard, *tail]
        else:
            order, outgoing = relay_arm(edges, blue, center, order, rounds - center_depth)
        record_detour(block, depth, host, parent, guard, center, incoming, outgoing,
                      shortened_outgoing=splice)

    sequence = list(range(1, rounds + 1))
    for block, main in enumerate(main_paths):
        ordered = sorted(detours[block], key=lambda item: item[0], reverse=True)
        paths = [path for _, path in ordered]
        for path in [*paths, main]:
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

    graph, initial, support, paths = protect_seeds(
        3, edges, blue, order, lost, 0, clique_support=False,
        neutral_rank=cycle_rank - len(releases)
    )
    return graph, initial, mask(lost), support, paths, waves


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
