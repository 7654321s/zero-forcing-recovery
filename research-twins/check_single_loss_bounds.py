"""Replay single-loss bounds and the extremal recovery families."""

from itertools import combinations, pairwise, product
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
TWINS = runpy.run_path(str(HERE / 'check_twin_truncation.py'))
MODEL = TWINS['MODEL']
adjacency = MODEL['TOOLS']['adjacency']
members = MODEL['TOOLS']['neighbors']
mask = MODEL['mask']
completion_time = MODEL['completion_time']
trace = runpy.run_path(str(HERE.parent / 'research-unicyclic' /
                           'verify_path_padding_reduction.py'))['trace']


def check_groups(white, other_singletons, pairs, joins, lost, early, late, cliques=()):
    labels = {}
    n = 0
    groups = [(name, 1) for name in (*white, *other_singletons)] + [(name, 2) for name in pairs]
    for name, size in groups:
        labels[name] = range(n, n + size)
        n += size
    edges = [edge for x, y in joins for edge in product(labels[x], labels[y])]
    edges.extend(edge for name in cliques for edge in combinations(labels[name], 2))
    adj = adjacency(n, edges)
    blue = ((1 << n) - 1) ^ mask(labels[v][0] for v in white)
    support = mask(labels['A'])
    slow = 1 << labels[lost][0]
    if completion_time(adj, blue) != early:
        raise AssertionError((white, lost, 'intact time'))
    MODEL['certify'](adj, blue, support, slow, early, late)


def extremal_examples():
    check_groups(
        ('x0', 'x1', 'x2', 'x3'), ('z',), ('A', 'P', 'U', 'D2', 'D3'),
        [('x0', 'x1'), ('x1', 'x2'), ('z', 'x1'), ('A', 'x0'), ('A', 'P'),
         ('U', 'x1'), ('U', 'x2'), ('D2', 'x2'), ('D2', 'z'), ('D3', 'x3'), ('D3', 'z')],
        'z', 1, 5,
    )
    check_groups(
        ('x1', 'x2', 'x3'), (), ('A', 'P', 'Z', 'D2', 'D3'),
        [('x1', 'x2'), ('A', 'x1'), ('A', 'P'), ('D2', 'x2'), ('D2', 'Z'),
         ('D3', 'x3'), ('D3', 'Z')],
        'Z', 1, 4,
    )


def check_two_round_family():
    sizes = [*range(2, 49), 64, 100]
    for length in sizes:
        white = [f'w{i}' for i in range(1, length + 1)] + ['g']
        pairs = ['A', 'P']
        joins = [*zip(white, white[1:]), ('z', 'g'), ('A', 'w1'), ('A', 'P')]
        for i in range(2, length + 1):
            source, helper = f'D{i}', f'E{i}'
            pairs.extend((source, helper))
            joins.extend(((source, helper), (source, 'g'), (source, 'z'), (source, f'w{i}')))
        check_groups(white, ('z',), pairs, joins, 'z', 2, length + 2)
        check_groups(white, (), [*pairs, 'z'], joins, 'z', 2, length + 2, cliques=('z',))
        nonadjacent = [edge for edge in joins if edge != ('z', 'g')] + [('C', 'g'), ('C', 'z')]
        check_groups(white, (), [*pairs, 'z', 'C'], nonadjacent, 'z', 2, length + 2)
    return 3 * len(sizes)


def check_small_graphs():
    cases = paired_cases = 0
    for n in range(1, 6):
        possible = list(combinations(range(n), 2))
        for edge_mask in range(1 << len(possible)):
            adj = adjacency(n, (possible[i] for i in members(edge_mask)))
            times = [completion_time(adj, blue) for blue in range(1 << n)]
            for blue, intact in enumerate(times):
                if intact > 1:
                    continue
                for lost in members(blue):
                    recovery = times[blue ^ (1 << lost)]
                    if recovery > n:
                        continue
                    if recovery > 5:
                        raise AssertionError((adj, blue, lost, recovery))
                    cases += 1
                    if any(v != lost and TWINS['twins'](adj, v, lost) for v in members(blue)):
                        if recovery > 4:
                            raise AssertionError((adj, blue, lost, recovery))
                        paired_cases += 1
    return cases, paired_cases


def check_two_round_bound(degree, lost, full_arrivals, delayed_arrivals):
    missed_first = {v for v, arrival in enumerate(full_arrivals)
                    if arrival <= 1 and (delayed_arrivals[v] is None or delayed_arrivals[v] > 1)}
    missed_second = {v for v, arrival in enumerate(delayed_arrivals)
                     if arrival is None or arrival > 2}
    if lost in missed_first:
        bound = 1 + degree + (degree - 1) * (len(missed_first) - 1)
    else:
        bound = (degree - 1) * len(missed_first)
    if len(missed_second) > bound:
        raise AssertionError((degree, lost, missed_first, missed_second, bound))
    if None not in delayed_arrivals:
        cap = min(degree**2 + 3, degree**2 // 2 + (6 if degree >= 6 else 7))
        if degree == 3:
            cap = 9
        if degree == 3 and len(missed_second) != 8:
            cap = 8
        if max(delayed_arrivals) > cap:
            raise AssertionError((degree, lost, delayed_arrivals, cap))
    return len(missed_second)


def check_discrepancy_growth():
    transitions = two_round_cases = 0
    for n in range(1, 6):
        possible = list(combinations(range(n), 2))
        for edge_mask in range(1 << len(possible)):
            adj = adjacency(n, (possible[i] for i in members(edge_mask)))
            degrees = [row.bit_count() for row in adj]
            degree = max(degrees)
            traces = [trace(adj, blue) for blue in range(1 << n)]
            for blue, (intact, full_arrivals) in enumerate(traces):
                if intact > n:
                    continue
                for lost in members(blue):
                    delayed, delayed_arrivals = traces[blue ^ (1 << lost)]
                    if degree and intact <= 2:
                        check_two_round_bound(degree, lost, full_arrivals, delayed_arrivals)
                        two_round_cases += 1
                    differences = {lost}
                    ever_affected = {lost}
                    capacity, next_layer = 1, degree
                    for round_number in range(1, intact + 1):
                        next_differences = {v for v in range(n) if full_arrivals[v] <= round_number
                                            and (delayed_arrivals[v] is None
                                                 or delayed_arrivals[v] > round_number)}
                        bound = sum(degrees[v] + (v == lost) for v in differences)
                        if len(next_differences) > bound:
                            raise AssertionError((adj, blue, lost, round_number, bound))
                        ever_affected.update(next_differences)
                        capacity += next_layer
                        next_layer *= degree - 1
                        if len(ever_affected) > capacity:
                            raise AssertionError((adj, blue, lost, round_number, capacity))
                        if round_number >= 2:
                            full_blue = mask(v for v in range(n)
                                             if full_arrivals[v] < round_number)
                            old = mask(differences)
                            multiple_blockers = 0
                            for target in next_differences - differences:
                                source = next(v for v in members(adj[target] & full_blue)
                                              if (adj[v] & ~full_blue) == (1 << target))
                                blockers = (adj[source] & old).bit_count()
                                if source not in differences and blockers > 1:
                                    multiple_blockers += 1
                            if len(next_differences) + multiple_blockers > capacity:
                                raise AssertionError((adj, lost, round_number, multiple_blockers))
                        if round_number == intact and delayed <= n:
                            extra = ((degree + 4) * len(differences) + 1) // 2
                            if delayed > intact + extra:
                                raise AssertionError((adj, blue, lost, delayed, intact + extra))
                        differences = next_differences
                        transitions += 1
    return transitions, two_round_cases


def check_saturated_subcubic():
    # Vertices 4..6 are round-one targets. Each blocks two round-two targets
    # after loss of vertex 0. The separate branch through 19..22 starts repair.
    for lost_is_source in (False, True):
        edges = [(0, 1), (0, 2), (1, 4), (2, 5)]
        edges += [(0, 6), (3, 22)] if lost_is_source else [(0, 3), (3, 6)]
        for offset in range(6):
            edges.extend(((4 + offset // 2, 7 + offset), (7 + offset, 13 + offset)))
        edges.extend(((13, 19), (19, 20), (20, 21), (21, 22)))
        adj = adjacency(23, edges)
        blue = mask([0, 1, 2, 3, *range(7, 13), 20, 22])
        intact, full_arrivals = trace(adj, blue)
        delayed, delayed_arrivals = trace(adj, blue ^ 1)
        degree = max(row.bit_count() for row in adj)
        if degree != 3 or intact != 2 or delayed > len(adj):
            raise AssertionError((lost_is_source, degree, intact, delayed))
        if check_two_round_bound(degree, 0, full_arrivals, delayed_arrivals) != 10:
            raise AssertionError((lost_is_source, delayed_arrivals))


def check_subcubic_example():
    edges = [(0, 1), (0, 15), (0, 16), (1, 2), (1, 4), (2, 3), (2, 9),
             (3, 5), (3, 6), (4, 7), (4, 8), (5, 8), (6, 10), (6, 13),
             (7, 11), (7, 12), (8, 16), (9, 14), (10, 14), (11, 15), (11, 16),
             (12, 14), (12, 15)]
    adj = adjacency(17, edges)
    blue = mask([0, 1, 2, 6, 7, 9, 11, 12, 14])
    if max(row.bit_count() for row in adj) != 3 or completion_time(adj, blue) > 2:
        raise AssertionError('Incorrect subcubic graph or intact deadline')
    MODEL['certify'](adj, blue, mask([0, 11]), 1 << 9, 2, 7)


def check_eight_round_example():
    edges = [(0, 1), (0, 11), (0, 14), (1, 5), (1, 10), (2, 11), (2, 12),
             (2, 13), (3, 14), (3, 15), (3, 16), (4, 6), (4, 10), (4, 17),
             (5, 6), (5, 9), (6, 12), (7, 9), (7, 13), (8, 15), (9, 16),
             (17, 18), (18, 19), (19, 20), (20, 21), (21, 22), (21, 23)]
    adj = adjacency(24, edges)
    blue = mask([0, 10, 11, 12, 13, 14, 15, 16, 18, 20, 21, 22, 23])
    intact, full_arrivals = trace(adj, blue)
    delayed, delayed_arrivals = trace(adj, blue ^ 1)
    degree = max(row.bit_count() for row in adj)
    if (degree, intact, delayed) != (3, 2, 8):
        raise AssertionError((degree, intact, delayed))
    if check_two_round_bound(degree, 0, full_arrivals, delayed_arrivals) != 10:
        raise AssertionError(delayed_arrivals)
    expected = [{19}, {17}, {4}, {1, 6}, {2, 5}, {0, 7, 9}, {3}, {8}]
    actual = [{v for v, arrival in enumerate(delayed_arrivals) if arrival == round_number}
              for round_number in range(1, delayed + 1)]
    if actual != expected:
        raise AssertionError(actual)
    MODEL['certify'](adj, blue, mask([22, 23]), 1, 2, 8)


def subcubic_two_round_block():
    edges = [(0, 1), (0, 8), (0, 9), (1, 4), (1, 10), (2, 8), (2, 10),
             (2, 11), (3, 6), (3, 9), (3, 11), (4, 7), (5, 7), (5, 10),
             (7, 11)]
    return edges, [0, 8, 9, 10, 11], 12, 5, 6


def subcubic_nine_round_certificate():
    block, seeds, size, entry, _ = subcubic_two_round_block()
    edges = [*block, (entry, size), (12, 13), (13, 14), (14, 15), (14, 16)]
    blue = mask([*seeds, 13, 15, 16])
    return edges, blue, 17, mask([15, 16])


def check_nine_round_example():
    edges, blue, size, support = subcubic_nine_round_certificate()
    adj = adjacency(size, edges)
    intact, full_arrivals = trace(adj, blue)
    delayed, delayed_arrivals = trace(adj, blue ^ 1)
    degree = max(row.bit_count() for row in adj)
    if (degree, intact, delayed) != (3, 2, 9):
        raise AssertionError((degree, intact, delayed))
    if check_two_round_bound(degree, 0, full_arrivals, delayed_arrivals) != 8:
        raise AssertionError(delayed_arrivals)
    expected = [{14}, {12}, {5}, {7}, {4}, {1}, {0, 2}, {3}, {6}]
    actual = [{v for v, arrival in enumerate(delayed_arrivals) if arrival == round_number}
              for round_number in range(1, delayed + 1)]
    if actual != expected:
        raise AssertionError(actual)
    MODEL['certify'](adj, blue, support, 1, 2, 9)


def check_low_degree_examples():
    edge = adjacency(2, [(0, 1)])
    if completion_time(edge, 1) != 1:
        raise AssertionError('Degree-one recovery should take one round')
    for rounds in range(1, 26):
        path = range(3 * rounds + 3)
        leaf_a, leaf_b = path.stop, path.stop + 1
        lost = 2 * rounds + 1
        path_and_edge = adjacency(leaf_b + 1, [*pairwise(path), (leaf_a, leaf_b)])
        blue = mask([0, lost, lost + 1, leaf_a, leaf_b])
        if completion_time(path_and_edge, blue) != rounds:
            raise AssertionError(('degree-two intact time', rounds))
        MODEL['certify'](path_and_edge, blue, mask([leaf_a, leaf_b]),
                         1 << lost, rounds, 3 * rounds + 1)


def quadratic_relay_links(prefix, targets, splice=None):
    if splice is None:
        return list(pairwise([prefix, *targets]))
    enter, resume = splice
    return [(prefix, enter), *pairwise([resume, *targets])]


def complete_quadratic_certificate(edges, blue, next_vertex, targets, splice=None):
    first, second, seed, helper, leaf_a, leaf_b = range(next_vertex, next_vertex + 6)
    pairs = quadratic_relay_links(second, targets, splice)
    relays = range(leaf_b + 1, leaf_b + 1 + len(pairs))
    for source, (left, right) in zip(relays, pairs):
        edges.extend(((source, left), (source, right)))
    edges.extend(((seed, first), (first, second), (seed, helper),
                  (helper, leaf_a), (helper, leaf_b)))
    adj = adjacency(relays.stop, edges)
    initial = mask([*blue, *relays, seed, helper, leaf_a, leaf_b])
    return adj, initial, mask([leaf_a, leaf_b])


def even_quadratic_degree_block(degree, continue_at_tail):
    lost = 0
    missed = range(1, degree + 1)
    predecessors = range(missed.stop, missed.stop + degree - 1)
    tail_parent = missed[3]
    cycle = list(zip(missed, [*missed[1:], missed[0]]))
    pairs = cycle * ((degree - 2) // 2)
    pairs.remove((missed[0], missed[1]))
    pairs.remove((tail_parent, missed[4]))
    pairs.append((missed[1], missed[4]))
    outside_sources = range(predecessors.stop, predecessors.stop + len(pairs))
    outside_targets = range(outside_sources.stop, outside_sources.stop + len(pairs))
    direct_targets = range(outside_targets.stop, outside_targets.stop + degree - 1)
    guard, tail, tail_source, last, last_source = range(direct_targets.stop,
                                                       direct_targets.stop + 5)

    edges = [(lost, missed[0]), *((lost, p) for p in predecessors),
             *zip(predecessors, missed[1:])]
    for source, pair, target in zip(outside_sources, pairs, outside_targets):
        edges.extend((source, v) for v in (*pair, target))
    edges.extend(zip(missed[1:], direct_targets))
    edges.extend((x, guard) for x in direct_targets)
    tail_child = direct_targets[tail_parent - missed[1]]
    tail_children = (tail_child,) if continue_at_tail else direct_targets
    edges.extend((x, tail) for x in tail_children)
    edges.extend(((missed[0], guard), (missed[0], last_source), (last_source, last),
                  (tail_parent, tail_source), (tail_source, tail)))
    blue = [lost, *predecessors, *outside_sources, tail_source, last_source]
    return edges, blue, last_source + 1, [*outside_targets, *direct_targets, last], tail, None


def small_quadratic_degree_block(degree):
    lost = 0
    missed = range(1, degree + 1)
    ordinary = missed[1:]
    predecessors = range(missed.stop, missed.stop + len(ordinary))
    multiplicities = (1, 1) if degree == 4 else (2, 1, 2)
    pairs = [(left, right) for left, right, count in zip(ordinary, ordinary[1:], multiplicities)
             for _ in range(count)]
    outside_sources = range(predecessors.stop, predecessors.stop + len(pairs))
    outside_targets = range(outside_sources.stop, outside_sources.stop + len(pairs))
    direct_targets = range(outside_targets.stop, outside_targets.stop + len(ordinary))
    guard, tail, finish, enter, resume = range(direct_targets.stop, direct_targets.stop + 5)
    finish_source, tail_source, enter_source, resume_source = range(resume + 1, resume + 5)

    edges = [(lost, missed[0]), *((lost, p) for p in predecessors),
             *zip(predecessors, ordinary)]
    for source, pair, target in zip(outside_sources, pairs, outside_targets):
        edges.extend((source, v) for v in (*pair, target))
    edges.extend(zip(ordinary, direct_targets))
    edges.extend((guard, x) for x in direct_targets[:-1])
    edges.extend(((missed[0], guard), (tail, direct_targets[-1]),
                  (ordinary[0], finish_source), (finish_source, finish),
                  (ordinary[-1], tail_source), (tail_source, tail),
                  (missed[0], enter_source), (enter_source, enter),
                  (missed[0], resume_source), (resume_source, resume)))
    blue = [lost, *predecessors, *outside_sources, finish_source, tail_source,
            enter_source, resume_source]
    targets = [*outside_targets, *direct_targets, finish]
    return edges, blue, resume_source + 1, targets, tail, (enter, resume)


def odd_quadratic_degree_block(degree):
    lost = 0
    predecessors = range(1, degree + 1)
    missed = range(degree + 1, 2 * degree + 1)
    group = [missed[0], *missed[3:]]
    size = len(group)
    cycle = list(zip(group, [*group[1:], group[0]]))
    pairs = [(missed[1], missed[2])] * (size - 1) + cycle * (size // 2)
    pairs.extend(zip(group[1::2], group[2::2]))

    outside_sources = range(missed.stop, missed.stop + len(pairs))
    outside_targets = range(outside_sources.stop, outside_sources.stop + len(pairs))
    direct_targets = range(outside_targets.stop, outside_targets.stop + degree)
    guard_source, guard, tail_source, tail = range(direct_targets.stop, direct_targets.stop + 4)
    edges = [(lost, p) for p in predecessors] + list(zip(predecessors, missed))
    for source, pair, target in zip(outside_sources, pairs, outside_targets):
        edges.extend((source, v) for v in (*pair, target))
    edges.extend(zip(missed, direct_targets))
    edges.extend((guard, x) for x in (direct_targets[0], *direct_targets[3:]))
    edges.extend((tail, x) for x in direct_targets[1:3])
    edges.extend(((missed[0], guard_source), (guard_source, guard),
                  (missed[1], tail_source), (tail_source, tail)))
    blue = [lost, *predecessors, *outside_sources, guard_source, tail_source]
    return edges, blue, tail + 1, [*outside_targets, *direct_targets, guard], tail, None


def quadratic_degree_block(degree, continue_at_tail=False):
    if degree <= 5:
        return small_quadratic_degree_block(degree)
    if degree % 2:
        return odd_quadratic_degree_block(degree)
    return even_quadratic_degree_block(degree, continue_at_tail)


def quadratic_degree_certificate(degree):
    edges, blue, order, targets, _, splice = quadratic_degree_block(degree)
    return complete_quadratic_certificate(edges, blue, order, targets, splice)


def quadratic_degree_time(degree):
    return degree**2 // 2 + (7 if degree <= 5 else 6)


def check_quadratic_degree_family():
    degrees = range(4, 23)
    for degree in degrees:
        adj, blue, support = quadratic_degree_certificate(degree)
        if max(row.bit_count() for row in adj) != degree or completion_time(adj, blue) != 2:
            raise AssertionError((degree, len(adj)))
        MODEL['certify'](adj, blue, support, 1, 2, quadratic_degree_time(degree))
    return len(degrees)


def nonterminal_layers(degree, rounds, reserve_path_edge):
    lost = 0
    predecessors = range(1, degree + 1)
    roots = range(degree + 1, 2 * degree + 1)
    branches = [[root] for root in roots]
    order = roots.stop
    blue = [lost, *predecessors]
    edges = [(lost, parent) for parent in predecessors] + list(zip(predecessors, roots))

    for _ in range(2, rounds):
        next_branches = []
        for branch in branches:
            children = []
            for parent in branch:
                count = degree - 1 - (reserve_path_edge and parent == roots[0])
                for _ in range(count):
                    source, child = order, order + 1
                    order += 2
                    edges.extend(((source, parent), (source, child)))
                    blue.append(source)
                    children.append(child)
            next_branches.append(children)
        branches = next_branches

    return edges, blue, order, roots[0], branches


def layered_degree_certificate(degree, rounds):
    edges, blue, order, first_root, branches = nonterminal_layers(degree, rounds, True)
    terminal = []
    for branch in branches:
        if len(branch) < 2:
            continue
        pairs = list(pairwise([*branch, branch[0]])) * ((degree - 1) // 2)
        if degree % 2 == 0:
            pairs.extend(zip(branch[::2], branch[1::2]))
        for left, right in pairs:
            source, child = order, order + 1
            order += 2
            blue.append(source)
            terminal.append(child)
            edges.extend(((source, left), (source, right), (source, child)))

    seed, helper, leaf_a, leaf_b = range(order, order + 4)
    blue.extend((seed, helper, leaf_a, leaf_b))
    edges.extend(pairwise([seed, *terminal, first_root]))
    edges.extend(((seed, helper), (helper, leaf_a), (helper, leaf_b)))
    return adjacency(leaf_b + 1, edges), mask(blue), mask([leaf_a, leaf_b]), len(terminal)


def check_layered_degree_family():
    cases = ((3, 3), (3, 4), (3, 6), (4, 3), (4, 4), (4, 6), (5, 3),
             (5, 4), (5, 5), (6, 3), (8, 3), (10, 3))
    for degree, rounds in cases:
        adj, blue, support, terminal = layered_degree_certificate(degree, rounds)
        first = (degree - 2) * (degree - 1)**(rounds - 2) // 2
        other = (degree - 1)**(rounds - 1) // 2
        expected = first + (degree - 1) * other - ((degree, rounds) == (3, 3))
        if terminal != expected or max(row.bit_count() for row in adj) != degree:
            raise AssertionError((degree, rounds, terminal, expected))
        if completion_time(adj, blue) != rounds:
            raise AssertionError(('layered intact time', degree, rounds))
        MODEL['certify'](adj, blue, support, 1, rounds, terminal + rounds + 1)
    return len(cases)


def cyclic_pairs(vertices, capacity):
    pairs = list(pairwise([*vertices, vertices[0]])) * (capacity // 2)
    if capacity % 2:
        pairs.extend(zip(vertices[::2], vertices[1::2]))
    return pairs


def guarded_terminal_layer(degree, edges, blue, order, parents):
    outside = []
    for left, right in cyclic_pairs(parents, degree - 2):
        source, child = order, order + 1
        order += 2
        edges.extend(((source, left), (source, right), (source, child)))
        blue.append(source)
        outside.append(child)

    direct = range(order, order + len(parents))
    edges.extend(zip(parents, direct))
    guards, guarded = [], []
    for index in range(0, len(direct), degree - 2):
        group = direct[index:index + degree - 2]
        guards.append(group[0])
        guarded.extend(group[1:])
        edges.extend((group[0], child) for child in group[1:])
    return direct.stop, [*outside, *guarded, *guards], len(outside) + len(guarded)


def guarded_layered_certificate(degree, rounds):
    edges, blue, order, _, branches = nonterminal_layers(degree, rounds, False)
    parents = [v for branch in branches for v in branch]
    order, targets, early = guarded_terminal_layer(degree, edges, blue, order, parents)
    graph, seeds, support = complete_quadratic_certificate(
        edges, blue, order, targets
    )
    return graph, seeds, support, early


def check_guarded_layered_family():
    cases = ((4, 3), (5, 3), (6, 3), (8, 3), (5, 4), (6, 4))
    for degree, rounds in cases:
        adj, blue, support, early_targets = guarded_layered_certificate(degree, rounds)
        last_layer = degree * (degree - 1)**(rounds - 2)
        guard_count = (last_layer + degree - 3) // (degree - 2)
        if early_targets != degree * last_layer // 2 - guard_count:
            raise AssertionError((degree, rounds, early_targets))
        if max(row.bit_count() for row in adj) != degree or completion_time(adj, blue) != rounds:
            raise AssertionError(('guarded layered deadline or degree', degree, rounds))
        delayed, arrivals = trace(adj, blue ^ 1)
        if delayed < early_targets + 3 or delayed > len(adj):
            raise AssertionError((degree, rounds, delayed))
        early_rounds = sorted(time for time in arrivals if 1 <= time <= early_targets + 3)
        if early_rounds != list(range(1, early_targets + 4)):
            raise AssertionError(('guarded serial prefix', degree, rounds))
        MODEL['certify'](adj, blue, support, 1, rounds, delayed)
    return len(cases)


def main():
    extremal_examples()
    print('Sharp one-round examples: two certificates at times 1/5 and 1/4')
    print('Unbounded two-round family:', check_two_round_family(), 'certificates')
    cases, paired_cases = check_small_graphs()
    print('Recoverable singleton cases through graph order five:', cases)
    print('Cases with a retained twin:', paired_cases)
    transitions, two_round_cases = check_discrepancy_growth()
    print('Discrepancy growth, cumulative bound and incidence transitions:', transitions)
    print('Refined round-two discrepancy cases:', two_round_cases)
    check_saturated_subcubic()
    print('Saturated subcubic cases with ten whites after round two: 2')
    check_subcubic_example()
    print('Subcubic example: exact restricted time 2 and delayed time 7')
    check_eight_round_example()
    print('Saturated subcubic example: exact restricted time 2 and delayed time 8')
    check_nine_round_example()
    print('Sharp subcubic example: exact restricted time 2 and delayed time 9')
    check_low_degree_examples()
    print('Sharp maximum-degree-one example and degree-two examples for deadlines 1..25')
    print('Quadratic-degree examples with exact restricted time 2:', check_quadratic_degree_family())
    print('Layered examples with exact restricted time 3..6:', check_layered_degree_family())
    print('Guarded layered examples with the stronger lower bound:', check_guarded_layered_family())


if __name__ == '__main__':
    main()
