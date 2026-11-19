"""Exhaust the subcubic round-two residuals with seven to ten whites."""

from argparse import ArgumentParser
from itertools import combinations, combinations_with_replacement


def toggle_edge(neighbors, left, right):
    neighbors[left] ^= 1 << right
    neighbors[right] ^= 1 << left


def templates(white_count):
    for missed in (2, 3):
        for own_first_target in (False, True):
            # A branch is specified by its new targets and whether one is
            # forced directly. A branch with two targets has an outside source.
            branch_types = ((0, False), (1, False), (1, True), (2, False), (2, True))
            ordinary = combinations_with_replacement(branch_types, missed - own_first_target)
            for ordinary_branches in ordinary:
                first_branches = ((branch,) for branch in branch_types) if own_first_target else ((),)
                for first_branch in first_branches:
                    for lost_count in range(4 - missed):
                        assignments = ((lost_count, False), *first_branch, *ordinary_branches)
                        yield from residual_templates(
                            white_count, missed, own_first_target, assignments
                        )


def residual_templates(white_count, missed, own_first_target, assignments):
    old = missed + 1
    new = sum(count for count, _ in assignments)
    restored_count = old + new - white_count
    if restored_count < 0:
        return

    remaining = [3 - missed] + [2] * missed + [2] * new
    neighbors = [0] * (old + new)
    rules = []
    for parent in range(1, old):
        if own_first_target and parent == 1:
            toggle_edge(neighbors, 0, parent)
        else:
            rules.append(1 | (1 << parent))

    next_child = old
    outside_sources = []
    for parent, (count, direct) in enumerate(assignments):
        remaining[parent] -= count
        for index in range(count):
            if direct and index == 0:
                toggle_edge(neighbors, parent, next_child)
            else:
                outside_sources.append((len(rules), parent))
                rules.append((1 << parent) | (1 << next_child))
            next_child += 1

    eligible = [parent for parent in range(old) if remaining[parent]]
    for restored in combinations(eligible, restored_count):
        capacity = remaining[:]
        for parent in restored:
            capacity[parent] -= 1
        white = ((1 << len(neighbors)) - 1) ^ sum(1 << parent for parent in restored)
        yield neighbors, rules, outside_sources, capacity, white, old


def completion_time(neighbors, rules, white, minimum):
    full = (1 << len(neighbors)) - 1
    elapsed = 0
    while white:
        added = 0
        for rule in rules:
            available = rule & white
            if available and not available & (available - 1):
                added |= available
        blue = full ^ white
        while blue:
            vertex = blue & -blue
            blue ^= vertex
            available = neighbors[vertex.bit_length() - 1] & white
            if available and not available & (available - 1):
                added |= available
        if not added:
            return 0
        white ^= added
        elapsed += 1
        if elapsed + white.bit_count() < minimum:
            return 0
    return elapsed


def enumerate_features(neighbors, rules, remaining, white, minimum, rank_budget, *, cubic=False):
    free = [v for v, capacity in enumerate(remaining) if capacity]
    free_white = [v for v in free if white & (1 << v)]
    features = {v: [] for v in free}
    for size in (1, 2, 3):
        for ends in combinations(free_white, size):
            features[ends[0]].append((False, ends, sum(1 << v for v in ends)))
    for left, right in combinations(free, 2):
        incident = (1 << left) | (1 << right)
        if white & incident and not neighbors[left] & (1 << right):
            features[left].append((True, (left, right), incident))

    fixed_start = any((rule & white).bit_count() == 1 for rule in rules)
    fixed_start |= any(not white & (1 << v) and (row & white).bit_count() == 1
                       for v, row in enumerate(neighbors))
    configurations = finishing = longest = 0

    def visit(index, first, possible_start, budget):
        nonlocal configurations, finishing, longest
        if index == len(free):
            if possible_start:
                configurations += 1
                elapsed = completion_time(neighbors, rules, white, minimum)
                if elapsed:
                    finishing += 1
                    longest = max(longest, elapsed)
            return

        # Every feature is picked at its least end with a growing index.
        vertex = free[index]
        if not cubic or not white & (1 << vertex) or not remaining[vertex]:
            visit(index + 1, 0, possible_start, budget)
        if not remaining[vertex]:
            return
        for choice, (direct, ends, mask) in enumerate(features[vertex][first:], first):
            cost = 1 if direct else len(ends) - 1
            if cost > budget or any(remaining[v] == 0 for v in ends):
                continue
            for end in ends:
                remaining[end] -= 1
            if direct:
                toggle_edge(neighbors, *ends)
            else:
                rules.append(mask)
            # Distinct blue vertices with the same white neighbors occupy
            # distinct degree slots, even though they force in the same round.
            next_choice = choice if cubic and not direct else choice + 1
            visit(index, next_choice, possible_start or (mask & white).bit_count() == 1,
                  budget - cost)
            if direct:
                toggle_edge(neighbors, *ends)
            else:
                rules.pop()
            for end in ends:
                remaining[end] += 1

    visit(0, 0, fixed_start, rank_budget)
    return configurations, finishing, longest


def enumerate_residuals(white_count, minimum, rank_budget=float('inf'), *, cubic=False):
    skeletons = configurations = finishing = longest = 0
    for neighbors, rules, outside_sources, remaining, white, old in templates(white_count):
        skeletons += 1

        def extend_sources(index, budget):
            nonlocal configurations, finishing, longest
            if index == len(outside_sources):
                count, success, elapsed = enumerate_features(
                    neighbors, rules, remaining, white, minimum, budget, cubic=cubic
                )
                configurations += count
                finishing += success
                longest = max(longest, elapsed)
                return
            extend_sources(index + 1, budget)
            if budget == 0:
                return
            rule_index, parent = outside_sources[index]
            for other in range(old):
                bit = 1 << other
                if other != parent and white & bit and remaining[other]:
                    remaining[other] -= 1
                    rules[rule_index] ^= bit
                    extend_sources(index + 1, budget - 1)
                    rules[rule_index] ^= bit
                    remaining[other] += 1

        extend_sources(0, rank_budget)
    return skeletons, configurations, finishing, longest


def check_subcubic_residuals():
    for whites, minimum, expected in (
        (10, 1, (10, 6176870, 5921708, 6)),
        (9, 7, (20, 5390980, 0, 0)),
        (8, 7, (57, 3470951, 1168, 7)),
        (7, 7, (95, 1535427, 0, 0)),
    ):
        observed = enumerate_residuals(whites, minimum)
        if observed != expected:
            raise AssertionError((whites, minimum, observed, expected))
        print(f'{whites} whites, at least {minimum} additional rounds: {observed}', flush=True)

    for rank, expected in ((2, (57, 427029, 0, 0)),
                           (3, (57, 1545781, 0, 0)),
                           (4, (57, 2907237, 1168, 7))):
        observed = enumerate_residuals(8, 7, rank)
        if observed != expected:
            raise AssertionError((rank, observed, expected))
        print(f'Eight whites, rank at most {rank}: {observed}', flush=True)


if __name__ == '__main__':
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--cubic-only', action='store_true', help='Check the eight-round cubic bound')
    if not parser.parse_args().cubic_only:
        check_subcubic_residuals()
    observed = enumerate_residuals(8, 7, cubic=True)
    if observed != (57, 770681, 0, 0):
        raise AssertionError(('eight degree-three whites', observed))
    print(f'Eight degree-three whites, at least seven additional rounds: {observed}', flush=True)
