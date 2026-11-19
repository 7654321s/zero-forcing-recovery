"""Enumerate all subcubic round-two residual rules when ten vertices are white."""

from itertools import combinations


# For each round-one branch, the second child is either forced directly
# by its parent or via a permanently blue source, like the first child.
def templates():
    for lost_is_source in (False, True):
        for self_count in range(4 if not lost_is_source else 3):
            for lost_target_self in ((False, True) if lost_is_source else (False,)):
                self_targets = [False] * (3 - self_count) + [True] * self_count
                if lost_is_source:
                    self_targets[0] = lost_target_self
                yield lost_is_source, self_targets


def completion_time(neighbors, blue_rules):
    white = (1 << len(neighbors)) - 1
    elapsed = 0
    while white:
        added = 0
        for rule in blue_rules:
            available = rule & white
            if available and not available & (available - 1):
                added |= available
        blue = ((1 << len(neighbors)) - 1) ^ white
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
    return elapsed


def enumerate_residuals():
    # 0 is the lost vertex. 1..3 are its three missed round-one targets,
    # with 1 its own target if it acted. Each parent has two labeled children.
    children = range(4, 10)
    features_by_first = [[] for _ in range(10)]
    for size in range(1, 4):
        for ends in combinations(children, size):
            mask = sum(1 << end for end in ends)
            features_by_first[ends[0]].append((False, ends, mask))
            if size == 2:
                features_by_first[ends[0]].append((True, ends, mask))
    counts = []
    max_time = 0
    for lost_is_source, self_targets in templates():
        neighbors = [0] * 10
        blue_rules = []
        for parent, self_target in enumerate(self_targets, 1):
            first, second = 2 * parent + 2, 2 * parent + 3
            if lost_is_source and parent == 1:
                neighbors[0] |= 1 << parent
                neighbors[parent] |= 1
            else:
                blue_rules.append(1 | (1 << parent))
            blue_rules.append((1 << parent) | (1 << first))
            if self_target:
                neighbors[parent] |= 1 << second
                neighbors[second] |= 1 << parent
            else:
                blue_rules.append((1 << parent) | (1 << second))
        counts.append(enumerate_template(neighbors, blue_rules, features_by_first))
        max_time = max(max_time, counts[-1][2])
        print(lost_is_source, self_targets, counts[-1], flush=True)
    return sum(count for count, _, _ in counts), sum(success for _, success, _ in counts), max_time


def enumerate_template(neighbors, blue_rules, features_by_first):
    remaining = [0] * 4 + [2] * 6
    count = success = max_time = 0

    def visit(first, start, has_singleton):
        nonlocal count, success, max_time
        if first == 10:
            if has_singleton:
                count += 1
                elapsed = completion_time(neighbors, blue_rules)
                if elapsed:
                    success += 1
                    max_time = max(max_time, elapsed)
            return
        # Finish this vertex, or add another feature whose least end is here.
        # Increasing the choice index avoids enumerating repeated rules.
        visit(first + 1, 0, has_singleton)
        if remaining[first] == 0:
            return
        choices = features_by_first[first]
        for i in range(start, len(choices)):
            direct, ends, mask = choices[i]
            if any(remaining[end] == 0 for end in ends):
                continue
            for end in ends:
                remaining[end] -= 1
            if direct:
                left, right = ends
                neighbors[left] ^= 1 << right
                neighbors[right] ^= 1 << left
            else:
                blue_rules.append(mask)
            visit(first, i + 1, has_singleton or len(ends) == 1)
            if direct:
                neighbors[left] ^= 1 << right
                neighbors[right] ^= 1 << left
            else:
                blue_rules.pop()
            for end in ends:
                remaining[end] += 1

    visit(4, 0, False)
    return count, success, max_time


if __name__ == '__main__':
    observed = enumerate_residuals()
    expected = (6176870, 5921708, 6)
    if observed != expected:
        raise AssertionError((observed, expected))
    print('Configurations, finishing runs, maximum additional rounds:', observed)
