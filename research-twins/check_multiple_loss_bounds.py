"""Replay extremal recovery examples for several lost initial blue vertices."""

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


def protect_seeds(degree, edges, blue, order, deliberately_lost, seed):
    """Add private blue paths and a connected minimum killing support."""
    losses = len(deliberately_lost)
    support = range(order, order + losses + 1)
    order = support.stop
    support_pairs = combinations(support, 2) if losses <= degree else pairwise(support)
    attachment = order
    for left, right in support_pairs:
        edges.extend(((order, left), (order, right)))
        blue.append(order)
        order += 1
    edges.append((seed, attachment))

    paths = []
    unprotected = set(deliberately_lost)
    for vertex in blue[:]:
        if vertex not in unprotected:
            path = range(order, order + 2 * losses + 2)
            edges.append((vertex, path[0]))
            edges.extend(pairwise(path))
            blue.extend(path)
            paths.append(tuple(path))
            order = path.stop
    return adjacency(order, edges), mask([*blue, *support]), mask(support), paths


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


def one_round_block(degree, roots, edges, blue, order):
    targets = []
    if len(roots) == 2:
        pairs = [tuple(roots)] * (degree - 2)
    elif len(roots) == 3:
        count, parity = divmod(degree - 2, 2)
        a, b, c = roots
        pairs = [(a, b)] * count + [(a, c), (b, c)] * (count + parity)
    else:
        pairs = []

    for left, right in pairs:
        source, target = order, order + 1
        order += 2
        edges.extend(((source, left), (source, right), (source, target)))
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
        order, targets, tail = one_round_block(degree, group, edges, blue, order)
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


def check_robust_samples(graph, blue, slow, support, paths, degree, rounds, losses):
    check_connected(graph, degree)
    if completion_time(graph, blue) != rounds or completion_time(graph, blue ^ support) <= len(graph):
        raise AssertionError(('intact or killing time', degree, rounds, losses))
    support_time = max(completion_time(graph, blue ^ support ^ (1 << retained))
                       for retained in members(support))
    expected = rounds if losses <= degree else max(rounds, losses)
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


def main():
    exhaustive = sampled = 0
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

    for d, k in ((4, 2), (4, 5), (5, 3), (6, 2), (7, 3), (8, 2), (6, 7)):
        graph, blue, slow, support, paths = two_round_certificate(d, k)
        sampled += check_robust_samples(graph, blue, slow, support, paths, d, 2, k)
        expected = 2 + k * (SINGLE['quadratic_degree_time'](d) - 2)
        upper = 2 + (13 * k if d == 4 else k * (d**2 + 11) // 2)
        if completion_time(graph, blue ^ slow) != expected or expected > upper:
            raise AssertionError(('concatenated two-round delay', d, k, expected, upper))
        print('Concatenated two-round family:', d, k, len(graph), expected, upper)

    print('Exhaustive losses on the degree-two and small one-round examples:', exhaustive)
    print('Recoverable losses checked against the cycle upper bound:', check_small_cycles())
    print('Recoverable losses checked against the subcubic one-round bound:',
          check_small_subcubic_one_round())
    print('Sampled losses on the protected examples:', sampled)


if __name__ == '__main__':
    main()
