"""Replay twin truncation, the one-singleton criterion and complete multipartite positives."""

from itertools import combinations, combinations_with_replacement, product
from pathlib import Path
import runpy


ROOT = Path(__file__).resolve().parents[1]
LEAVES = runpy.run_path(str(ROOT / 'research-bicyclic' / 'check_leaf_multiplicities.py'))
MODEL = LEAVES['THETA']
members = MODEL['TOOLS']['neighbors']
mask = MODEL['mask']
completion_time = MODEL['completion_time']
exhaustive = MODEL['every_minimum_support']


def twins(adj, x, y):
    exterior = ~((1 << x) | (1 << y))
    return (adj[x] ^ adj[y]) & exterior == 0


def twin_classes(adj):
    classes = []
    for v in range(len(adj)):
        for group in classes:
            if twins(adj, v, group[0]):
                group.append(v)
                break
        else:
            classes.append([v])
    return classes


def truncate(adj, classes):
    retained = [v for group in classes for v in group[:2]]
    indices = {v: i for i, v in enumerate(retained)}
    mandatory = mask(indices[v] for group in classes if len(group) >= 2 for v in group[:2])
    reduced = [mask(indices[w] for w in members(adj[v]) if w in indices) for v in retained]
    return reduced, retained, mandatory


def external_neighborhoods_incomparable(adj, x, v):
    exterior = ~((1 << x) | (1 << v))
    return bool(adj[x] & ~adj[v] & exterior) and bool(adj[v] & ~adj[x] & exterior)


def blowup(edges, counts, cliques):
    """Replace a vertex by a clique or an independent set, keeping all cross edges."""
    origins = [v for v, size in enumerate(counts) for _ in range(size)]
    adj = [0] * len(origins)
    for u, v in combinations(range(len(origins)), 2):
        x, y = origins[u], origins[v]
        if (x == y and cliques[x]) or (x, y) in edges:
            adj[u] |= 1 << v
            adj[v] |= 1 << u
    return adj


def small_blowups():
    for n in range(1, 4):
        possible = list(combinations(range(n), 2))
        for edge_mask in range(1 << len(possible)):
            edges = {possible[i] for i in members(edge_mask)}
            for counts in product((1, 2, 3), repeat=n):
                if 3 in counts:
                    for cliques in product((False, True), repeat=n):
                        yield blowup(edges, counts, cliques)


def check_projection(adj, reduced, retained, mandatory, extra):
    def lift(blue):
        return mask(retained[v] for v in members(blue))

    optional = ((1 << len(reduced)) - 1) ^ mandatory
    count = 0
    for part in MODEL['SIMULATOR']['subsets'](optional):
        blue = mandatory | part
        enlarged_blue = lift(blue) | extra
        vertices = list(members(blue))
        for size in range(3):
            for loss in combinations(vertices, size):
                reduced_time = completion_time(reduced, blue ^ mask(loss))
                full_time = completion_time(adj, enlarged_blue ^ mask(retained[v] for v in loss))
                if reduced_time > len(reduced):
                    if full_time <= len(adj):
                        raise AssertionError((adj, blue, loss, reduced_time, full_time))
                elif reduced_time != full_time:
                    raise AssertionError((adj, blue, loss, reduced_time, full_time))
                count += 1
    return count


def check_small_blowups():
    cases = states = negative = singletons = 0
    for adj in small_blowups():
        classes = twin_classes(adj)
        reduced, retained, mandatory = truncate(adj, classes)
        extra = ((1 << len(adj)) - 1) ^ mask(retained)
        positive = exhaustive(adj)[0]
        if positive != exhaustive(reduced)[0]:
            raise AssertionError((adj, reduced))
        states += check_projection(adj, reduced, retained, mandatory, extra)
        row = LEAVES['find_pair'](reduced, mandatory)
        if positive != (row is None):
            raise AssertionError((adj, reduced, positive, row))
        if row is not None:
            blue, support, slow = (mask(retained[i] for i in members(row[field]))
                                   for field in ('blue', 'killing', 'slow'))
            MODEL['certify'](adj, blue | extra, support, slow,
                             row['restricted_deadline'], row['slow_completion_time'])
            negative += 1

        single = [group[0] for group in classes if len(group) == 1]
        if len(single) == 1 and all(adj):
            x, = single
            kinds = {external_neighborhoods_incomparable(adj, x, v)
                     for v in range(len(adj)) if v != x}
            if positive != (len(kinds) == 1):
                raise AssertionError((adj, x, kinds, positive))
            singletons += 1
        cases += 1
    return cases, states, negative, singletons


def check_multipartite():
    count = 0
    for parts in range(1, 5):
        edges = set(combinations(range(parts), 2))
        for sizes in combinations_with_replacement(range(1, 5), parts):
            if sum(sizes) <= 10:
                if not exhaustive(blowup(edges, sizes, (False,) * parts))[0]:
                    raise AssertionError(sizes)
                count += 1
    return count


def main():
    cases, states, negative, singletons = check_small_blowups()
    print('Twin truncation comparisons:', cases, flush=True)
    print('Exact projected loss states:', states, flush=True)
    print('Lifted counterexamples:', negative, flush=True)
    print('One-singleton comparisons:', singletons, flush=True)
    print('Complete multipartite positives:', check_multipartite(), flush=True)


if __name__ == '__main__':
    main()
