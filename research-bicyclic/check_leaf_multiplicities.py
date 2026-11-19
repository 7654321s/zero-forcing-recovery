"""Check compressed direct-leaf attachments on positive and bounded bicyclic cores."""

import argparse
from functools import lru_cache
from itertools import combinations, combinations_with_replacement, permutations, product
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
SINGLE_SITE = runpy.run_path(str(HERE / 'check_single_site.py'))
THETA = SINGLE_SITE['THETA']
NEIGHBORS = THETA['TOOLS']['neighbors']


def automorphisms(adj):
    n = len(adj)
    for order in permutations(range(n)):
        if all((adj[i] >> j & 1) == (adj[order[i]] >> order[j] & 1)
               for i in range(n) for j in range(i + 1, n)):
            yield order


def expected_positive(name, counts):
    if name == 'bowtie':
        return not any(counts[1:])
    if name == 'theta122':
        return not any(counts[2:]) and (min(counts[:2]) == 0 or min(counts[:2]) == 2)
    return name in ('theta222', 'theta223') and not any(counts)


def find_pair(adj, mandatory):
    if not mandatory:
        return THETA['TOOLS']['find_size_two'](adj, THETA['completion_time'])

    infinity = len(adj) + 1
    optional = ((1 << len(adj)) - 1) ^ mandatory

    @lru_cache(maxsize=None)
    def time(blue):
        return THETA['completion_time'](adj, blue)

    for extra in THETA['SIMULATOR']['subsets'](optional):
        blue = mandatory | extra
        singles = {v: time(blue ^ (1 << v)) for v in NEIGHBORS(blue)}
        latest = max(singles.values())
        if latest == infinity:
            continue
        quick = [v for v, rounds in singles.items() if rounds < latest]
        for x, y in combinations(quick, 2):
            support = (1 << x) | (1 << y)
            if time(blue ^ support) == infinity:
                delayed = next(v for v, rounds in singles.items() if rounds == latest)
                return {'blue': blue, 'killing': support, 'slow': 1 << delayed,
                        'restricted_deadline': max(singles[x], singles[y]),
                        'slow_completion_time': latest}
    return None


def replay(adj, row, blue_extra=0):
    THETA['certify'](adj, row['blue'] | blue_extra, row['killing'], row['slow'],
                    row['restricted_deadline'], row['slow_completion_time'])


def check_core(name, core, expand=True):
    perms = list(automorphisms(core))
    positive = negative = expanded = 0
    for counts in product(range(3), repeat=len(core)):
        if any(tuple(counts[v] for v in perm) < counts for perm in perms):
            continue

        adj = list(core)
        mandatory = 0
        for v, amount in enumerate(counts):
            new = THETA['append_leaves'](adj, v, amount)
            if amount == 2:
                mandatory |= THETA['mask'](new)

        if expected_positive(name, counts):
            result, error, _, _ = THETA['every_minimum_support'](adj)
            if not result:
                raise AssertionError((name, counts, error))
            positive += 1
            continue

        row = find_pair(adj, mandatory)
        if row is None:
            raise AssertionError(f'No budget-one certificate for {name} with leaf counts {counts}')
        replay(adj, row)
        negative += 1

        if not expand:
            continue
        blue_extra = 0
        for v, amount in enumerate(counts):
            if amount == 2:
                blue_extra |= THETA['mask'](THETA['append_leaves'](adj, v, 2 + v % 3))
        if blue_extra:
            replay(adj, row, blue_extra)
            expanded += 1
    return positive, negative, expanded


def negative_bicyclic_cores(max_order):
    for lengths in combinations_with_replacement(range(1, max_order), 3):
        if lengths[1] >= 2 and sum(lengths) <= max_order + 1 and lengths not in THETA['POSITIVE_CORES']:
            yield f'theta{lengths}', THETA['theta'](lengths)[0]

    two_cycles = SINGLE_SITE['TWO_CYCLES']
    for p, q in combinations_with_replacement(range(3, max_order), 2):
        if p + q - 1 <= max_order and (p, q) != (3, 3):
            yield f'shared{p, q}', two_cycles['graph'](p, q, True)[0]
        for length in range(1, max_order + 2 - p - q):
            yield f'path{p, q, length}', two_cycles['graph'](p, q, False, length)[0]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-negative-core-order', type=int, default=8)
    args = parser.parse_args()
    if args.max_negative_core_order < 4:
        parser.error('--max-negative-core-order must be at least 4')
    all_positive = all_negative = all_expanded = 0
    for name, core in SINGLE_SITE['cores']().items():
        positive, negative, expanded = check_core(name, core)
        print(name, 'positive:', positive, 'negative:', negative, 'expanded:', expanded)
        all_positive += positive
        all_negative += negative
        all_expanded += expanded
    print('Total compressed configurations on positive cores:', all_positive + all_negative, flush=True)
    print('Larger certificate replays:', all_expanded, flush=True)

    core_count = cert_count = 0
    for name, core in negative_bicyclic_cores(args.max_negative_core_order):
        _, negative, _ = check_core(name, core, expand=False)
        core_count += 1
        cert_count += negative
    print(f'Negative cores through order {args.max_negative_core_order}: {core_count}', flush=True)
    print('Compressed negative-core certificates:', cert_count, flush=True)


if __name__ == '__main__':
    main()
