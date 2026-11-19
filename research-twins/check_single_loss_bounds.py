"""Replay the sharp single-loss time bounds and the unbounded two-round family."""

from itertools import combinations, product
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


def check_discrepancy_growth():
    transitions = 0
    for n in range(1, 6):
        possible = list(combinations(range(n), 2))
        for edge_mask in range(1 << len(possible)):
            adj = adjacency(n, (possible[i] for i in members(edge_mask)))
            degrees = [row.bit_count() for row in adj]
            traces = [trace(adj, blue) for blue in range(1 << n)]
            for blue, (intact, full_arrivals) in enumerate(traces):
                if intact > n:
                    continue
                for lost in members(blue):
                    _, delayed_arrivals = traces[blue ^ (1 << lost)]
                    differences = {lost}
                    for round_number in range(1, intact + 1):
                        next_differences = {v for v in range(n) if full_arrivals[v] <= round_number
                                            and (delayed_arrivals[v] is None
                                                 or delayed_arrivals[v] > round_number)}
                        bound = sum(degrees[v] + (v == lost) for v in differences)
                        if len(next_differences) > bound:
                            raise AssertionError((adj, blue, lost, round_number, bound))
                        differences = next_differences
                        transitions += 1
    return transitions


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


def main():
    extremal_examples()
    print('Sharp one-round examples: two certificates at times 1/5 and 1/4')
    print('Unbounded two-round family:', check_two_round_family(), 'certificates')
    cases, paired_cases = check_small_graphs()
    print('Recoverable singleton cases through graph order five:', cases)
    print('Cases with a retained twin:', paired_cases)
    print('Discrepancy growth transitions:', check_discrepancy_growth())
    check_subcubic_example()
    print('Subcubic example: exact restricted time 2 and delayed time 7')


if __name__ == '__main__':
    main()
