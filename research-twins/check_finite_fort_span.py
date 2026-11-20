"""Verify the minimum span of a finite fort in the signed prism lift."""

import argparse
from itertools import combinations
from pathlib import Path
import runpy

from pysat.card import ITotalizer
from pysat.solvers import Solver


COVER = runpy.run_path(str(Path(__file__).with_name('check_cyclic_cover_saturation.py')))
mask, members = COVER['mask'], COVER['members']
BAND = runpy.run_path(str(Path(__file__).with_name('check_block_stabilization.py')))
FRONTIERS = {
    2: (4, (22, 18, 16)),
    3: (5, (27, 23, 22, 21)),
    4: (5, (41, 34, 24)),
    5: (6, (42, 24)),
}


def guarded_strip(blocks, span):
    sheets = span + 2
    graph, seeds, _, _ = COVER['signed_prism_cover'](blocks, sheets)
    guards = mask(v for v in range(len(graph)) if v % sheets in (0, sheets - 1))
    return graph, seeds, guards


def arrival_from_guards(blocks, span):
    graph, _, guards = guarded_strip(blocks, span)
    return COVER['MODEL']['trace'](graph, guards)[1]


def verify_timetable(graph, guards, times):
    if len(times) != len(graph) or mask(v for v, t in enumerate(times) if not t) != guards:
        raise AssertionError('Incorrect time-zero sheets')
    for v, deadline in enumerate(times):
        if deadline and not any(times[u] < deadline
                                and all(times[w] < deadline for w in members(graph[u] ^ (1 << v)))
                                for u in members(graph[v])):
            raise AssertionError(('No force by the assigned round', v, deadline))


def check_repeated_timetable():
    # Stage zero has 18 labels. Each appended stage has 16 labels.
    reference = arrival_from_guards(12, 6)
    if None in reference or max(reference) != 51:
        raise AssertionError('The six interior sheets do not fill by round 51')
    prefix = reference[:18 * 8]
    stages = [reference[i:i + 16 * 8] for i in range(18 * 8, len(reference), 16 * 8)]
    first = stages[0]
    bulk = stages[1]
    if len(stages) != 11 or stages[1:6] != [bulk] * 5:
        raise AssertionError('Bulk timetable does not repeat')
    suffix = [time for stage in stages[6:] for time in stage]
    for blocks in (12, 13):
        graph, _, guards = guarded_strip(blocks, 6)
        timetable = [*prefix, *first, *(bulk * (blocks - 7)), *suffix]
        verify_timetable(graph, guards, timetable)


def check_minimum_spans():
    # When the guards force the graph, no fort fits between them.
    for blocks, (span, _) in FRONTIERS.items():
        if None in arrival_from_guards(blocks, span - 1):
            raise AssertionError(('A fort fits in a smaller strip', blocks, span))
        graph, seeds, _ = guarded_strip(blocks, span)
        times = arrival_from_guards(blocks, span)
        white = mask(v for v, t in enumerate(times) if t is None)
        COVER['fort_cost'](graph, seeds, white)
        print(f'{blocks} blocks: minimum span {span} sheets')
    for blocks in range(6, 12):
        if None in arrival_from_guards(blocks, 6):
            raise AssertionError(('A fort fits in six sheets', blocks))
    check_repeated_timetable()

    # The common witness occupies all seven interior sheets and keeps both guards empty.
    graph, seeds, guards = guarded_strip(6, 7)
    witness = mask(v * 9 + sheet for v, sheet in COVER['FOUR_BLOCK_FORT'])
    occupied = {v % 9 for v in members(witness)}
    if witness & guards or occupied != set(range(1, 8)) or COVER['fort_cost'](graph, seeds, witness) != 24:
        raise AssertionError('Invalid seven-sheet witness')
    print('At least six blocks: minimum span seven sheets, with a common cost-24 witness')


def check_seed_frontiers():
    for blocks, (first, costs) in FRONTIERS.items():
        for span, expected in enumerate(costs, first):
            graph, seeds, guards = guarded_strip(blocks, span)
            interior = [v + 1 for v in range(len(graph)) if not (guards >> v) & 1]
            seed_vars = [v + 1 for v in members(seeds & ~guards)]
            clauses = list(BAND['fort_clauses'](graph, range(len(graph))))
            clauses.append(interior)
            clauses.extend([-(v + 1)] for v in members(guards))
            with ITotalizer(lits=seed_vars, ubound=expected, top_id=len(graph)) as counter:
                with Solver(name='cadical195', bootstrap_with=clauses + counter.cnf.clauses) as solver:
                    if solver.solve(assumptions=[-counter.rhs[expected - 1]]):
                        raise AssertionError(('A cheaper fort fits inside the span', blocks, span))
                    if not solver.solve(assumptions=[-counter.rhs[expected]]):
                        raise AssertionError(('Missing witness', blocks, span, expected))
                    witness = mask(v - 1 for v in solver.get_model() if 0 < v <= len(graph))
                    if witness & guards or COVER['fort_cost'](graph, seeds, witness) != expected:
                        raise AssertionError(('Incorrect witness', blocks, span))
        print(f'{blocks} blocks: minimum seed costs {costs} from span {first}')


def check_seed_families(blocks, span, shapes, expected):
    # Four sheets on either side suffice for two rounds of intact dependence.
    sheets = 19
    graph, seeds, _, _ = COVER['signed_prism_cover'](blocks, sheets)
    families = {}
    for shape in shapes:
        coordinates = (divmod(v, span + 2) for v in members(shape))
        fort = mask(v * sheets + s + 4 for v, s in coordinates)
        families.setdefault(fort & seeds, []).append(fort)

    observed = []
    for lost, family in families.items():
        times = COVER['MODEL']['trace'](graph, seeds & ~lost)[1]
        maximal = mask(v for v, t in enumerate(times) if t is None)
        if maximal not in family:
            raise AssertionError(('Closure outside the listed family', blocks, span))
        minimal = [fort for fort in family
                   if all(other == fort or (other & fort) != other for other in family)]
        if len(minimal) != 1:
            raise AssertionError(('Unexpected inclusion-minimal forts', blocks, span))
        observed.append((len(family), minimal[0].bit_count(), maximal.bit_count()))
    if tuple(sorted(observed)) != expected:
        raise AssertionError(('Unexpected seed-family statistics', blocks, span, observed))


def check_guarded_shapes(blocks, span, shapes, expected_families):
    sheets = span + 2
    graph, seeds, guards = guarded_strip(blocks, span)
    times = COVER['MODEL']['trace'](graph, guards)[1]
    outside = mask(v for v, t in enumerate(times) if t is not None)
    for fort in shapes:
        if fort & outside or COVER['fort_cost'](graph, seeds, fort) != 24:
            raise AssertionError(('Invalid minimum-cost fort', blocks, span))
        occupied = {v % sheets for v in members(fort)}
        if min(occupied) != 1 or max(occupied) != span:
            raise AssertionError(('Incorrect witness span', blocks, span))
        seed_sheets = {v % sheets for v in members(fort & seeds)}
        if min(seed_sheets) != 1 or max(seed_sheets) != span:
            raise AssertionError(('Incorrect seed-set span', blocks, span))

    free = [v + 1 for v in range(len(graph)) if not outside & (1 << v)]
    clauses = list(BAND['fort_clauses'](graph, range(len(graph))))
    clauses.extend([-(v + 1)] for v in members(outside))
    clauses.extend([v for v in free if (v - 1) % sheets == sheet] for sheet in (1, span))
    for fort in shapes:
        clauses.append([-v if fort & (1 << (v - 1)) else v for v in free])
    with ITotalizer(lits=[v + 1 for v in members(seeds & ~outside)], ubound=24,
                    top_id=len(graph)) as counter:
        with Solver(name='cadical195', bootstrap_with=clauses + counter.cnf.clauses) as solver:
            if solver.solve(assumptions=[-counter.rhs[24]]):
                raise AssertionError(('An additional minimum-cost fort exists', blocks, span))
    check_seed_families(blocks, span, shapes, expected_families)


def check_shortest_minimum_cost_forts():
    for blocks in (27, 28):
        BAND['check_band'](blocks, stages=26, budget=24)

    common = mask(v * 9 + s for v, s in COVER['FOUR_BLOCK_FORT'])
    removed = mask(v * 9 + 4 for v in (43, 44))
    if common & removed != removed or common.bit_count() != 46:
        raise AssertionError('Unexpected common fort')
    shapes = (common ^ removed, common)
    for blocks in range(4, 28):
        check_guarded_shapes(blocks, 7, shapes, ((2, 44, 46),))
    print('Exactly two cost-24 forts of span seven at every length from four blocks')


# These coordinates are relative to the beginning of the penultimate stage.
TAIL_COMMON = (
    (3, 5), (4, 1), (4, 2), (5, 2), (5, 3), (6, 3), (6, 4), (7, 4),
    (9, 3), (9, 4), (10, 3), (10, 4), (11, 4), (11, 5), (12, 4), (13, 5),
    (15, 6), (16, 5), (17, 3), (17, 4), (17, 6), (18, 6), (19, 6), (21, 3),
    (21, 6), (22, 3), (22, 5), (22, 6), (25, 6), (26, 5), (26, 6), (27, 5),
    (27, 6), (28, 5), (29, 5), (30, 5), (30, 6), (30, 8), (31, 5), (31, 8),
)
TAIL_OPTIONAL = ((9, 5), (20, 5), (21, 4), (22, 4), (23, 4), (23, 5),
                 (24, 5), (25, 4), (25, 5))


def patterns_from_optional_vertices(span, start, common, optional):
    graph, seeds, _ = guarded_strip(4, span)
    sheets = span + 2
    patterns = []
    supports = set()
    for length in range(len(optional) + 1):
        for included in combinations(optional, length):
            coordinates = common + included
            fort = mask((v + start) * sheets + s for v, s in coordinates)
            try:
                cost = COVER['fort_cost'](graph, seeds, fort)
            except AssertionError:
                continue
            if cost == 24:
                patterns.append(coordinates)
                supports.add(fort & seeds)
    return patterns, supports


def check_eight_sheet_forts():
    start = BAND['stage_start'](2)
    patterns, supports = patterns_from_optional_vertices(8, start, TAIL_COMMON, TAIL_OPTIONAL)
    if len(patterns) != 40 or len(supports) != 2:
        raise AssertionError('Unexpected eight-sheet terminal patterns')
    if {len(pattern) for pattern in patterns} != set(range(42, 48)):
        raise AssertionError('Unexpected sizes of eight-sheet forts')

    for blocks in range(4, 28):
        start = BAND['stage_start'](blocks - 2)
        shapes = [mask((v + start) * 10 + s for v, s in pattern) for pattern in patterns]
        check_guarded_shapes(blocks, 8, shapes, ((8, 44, 47), (32, 42, 47)))
    print('Exactly 40 cost-24 forts of span eight, with two seed sets, at every length from four blocks')


OPENING_NINE_COMMON = (
    (0, 1), (0, 2), (3, 1), (3, 2), (5, 3), (6, 2), (6, 3), (7, 2),
    (9, 3), (9, 4), (12, 2), (14, 3), (15, 3), (15, 4), (21, 5), (22, 2),
    (25, 5), (26, 4), (26, 5), (27, 4), (27, 5), (28, 4), (29, 5), (31, 5),
    (33, 7), (35, 4), (35, 7), (36, 7), (38, 5), (38, 6), (39, 4), (39, 5),
    (39, 7), (40, 4), (40, 5), (40, 6), (41, 5), (41, 6), (42, 7), (43, 5),
    (43, 6), (44, 5), (44, 6), (45, 6), (47, 8), (48, 6), (48, 9), (49, 6),
)
OPENING_NINE_OPTIONAL = ((2, 2), (4, 1), (36, 5), (42, 6), (43, 7), (44, 7), (49, 8))


def check_nine_sheet_forts():
    patterns, supports = patterns_from_optional_vertices(9, 0, OPENING_NINE_COMMON,
                                                       OPENING_NINE_OPTIONAL)
    if len(patterns) != 12 or len(supports) != 2:
        raise AssertionError('Unexpected nine-sheet opening patterns')
    if {len(pattern) for pattern in patterns} != set(range(50, 55)):
        raise AssertionError('Unexpected sizes of nine-sheet forts')

    shapes = [mask(v * 11 + s for v, s in pattern) for pattern in patterns]
    for blocks in range(4, 28):
        check_guarded_shapes(blocks, 9, shapes, ((4, 51, 53), (8, 50, 54)))
    print('Exactly 12 cost-24 forts of span nine, with two seed sets, at every length from four blocks')


def check_larger_optimal_spans(lengths):
    strip = runpy.run_path(str(Path(__file__).with_name('check_finite_fort_strip.py')))
    sheets = 34
    budget = 24
    for blocks in lengths:
        graph, blue, *_ = COVER['signed_prism_cover'](blocks, sheets)
        clauses, seeds, top = strip['strip_formula'](graph, blue, budget, sheets=sheets,
                                                    quotient_bounds=False, require_minimal=False)
        clauses.append([v + 1 for v in range(len(graph)) if 10 <= v % sheets < sheets - 1])
        with ITotalizer(lits=seeds, ubound=budget, top_id=top) as counter:
            with Solver(name='cadical195', bootstrap_with=clauses + counter.cnf.clauses) as solver:
                if solver.solve(assumptions=[-counter.rhs[budget]]):
                    raise AssertionError(('A cost-24 fort spans at least ten sheets', blocks))
        print(f'{blocks} blocks: every cost-24 fort spans at most nine sheets', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--longer', type=int, nargs='+', choices=range(4, 12), default=(),
                        help='also replay the exclusions at spans ten through thirty-two')
    args = parser.parse_args()
    check_minimum_spans()
    check_seed_frontiers()
    check_shortest_minimum_cost_forts()
    check_eight_sheet_forts()
    check_nine_sheet_forts()
    print('Checked the five seed families with their unique minimal forts and forced closures')
    if args.longer:
        check_larger_optimal_spans(args.longer)
