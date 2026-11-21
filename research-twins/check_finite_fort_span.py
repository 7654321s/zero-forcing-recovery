"""Verify the minimum span of a finite fort in the signed prism lift."""

import argparse
from collections import Counter
from itertools import combinations
from pathlib import Path
import runpy

from pysat.card import ITotalizer
from pysat.solvers import Solver


COVER = runpy.run_path(str(Path(__file__).with_name('check_cyclic_cover_saturation.py')))
mask, members = COVER['mask'], COVER['members']
BAND = runpy.run_path(str(Path(__file__).with_name('check_block_stabilization.py')))
ORDINARY_BLOCKER = (
    (3, (5,)), (4, (1,)), (5, (2, 3)), (12, (4,)),
    (13, (5,)), (16, (5,)), (17, (3, 6)), (19, (6,)),
    (20, (4, 5)), (21, (3,)), (30, (5, 8)), (31, (5, 9)),
    (33, (6, 9)), (34, (5, 9)), (35, (7,)), (36, (7, 8)),
    (37, (6, 7, 9)), (45, (10,)), (46, (11,)), (47, (10,)),
)
ORDINARY_PACKING_LOSS = (
    (3, (5,)), (4, (1,)), (5, (2, 3)), (12, (4,)), (13, (5,)), (15, (6,)),
    (16, (5,)), (17, (3, 5, 6)), (18, (6,)), (21, (3, 4, 6)), (28, (5,)),
    (30, (5, 8)), (31, (5, 8)), (33, (7, 8)), (34, (8,)), (35, (7,)),
    (36, (7,)), (37, (7, 8)), (45, (9,)), (46, (9, 10)),
)
ORDINARY_INCIDENCE_LOSS = (
    (3, (5,)), (4, (1,)), (5, (2, 3)), (12, (4,)), (13, (5,)), (16, (5,)),
    (17, (3, 6)), (19, (6,)), (20, (4,)), (21, (3,)), (28, (6,)),
    (30, (5, 8)), (31, (5, 9)), (33, (6, 9)), (34, (5, 9)), (35, (7,)),
    (36, (7, 8)), (37, (6, 9)), (45, (8, 10)), (46, (11,)), (47, (10,)),
)
ORDINARY_SURVIVOR_PERIOD = 128
# Bit y of a label's mask keeps that seed on sheet phase y.
ORDINARY_SURVIVOR_MASKS = (
    (0, 0x00020000000800200000000007600000),
    (1, 0x00040000001000400000000009810000),
    (2, 0x0c504024220443126800100000001106),
    (3, 0x001000000000000000000000aa020000),
    (4, 0x90c2408006904a5002a1110504510010),
    (5, 0x8022a90a902800008212001141a4ae08),
    (12, 0x00000000000000000000001244c00000),
    (13, 0x00000100010640000052180034308120),
    (14, 0x48005145000010344202840148000081),
    (15, 0x0000000000000000000000000a000000),
)
FRONTIERS = {
    2: (4, (22, 18, 16)),
    3: (5, (27, 23, 22, 21)),
    4: (5, (41, 34, 24)),
    5: (6, (42, 24)),
}
RESTORATION_PROFILES = {
    (7, 2): ((6, 2), (7, 3), (8, 4), (9, 3), (10, 1), (11, 1), (12, 2),
             (13, 5), (14, 3)),
    (8, 8): ((7, 3), (8, 4), (9, 2), (10, 5), (11, 2), (12, 1), (13, 4),
             (14, 2), (17, 1)),
    (8, 32): ((7, 3), (8, 4), (9, 2), (10, 4), (11, 5), (12, 1), (13, 3), (14, 2)),
    (9, 4): ((7, 2), (8, 1), (9, 1), (10, 1), (11, 4), (12, 2), (13, 3),
             (14, 5), (15, 3), (16, 1), (17, 1)),
    (9, 8): ((8, 3), (9, 1), (10, 1), (11, 4), (12, 1), (13, 4), (14, 4),
             (15, 4), (16, 1), (17, 1)),
}
ADDITIONAL_BLOCKER = (
    (0, 1), (0, 2), (9, 4), (10, 2), (11, 2), (15, 4), (18, 3), (20, 2),
    (22, 2), (23, 3), (23, 4), (32, 5), (33, 7), (35, 4), (35, 7), (36, 5),
    (36, 7), (37, 5), (38, 5), (38, 6), (39, 4), (39, 5), (39, 7), (47, 8),
    (48, 9),
)


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


def restoration_profile(graph, seeds, lost):
    counts = Counter()
    surviving = seeds & ~lost
    for restored in members(lost):
        arrival = COVER['MODEL']['trace'](graph, surviving | (1 << restored))[1]
        if None in arrival:
            raise AssertionError(('Restoring a seed leaves an obstruction', restored))
        counts[max(arrival)] += 1
    return tuple(sorted(counts.items()))


def check_seed_families(blocks, span, shapes, expected, *, restoration_times=False):
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
        least = minimal[0]
        groups = {}
        for v in members(maximal ^ least):
            signature = tuple(bool(fort & (1 << v)) for fort in family)
            groups[signature] = groups.get(signature, 0) + 1
        sizes = tuple(sorted(groups.values()))
        if len(family) != 2 ** len(sizes):
            raise AssertionError(('Missing a combination of optional groups', blocks, span))
        observed.append((len(family), least.bit_count(), maximal.bit_count(), sizes))
        if restoration_times and blocks <= 20:
            observed_profile = restoration_profile(graph, seeds, lost)
            if observed_profile != RESTORATION_PROFILES[span, len(family)]:
                raise AssertionError(('Unexpected restoration times', blocks, span, observed_profile))
    if tuple(sorted(observed)) != expected:
        raise AssertionError(('Unexpected seed-family statistics', blocks, span, observed))


def check_guarded_shapes(blocks, span, shapes, expected_families, *, restoration_times=False):
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
    check_seed_families(blocks, span, shapes, expected_families,
                        restoration_times=restoration_times)


def check_shortest_minimum_cost_forts(*, restoration_times=False):
    for blocks in (27, 28):
        BAND['check_band'](blocks, stages=26, budget=24)

    common = mask(v * 9 + s for v, s in COVER['FOUR_BLOCK_FORT'])
    removed = mask(v * 9 + 4 for v in (43, 44))
    if common & removed != removed or common.bit_count() != 46:
        raise AssertionError('Unexpected common fort')
    shapes = (common ^ removed, common)
    for blocks in range(4, 28):
        check_guarded_shapes(blocks, 7, shapes, ((2, 44, 46, (2,)),),
                             restoration_times=restoration_times)
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


def check_eight_sheet_forts(*, restoration_times=False):
    start = BAND['stage_start'](2)
    patterns, supports = patterns_from_optional_vertices(8, start, TAIL_COMMON, TAIL_OPTIONAL)
    if len(patterns) != 40 or len(supports) != 2:
        raise AssertionError('Unexpected eight-sheet terminal patterns')
    if {len(pattern) for pattern in patterns} != set(range(42, 48)):
        raise AssertionError('Unexpected sizes of eight-sheet forts')

    for blocks in range(4, 28):
        start = BAND['stage_start'](blocks - 2)
        shapes = [mask((v + start) * 10 + s for v, s in pattern) for pattern in patterns]
        check_guarded_shapes(blocks, 8, shapes, ((8, 44, 47, (1, 1, 1)),
                                                (32, 42, 47, (1, 1, 1, 1, 1))),
                             restoration_times=restoration_times)
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


def check_nine_sheet_forts(*, restoration_times=False):
    patterns, supports = patterns_from_optional_vertices(9, 0, OPENING_NINE_COMMON,
                                                       OPENING_NINE_OPTIONAL)
    if len(patterns) != 12 or len(supports) != 2:
        raise AssertionError('Unexpected nine-sheet opening patterns')
    if {len(pattern) for pattern in patterns} != set(range(50, 55)):
        raise AssertionError('Unexpected sizes of nine-sheet forts')

    shapes = [mask(v * 11 + s for v, s in pattern) for pattern in patterns]
    for blocks in range(4, 28):
        check_guarded_shapes(blocks, 9, shapes, ((4, 51, 53, (1, 1)),
                                                (8, 50, 54, (1, 1, 2))),
                             restoration_times=restoration_times)
    print('Exactly 12 cost-24 forts of span nine, with two seed sets, at every length from four blocks')


def check_larger_optimal_spans(lengths):
    strip = runpy.run_path(str(Path(__file__).with_name('check_finite_fort_strip.py')))
    sheets = 34
    budget = 24
    for blocks in lengths:
        graph, blue, *_ = COVER['signed_prism_cover'](blocks, sheets)
        clauses, seeds, top = strip['strip_formula'](graph, blue, budget, sheets=sheets,
                                                    quotient_bounds=blocks == 26,
                                                    require_minimal=False)
        clauses.append([v + 1 for v in range(len(graph)) if 10 <= v % sheets < sheets - 1])
        with ITotalizer(lits=seeds, ubound=budget, top_id=top) as counter:
            with Solver(name='cadical195', bootstrap_with=clauses + counter.cnf.clauses) as solver:
                if solver.solve(assumptions=[-counter.rhs[budget]]):
                    raise AssertionError(('A cost-24 fort spans at least ten sheets', blocks))
        print(f'{blocks} blocks: every cost-24 fort spans at most nine sheets', flush=True)


def check_additional_blocker():
    sheets = 19
    lost = mask(v * sheets + s + 4 for v, s in ADDITIONAL_BLOCKER)
    if lost.bit_count() != 25:
        raise AssertionError('Expected a 25-seed loss set')
    for blocks in range(4, 21):
        graph, seeds, *_ = COVER['signed_prism_cover'](blocks, sheets)
        if lost & seeds != lost:
            raise AssertionError(('Expected seed labels in the loss set', blocks))
        arrival = COVER['MODEL']['trace'](graph, seeds & ~lost)[1]
        remaining = mask(v for v, t in enumerate(arrival) if t is None)
        occupied = {v % sheets for v in members(remaining)}
        if remaining.bit_count() != 59 or min(occupied) != 5 or max(occupied) != 13:
            raise AssertionError(('Unexpected residual fort for the 25-seed loss', blocks))
        profile = restoration_profile(graph, seeds, lost)
        if profile[0][0] != 10 or profile[-1][0] != 17:
            raise AssertionError(('Unexpected range of restoration times', blocks, profile))
    print('Checked an inclusion-minimal 25-seed loss at lengths four through twenty', flush=True)


def check_ordinary_stage_blocker():
    projection = runpy.run_path(str(Path(__file__).with_name('check_finite_fort_projection.py')))
    stage_start = BAND['stage_start']
    base, *_ = BAND['chain'](8)
    lift = projection['neighborhoods'](
        len(base), ((u, v, -1 if (u, v) == (0, 1) else 1)
                    for u, neighbors in enumerate(base) for v in members(neighbors) if u < v))
    for width in (1, 2):
        allowed = set(range(stage_start(2), stage_start(2 + width)))
        if projection['maximal_projection'](lift, allowed):
            raise AssertionError(('Unexpected finite support in ordinary stages', width))

    # The width-19 bands bound a cost-29 fort to at most 37 interior sheets.
    strip = runpy.run_path(str(Path(__file__).with_name('check_finite_fort_strip.py')))
    sheets, budget = 39, 29
    graph, blue, *_ = COVER['signed_prism_cover'](8, sheets)
    clauses, seeds, top = strip['strip_formula'](graph, blue, budget, sheets=sheets,
                                                quotient_bounds=False, require_minimal=False)
    lower, upper = stage_start(2) * sheets, stage_start(5) * sheets
    clauses.extend([-(v + 1)] for v in range(len(graph)) if not lower <= v < upper)
    active_seeds = [seed for seed in seeds if lower <= seed - 1 < upper]
    with ITotalizer(lits=active_seeds, ubound=budget, top_id=top) as counter:
        with Solver(name='cadical195', bootstrap_with=clauses + counter.cnf.clauses) as solver:
            if solver.solve(assumptions=[-counter.rhs[budget]]):
                raise AssertionError('A cheaper fort fits in three ordinary stages')

    expected = ((10, 5), (11, 8), (12, 5), (13, 3), (14, 3), (15, 5), (16, 1))
    for blocks, sheets, first in ((21, 28, 9), (24, 31, 11), (30, 29, 13)):
        graph, blue, *_ = COVER['signed_prism_cover'](blocks, sheets)
        start, stop = stage_start(first), stage_start(first + 3)
        lost = mask((start + v) * sheets + sheet + 7
                    for v, times in ORDINARY_BLOCKER for sheet in times)
        if lost & blue != lost or lost.bit_count() != 30:
            raise AssertionError(('Unexpected ordinary loss coordinates', blocks, sheets))
        arrival = COVER['MODEL']['trace'](graph, blue & ~lost)[1]
        fort = mask(v for v, time in enumerate(arrival) if time is None)
        if fort & blue != lost or fort.bit_count() != 73 or any(
                not start <= v // sheets < stop or v % sheets in (0, sheets - 1) for v in members(fort)):
            raise AssertionError(('Unexpected ordinary residual fort', blocks, sheets))
        if restoration_profile(graph, blue, lost) != expected:
            raise AssertionError(('Unexpected ordinary restoration times', blocks, sheets))
    print('Minimum cost in three ordinary stages is 30, with a 73-vertex residual fort', flush=True)


def check_guarded_ordinary_loss(sites):
    blocks, sheets, first = 24, 31, 10
    graph, blue, *_ = COVER['signed_prism_cover'](blocks, sheets)
    start, stop = BAND['stage_start'](first), BAND['stage_start'](first + 3)
    lost = mask((start + label) * sheets + sheet + 7 for label, sheet in sites)
    if lost.bit_count() != 30 or lost & blue != lost:
        raise AssertionError('Unexpected seed sites of the ordinary loss')
    arrivals = COVER['MODEL']['trace'](graph, blue & ~lost)[1]
    fort = mask(v for v, time in enumerate(arrivals) if time is None)
    if fort & blue != lost or any(
            not start <= v // sheets < stop or v % sheets in (0, sheets - 1) for v in members(fort)):
        raise AssertionError('Loss has no guarded ordinary fort')
    if sum(count for _, count in restoration_profile(graph, blue, lost)) != 30:
        raise AssertionError('Loss failed a one-seed restoration')


def check_ordinary_packing():
    sites = [(label, sheet) for label, group in ORDINARY_PACKING_LOSS for sheet in group]
    residues = {((label // 16) % 2, label % 16, (sheet - 3 * (label // 32)) % 4)
                for label, sheet in sites}
    if len(sites) != 30 or len(residues) != 30:
        raise AssertionError('Two ordinary loss sites have the same lattice residue')
    stages = {label // 16 for label, _ in sites}
    span = min(s for _, s in sites), max(s for _, s in sites)
    if stages != {0, 1, 2} or span != (1, 10):
        raise AssertionError('Unexpected support of the packing loss')
    check_guarded_ordinary_loss(sites)
    print('Thirty distinct lattice residues give one ordinary blocker per eight cells',
          flush=True)


def check_ordinary_incidence():
    sites = [(label, sheet) for label, group in ORDINARY_INCIDENCE_LOSS for sheet in group]
    occurrences = Counter(label % 16 for label, _ in sites)
    if occurrences[5] != 5 or any(count > 4 for label, count in occurrences.items() if label != 5):
        raise AssertionError('Unexpected incidence counts of the ordinary loss')
    if {label // 16 for label, _ in sites} != {0, 1, 2}:
        raise AssertionError('Unexpected stages of the ordinary loss')
    check_guarded_ordinary_loss(sites)
    print('Every seed is in at most five translates of the verified ordinary loss', flush=True)

    offsets = [(label // 16, sheet) for label, sheet in sites if label % 16 == 5]
    variables = {}
    window = []
    for stage in range(8):
        for sheet in range(20):
            window.append([variables.setdefault((stage + dx, sheet + dy), len(variables) + 1)
                           for dx, dy in offsets])
    defects = tuple(range(len(variables) + 1, len(variables) + len(window) + 1))
    clauses = []
    for defect, row in zip(defects, window):
        clauses.append([defect, *row])
        clauses.extend([defect, -a, -b] for a, b in combinations(row, 2))
    with ITotalizer(lits=list(defects), ubound=4, top_id=defects[-1]) as total:
        with Solver(name='cadical195', bootstrap_with=clauses + total.cnf.clauses) as solver:
            if solver.solve(assumptions=[-total.rhs[4]]):
                raise AssertionError('An incidence window has fewer than five exceptions')
    print('Every 8-by-20 window has at least five placements without exactly one label-5 survivor',
          flush=True)


def check_periodic_ordinary_survivors():
    period = ORDINARY_SURVIVOR_PERIOD
    sheets, first = 11, 9
    graph, seeds, *_ = COVER['signed_prism_cover'](17, sheets)
    start = BAND['stage_start'](first)
    offsets = {v for v in range(16) if seeds & (1 << ((start + v) * sheets))}
    blue = set()
    for label, phases in ORDINARY_SURVIVOR_MASKS:
        if label not in offsets or phases >> period:
            raise AssertionError('Unexpected periodic survivor coordinate')
        blue.update(16 * sheet + label for sheet in members(phases))
    if len(blue) != 151:
        raise AssertionError(('Unexpected periodic survivor count', len(blue)))

    local = []
    for label in range(16):
        neighbors = []
        for w in members(graph[(start + label) * sheets]):
            vertex, sheet = divmod(w, sheets)
            shift = sheet if sheet <= sheets // 2 else sheet - sheets
            if abs(shift) != 1:
                raise AssertionError(('Unexpected ordinary sheet shift', shift))
            neighbors.append(((vertex - start) % 16, shift))
        local.append(neighbors)
    # Keep all neighbor occurrences, even if two vertices have the same phase and label.
    rows = [tuple(16 * ((sheet + shift) % period) + label for label, shift in neighbors)
            for sheet in range(period) for neighbors in local]
    for rounds in range(1, len(rows) + 1):
        additions = set()
        for source in blue:
            white = [w for w in rows[source] if w not in blue]
            if len(white) == 1:
                additions.add(white[0])
        if not additions:
            raise AssertionError('Periodic forcing stopped before completion')
        blue.update(additions)
        if len(blue) == len(rows):
            break
    if rounds != 668 or len(blue) != len(rows):
        raise AssertionError(('Unexpected periodic forcing rounds', rounds))
    print('151 seeds per ordinary 128-sheet period force all vertices by round 668', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--longer', type=int, nargs='+', choices=(*range(4, 18), 26), default=(),
                        help='also replay the exclusions at spans ten through thirty-two')
    parser.add_argument('--restoration-times', action='store_true',
                        help='check the completion times after restoring one lost seed')
    parser.add_argument('--ordinary-stage-blocker', action='store_true',
                        help='check the finite blocker confined to three ordinary stages')
    parser.add_argument('--ordinary-packing', action='store_true',
                        help='check a lattice packing of disjoint ordinary size-30 blockers')
    parser.add_argument('--ordinary-density', action='store_true',
                        help='check ordinary witnesses for the survivor density bounds')
    args = parser.parse_args()
    if args.ordinary_packing:
        check_ordinary_packing()
    if args.ordinary_stage_blocker:
        check_ordinary_stage_blocker()
    if args.ordinary_density:
        check_ordinary_incidence()
        check_periodic_ordinary_survivors()
    ordinary_only = args.ordinary_stage_blocker or args.ordinary_packing or args.ordinary_density
    if ordinary_only and not args.longer and not args.restoration_times:
        raise SystemExit(0)
    check_minimum_spans()
    check_seed_frontiers()
    check_shortest_minimum_cost_forts(restoration_times=args.restoration_times)
    check_eight_sheet_forts(restoration_times=args.restoration_times)
    check_nine_sheet_forts(restoration_times=args.restoration_times)
    print('Checked the five seed families, their forcing closures and all optional-group combinations')
    if args.restoration_times:
        print('Checked all 2040 single-seed restorations at lengths four through twenty')
        check_additional_blocker()
    if args.longer:
        check_larger_optimal_spans(args.longer)
