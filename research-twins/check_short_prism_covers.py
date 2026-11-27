"""Verify signed prism covers using periodic sheet-band counts."""

import argparse
from itertools import accumulate, combinations_with_replacement, product
from math import gcd
from pathlib import Path
import runpy

from pysat.card import CardEnc, EncType
from pysat.solvers import Solver


WRAPPED = runpy.run_path(str(Path(__file__).with_name('check_32_sheet_cover.py')))
CHECKS = WRAPPED['CHECKS']
members = WRAPPED['members']
mask = WRAPPED['mask']
BAND_WIDTH = 25
CASES = {
    2: tuple((sheets, min(2 * sheets, 16)) for sheets in range(1, 18)),
    3: ((22, 21), (23, 21)),
}


def residual_bounds(sheets, budget, band_through=BAND_WIDTH):
    # Full periods in a band contribute exactly budget seeds per period.
    bounds = {}
    for width in range(10, band_through + 1):
        periods, residual = divmod(width, sheets)
        lower = width - 4 - periods * budget
        if lower > 0:
            if not residual:
                return None
            bounds[residual] = max(lower, bounds.get(residual, 0))
    return bounds


def sparse_sheet_profiles(sheets, budget, bounds, width, surplus):
    # When there is surplus, choose a rotation with a surplus window at zero.
    if surplus < 0:
        return
    orbit = [(j * width) % sheets for j in range(sheets)]
    for positions in combinations_with_replacement(range(sheets), max(surplus - 1, 0)):
        extras = [0] * sheets
        extras[0] = int(surplus > 0)
        for position in positions:
            extras[position] += 1
        counts = [0] * sheets
        for current, following in zip(orbit, orbit[1:]):
            counts[following] = counts[current] + extras[(current + 1) % sheets] - extras[current]
        shift, remainder = divmod(budget - sum(counts), sheets)
        if remainder or min(counts) + shift < 0:
            continue
        counts = tuple(value + shift for value in counts)
        doubled = counts + counts
        prefix = list(accumulate(doubled, initial=0))
        if all(prefix[start + length] - prefix[start] >= lower
               for length, lower in bounds.items() for start in range(sheets)):
            maximum = max(counts)
            yield min(doubled[start:start + sheets]
                      for start, count in enumerate(counts) if count == maximum)


def tight_sheet_cap(sheets, budget, bounds, cap):
    bands = [(width * budget - sheets * lower, width) for width, lower in bounds.items()
             if gcd(width, sheets) == 1]
    surplus, width = min(bands, default=(3, 0))
    # Sparse surplus profiles are cheap to enumerate. The complement bound handles the other cases.
    if surplus > 2:
        return cap
    profiles = sparse_sheet_profiles(sheets, budget, bounds, width, surplus)
    return min(max(map(max, profiles), default=0), cap)


def wrapped_formula(graph, blue, sheets, budget, *, band_through=BAND_WIDTH,
                    require_minimal=True, compact_bands=False, sheet_cap=None, sheet_count_flags=None):
    bounds = residual_bounds(sheets, budget, band_through)
    if bounds is None or any(width * budget < sheets * lower for width, lower in bounds.items()):
        return None
    # Pack disjoint certified windows to bound both individual sheets and longer windows.
    required = [0] * sheets
    stronger = {}
    best_single = 0
    for length in range(1, sheets):
        packed = max((required[length - width] + bound for width, bound in bounds.items()
                      if width <= length), default=0)
        required[length] = max(required[length - 1], packed)
        best_single = max(best_single, bounds.get(length, 0))
        if required[length] > best_single:
            stronger[length] = required[length]
    cap = tight_sheet_cap(sheets, budget, bounds, budget - required[-1])
    saturated = [width for width, lower in bounds.items() if width * budget == sheets * lower]
    for width in saturated:
        if width - 1 in bounds:
            cap = min(cap, bounds[width] - bounds[width - 1])
    repeat = gcd(sheets, *saturated)
    if sheet_cap is not None:
        cap = min(cap, sheet_cap)
    if cap < 1 or cap * sheets < budget:
        return None
    order = len(graph)
    clauses = list(WRAPPED['BLOCK']['fort_clauses'](graph, range(order)))
    if require_minimal:
        neighbors = [tuple(members(row)) for row in graph]
        clauses.extend(WRAPPED['STRIP']['minimal_fort_clauses'](neighbors))
    times, ancestry, _ = WRAPPED['LOSS']['nominal_cones'](graph, blue)
    for v in range(order):
        if times[v]:
            clauses.append([-(v + 1), *(s + 1 for s in members(ancestry[v]))])

    top = 3 * order
    flags = []
    for sheet in range(sheets):
        ids = [v + 1 for v in range(sheet, order, sheets) if blue & (1 << v)]
        row, top = WRAPPED['thresholds'](ids, top, clauses, cap)
        flags.append(row)
        clauses.append([v + 1 for s in (sheet, (sheet + 1) % sheets)
                        for v in range(s, order, sheets)])
    if sheet_count_flags is not None:
        sheet_count_flags.extend(flags)
    clauses.append([flags[0][0]])
    for row in flags[1:]:
        clauses.extend([-threshold, maximum] for threshold, maximum in zip(row, flags[0]))
    # Equal consecutive saturated window counts force equal entering and leaving sheet counts.
    for first in range(sheets - repeat):
        for a, b in zip(flags[first], flags[first + repeat]):
            clauses.extend(([-a, b], [a, -b]))
    total = CardEnc.equals(lits=[flag for row in flags for flag in row], bound=budget,
                           top_id=top, encoding=EncType.seqcounter)
    clauses.extend(total.clauses)
    top = total.nv

    for width, lower in sorted((bounds | stronger).items()):
        if compact_bands and width == sheets - 1:
            continue  # The per-sheet counters already impose this complement bound.
        complement = compact_bands and 2 * width > sheets
        length = sheets - width if complement else width
        bound = budget - lower if complement else lower
        encode = CardEnc.atmost if complement else CardEnc.atleast
        for sheet in range(sheets):
            window = [flag for j in range(length) for flag in flags[(sheet + j) % sheets]]
            if not complement and bound > len(window):
                return None
            count = encode(lits=window, bound=bound, top_id=top, encoding=EncType.seqcounter)
            clauses.extend(count.clauses)
            top = count.nv
    return clauses


def upper_cost(blocks, sheets, graph, blue):
    coordinates = CHECKS['TWO_BLOCK_FORT' if blocks == 2 else 'THREE_BLOCK_FORT']
    projected = mask({v * sheets + s % sheets for v, s in coordinates})
    cost = CHECKS['fort_cost'](graph, blue, projected)
    fiber = (1 << (2 * sheets)) - 1
    if not fiber & ~blue and CHECKS['MODEL']['completion_time'](graph, blue ^ fiber) > len(graph):
        return min(cost, 2 * sheets)
    return cost


def check_cyclic_cost(blocks, sheets, expected):
    graph, blue, *_ = CHECKS['signed_prism_cover'](blocks, sheets)
    if upper_cost(blocks, sheets, graph, blue) != expected:
        raise AssertionError(('Missing an upper witness', blocks, sheets, expected))
    first = ((BAND_WIDTH - 4) * sheets + BAND_WIDTH - 1) // BAND_WIDTH
    for budget in range(first, expected):
        clauses = wrapped_formula(graph, blue, sheets, budget)
        if clauses is None:
            continue
        with Solver(name='cadical195', bootstrap_with=clauses) as solver:
            if solver.solve():
                raise AssertionError(('A cheaper wrapped fort exists', blocks, sheets, budget))
    print(f'{blocks} blocks, {sheets} sheets: blocking cost {expected}', flush=True)


def check_wrapped_budget(blocks, sheets, budget, band_through, *, occupied_stage_pairs=False):
    graph, blue, *_ = CHECKS['signed_prism_cover'](blocks, sheets)
    clauses = wrapped_formula(graph, blue, sheets, budget, band_through=band_through,
                              require_minimal=False, compact_bands=True)
    if clauses is not None:
        if occupied_stage_pairs:
            stage_start = WRAPPED['BLOCK']['stage_start']
            for stage in range(1, blocks - 1):
                start = stage_start(stage) * sheets
                stop = stage_start(stage + 2) * sheets
                clauses.append(list(range(start + 1, stop + 1)))
        with Solver(name='cadical195', bootstrap_with=clauses) as solver:
            if solver.solve():
                raise AssertionError(('A wrapped fort exists', blocks, sheets, budget))
    scope = ' meeting every appended stage pair' if occupied_stage_pairs else ''
    print(f'{blocks} blocks, {sheets} sheets: no wrapped fort of cost {budget}{scope}', flush=True)


def exclude_sheet_profiles(blocks, sheets, budget, width, profiles):
    cap = max(map(max, profiles))
    graph, blue, *_ = CHECKS['signed_prism_cover'](blocks, sheets)
    flags = []
    clauses = wrapped_formula(graph, blue, sheets, budget, band_through=width,
                              require_minimal=False, compact_bands=True, sheet_cap=cap,
                              sheet_count_flags=flags)
    if clauses is None or len(flags) != sheets or any(len(row) != cap for row in flags):
        raise AssertionError(('Unexpected wrapped profile formula', blocks, sheets))
    with Solver(name='cadical195', bootstrap_with=clauses) as solver:
        for profile in sorted(profiles):
            assumptions = [flag if count >= threshold else -flag
                           for row, count in zip(flags, profile)
                           for threshold, flag in enumerate(row, start=1)]
            if solver.solve(assumptions=assumptions):
                raise AssertionError(('A wrapped fort exists', blocks, sheets, budget, profile))
    print(f'{blocks} blocks, {sheets} sheets: all {len(profiles)} cost-{budget} profiles excluded',
          flush=True)


def check_degree_33_period_39():
    blocks, sheets, budget, width = 36, 39, 33, 25
    bounds = residual_bounds(sheets, budget, width)
    surplus = width * budget - sheets * bounds[width]
    profiles = set(sparse_sheet_profiles(sheets, budget, bounds, width, surplus))
    groups = {cap: [row for row in profiles if max(row) == cap] for cap in (1, 2, 3)}
    if surplus != 6 or len(profiles) != 967 or tuple(map(len, groups.values())) != (177, 789, 1):
        raise AssertionError('Unexpected sheet counts at degree 33 and period 39')
    for group in groups.values():
        exclude_sheet_profiles(blocks, sheets, budget, width, group)


def check_degree_31_period_37(blocks=36):
    sheets, budget, width = 37, 31, 24
    bounds = residual_bounds(sheets, budget, width)
    surplus = width * budget - sheets * bounds[width]
    profiles = set(sparse_sheet_profiles(sheets, budget, bounds, width, surplus))
    if len(profiles) != 130 or max(map(max, profiles)) != 2:
        raise AssertionError('Unexpected sheet counts at period 37')
    exclude_sheet_profiles(blocks, sheets, budget, width, profiles)


def check_degree_31_period_36(blocks=13):
    sheets, budget, width = 36, 31, 28
    bounds = residual_bounds(sheets, budget, width)
    # Each of the four orbits must contain one surplus window. Rotate the
    # position in the zero residue class to zero before choosing the others.
    orbits = [[(r + j * width) % sheets for j in range(9)] for r in range(4)]
    profiles = set()
    for positions in product(*(range(r, sheets, 4) for r in (1, 2, 3))):
        surplus = {0, *positions}
        offsets = [0] * sheets
        for orbit in orbits:
            for i, j in zip(orbit, orbit[1:]):
                offsets[j] = offsets[i] + ((i + 1) % sheets in surplus) - (i in surplus)
            minimum = min(offsets[i] for i in orbit)
            for i in orbit:
                offsets[i] -= minimum
        units, remainder = divmod(budget - sum(offsets), 9)
        if remainder or units < 0:
            continue
        for extra in combinations_with_replacement(range(4), units):
            levels = [extra.count(r) for r in range(4)]
            counts = tuple(n + levels[i % 4] for i, n in enumerate(offsets))
            repeated = counts + counts
            prefix = list(accumulate(repeated, initial=0))
            if any(prefix[i + length] - prefix[i] < lower
                   for length, lower in bounds.items() for i in range(sheets)):
                continue
            peak = max(counts)
            profiles.add(min(repeated[i:i + sheets] for i, n in enumerate(counts) if n == peak))
    if len(profiles) != 45 or max(map(max, profiles)) != 2:
        raise AssertionError('Unexpected sheet counts at period 36')
    exclude_sheet_profiles(blocks, sheets, budget, width, profiles)


def check_ordinary_wrapping(sheets, budget):
    if budget not in (28, 29, 30):
        raise ValueError('Ordinary wrapping check requires a budget from 28 to 30')
    graph, blue, *_ = CHECKS['signed_prism_cover'](36, sheets)
    clauses = wrapped_formula(graph, blue, sheets, budget, band_through=20,
                              require_minimal=False, compact_bands=True)
    if clauses is not None:
        stage_start = WRAPPED['BLOCK']['stage_start']
        stages = 31 if budget == 30 else 30
        first = stage_start(2) * sheets
        stop = stage_start(2 + stages) * sheets
        clauses.extend([-(v + 1)] for v in range(len(graph)) if not first <= v < stop)
        clauses.append(list(range(first + 1, stage_start(3) * sheets + 1)))
        with Solver(name='cadical195', bootstrap_with=clauses) as solver:
            if solver.solve():
                raise AssertionError(('An ordinary wrapped fort exists', sheets, budget))
    print(f'{sheets} sheets: no ordinary wrapped fort of cost {budget}', flush=True)


def check_insertion_obstruction(sheets):
    blocks, budget = 24, 24
    graph, blue, *_ = CHECKS['signed_prism_cover'](blocks, sheets)
    # Two bands partition the complement of one sheet at these three periods.
    cap = 33 - sheets if sheets > 25 else None
    clauses = wrapped_formula(graph, blue, sheets, budget, band_through=24,
                              require_minimal=False, compact_bands=True, sheet_cap=cap)
    stage_start = WRAPPED['BLOCK']['stage_start']
    opening = stage_start(1) * sheets
    clauses.append([v + 1 for v in members(blue) if v < opening])
    for stage in range(1, blocks - 1):
        start = stage_start(stage) * sheets
        stop = stage_start(stage + 2) * sheets
        clauses.append(list(range(start + 1, stop + 1)))

    # Every projected seed must have exactly one lifted representative.
    top = max(abs(v) for clause in clauses for v in clause)
    for start in range(0, len(graph), sheets):
        if (blue >> start) & 1:
            bound = CardEnc.atmost(lits=list(range(start + 1, start + sheets + 1)),
                                   bound=1, top_id=top, encoding=EncType.seqcounter)
            clauses.extend(bound.clauses)
            top = bound.nv
    with Solver(name='cadical195', bootstrap_with=clauses) as solver:
        if solver.solve():
            raise AssertionError(('A wrapped fort prevents insertion at 24 blocks', sheets))
    print(f'24 blocks, {sheets} sheets: no cost-24 wrapped fort prevents insertion', flush=True)


def check_four_sheet_barrier(blocks):
    """Check separation at the center of four intact sheets by round five."""
    sheets, cut = 31, 15
    graph, blue, *_ = CHECKS['signed_prism_cover'](blocks, sheets)
    intact = mask(v for v in members(blue) if cut - 2 <= v % sheets < cut + 2)
    _, arrivals = CHECKS['MODEL']['trace'](graph, intact)
    left = []
    right = 0
    for v, arrival in enumerate(arrivals):
        if arrival is None or arrival > 5:
            if cut - 2 <= v % sheets < cut:
                left.append(v)
            elif cut <= v % sheets < cut + 2:
                right |= 1 << v
    for v in left:
        neighborhood = graph[v]
        for u in members(graph[v]):
            neighborhood |= graph[u]
        if neighborhood & right:
            raise AssertionError(('Two late white vertices cross the cut', blocks, v))


def check_stage_ancestry(blocks):
    """Check that a vertex needs seeds only in its own stage and its successor."""
    sheets = 13
    graph, blue, *_ = CHECKS['signed_prism_cover'](blocks, sheets)
    arrivals, supporters, _ = WRAPPED['LOSS']['nominal_cones'](graph, blue)
    if max(arrivals) != 2:
        raise AssertionError('Unexpected intact completion time')
    opening = WRAPPED['BLOCK']['stage_start'](1)

    def stage(vertex):
        label = vertex // sheets
        return 0 if label < opening else 1 + (label - opening) // 16

    for v, seeds in enumerate(supporters):
        if any((stage(u) - stage(v)) % blocks not in (0, 1) for u in members(seeds)):
            raise AssertionError(('Unexpected stage ancestry', v))
    print(f'{blocks} blocks: nominal two-round proofs use seeds only in the same or next stage',
          flush=True)


def check_rectangle_separation():
    """Replay four rectangles with ordinary stage guards and four-sheet guards."""
    enumerate_losses = runpy.run_path(str(Path(__file__).with_name('check_cost_25_blocking_sets.py')))
    ordinary_blocker = enumerate_losses['SPAN']['ORDINARY_BLOCKER']
    stage_start = WRAPPED['BLOCK']['stage_start']
    blocks, sheets = 17, 30
    graph, blue, *_ = CHECKS['signed_prism_cover'](blocks, sheets)
    neighbors = tuple(tuple(members(row)) for row in graph)
    white = bytearray(not (blue >> v) & 1 for v in range(len(graph)))
    final_white = enumerate_losses['remaining_white']
    losses, isolated = [], []
    for first in (4, 9):
        for sheet in (0, 15):
            lost = mask((stage_start(first) + v) * sheets + sheet + offset - 1
                        for v, offsets in ordinary_blocker for offset in offsets)
            if lost & blue != lost or lost.bit_count() != 30:
                raise AssertionError(('Unexpected rectangle seed labels', first, sheet))
            repaired = lost ^ (lost & -lost)
            fort = final_white(neighbors, white, lost)
            if not fort or final_white(neighbors, white, repaired):
                raise AssertionError(('Unexpected isolated rectangle recovery', first, sheet))
            losses.append((repaired, lost))
            isolated.append(fort)

    for choices in product((0, 1), repeat=len(losses)):
        combined = 0
        expected = 0
        for index, choice in enumerate(choices):
            combined |= losses[index][choice]
            if choice:
                expected |= isolated[index]
        if final_white(neighbors, white, combined) != expected:
            raise AssertionError(('Rectangle white sets do not factor', choices))
    print('All 16 mixed four-rectangle closures agree with isolated closures', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--wrapped', type=int, nargs=4, action='append',
                      metavar=('BLOCKS', 'SHEETS', 'BUDGET', 'BAND_WIDTH'),
                      help='exclude a wrapped fort using the specified certified sheet bands')
    mode.add_argument('--wrapped-with-occupied-pairs', type=int, nargs=4, action='append',
                      metavar=('BLOCKS', 'SHEETS', 'BUDGET', 'BAND_WIDTH'),
                      help='exclude a wrapped fort that meets every adjacent appended stage pair')
    mode.add_argument('--ordinary-wrapped', type=int, nargs=2, action='append',
                      metavar=('SHEETS', 'BUDGET'),
                      help='exclude wrapping in the ordinary stage window at budget 28, 29 or 30')
    mode.add_argument('--insertion-obstruction', type=int, nargs='+', choices=range(22, 29),
                      metavar='SHEETS',
                      help='exclude wrapping at cost 24 when insertion is blocked at 24 blocks')
    mode.add_argument('--degree-31-period-37', nargs='?', type=int, choices=(33, 36), const=36,
                      metavar='BLOCKS', help='exclude all cost-31 wrapped profiles at 37 sheets')
    mode.add_argument('--degree-31-period-36', nargs='?', type=int, choices=range(6, 25), const=13,
                      metavar='BLOCKS', help='exclude all cost-31 wrapped profiles at 36 sheets')
    mode.add_argument('--degree-33-period-39', action='store_true',
                      help='exclude all cost-33 wrapped profiles at 39 sheets')
    mode.add_argument('--four-sheet-barrier', action='store_true',
                      help='check the round-five separation across four intact sheets')
    mode.add_argument('--stage-ancestry', action='store_true',
                      help='check the one-sided stage support of two-round forcing proofs')
    mode.add_argument('--rectangle-separation', action='store_true',
                      help='replay combined ordinary rectangles with intact guards')
    args = parser.parse_args()
    if args.wrapped:
        for case in args.wrapped:
            check_wrapped_budget(*case)
    elif args.wrapped_with_occupied_pairs:
        for case in args.wrapped_with_occupied_pairs:
            check_wrapped_budget(*case, occupied_stage_pairs=True)
    elif args.ordinary_wrapped:
        for case in args.ordinary_wrapped:
            check_ordinary_wrapping(*case)
    elif args.insertion_obstruction:
        for sheets in args.insertion_obstruction:
            check_insertion_obstruction(sheets)
    elif args.degree_31_period_37:
        check_degree_31_period_37(args.degree_31_period_37)
    elif args.degree_31_period_36:
        check_degree_31_period_36(args.degree_31_period_36)
    elif args.degree_33_period_39:
        check_degree_33_period_39()
    elif args.four_sheet_barrier:
        for blocks in range(13, 28):
            check_four_sheet_barrier(blocks)
            print(f'{blocks} blocks: four intact sheets separate remaining whites at round five',
                  flush=True)
    elif args.stage_ancestry:
        for blocks in (7, 8, 9, 10, 11):
            check_stage_ancestry(blocks)
    elif args.rectangle_separation:
        check_rectangle_separation()
    else:
        for blocks, cases in CASES.items():
            for sheets, expected in cases:
                check_cyclic_cost(blocks, sheets, expected)
