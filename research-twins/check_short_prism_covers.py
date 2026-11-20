"""Verify signed prism covers using periodic sheet-band counts."""

import argparse
from itertools import accumulate, combinations_with_replacement
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


def tight_sheet_cap(sheets, budget, bounds, cap):
    bands = [(width * budget - sheets * lower, width) for width, lower in bounds.items()
             if gcd(width, sheets) == 1]
    surplus, width = min(bands, default=(3, 0))
    # Sparse surplus profiles are cheap to enumerate. The complement bound handles the other cases.
    if surplus > 2:
        return cap
    orbit = [(j * width) % sheets for j in range(sheets)]
    largest = 0
    for positions in combinations_with_replacement(range(sheets), surplus):
        extras = [0] * sheets
        for position in positions:
            extras[position] += 1
        counts = [0] * sheets
        for current, following in zip(orbit, orbit[1:]):
            counts[following] = counts[current] + extras[(current + 1) % sheets] - extras[current]
        shift, remainder = divmod(budget - sum(counts), sheets)
        if remainder or min(counts) + shift < 0:
            continue
        counts = [value + shift for value in counts]
        prefix = list(accumulate(counts + counts, initial=0))
        if all(prefix[start + length] - prefix[start] >= lower
               for length, lower in bounds.items() for start in range(sheets)):
            largest = max(largest, max(counts))
    return min(largest, cap)


def wrapped_formula(graph, blue, sheets, budget, *, band_through=BAND_WIDTH,
                    require_minimal=True, compact_bands=False, sheet_cap=None):
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
    clauses.append([flags[0][0]])
    for row in flags[1:]:
        clauses.extend([-threshold, maximum] for threshold, maximum in zip(row, flags[0]))
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


def check_stage_ancestry():
    """Check that a vertex needs seeds only in its own stage and its successor."""
    blocks, sheets = 14, 13
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
    print('Nominal two-round proofs use seeds only in the same or next stage', flush=True)


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
    mode.add_argument('--four-sheet-barrier', action='store_true',
                      help='check the round-five separation across four intact sheets')
    mode.add_argument('--stage-ancestry', action='store_true',
                      help='check the one-sided stage support of two-round forcing proofs')
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
    elif args.four_sheet_barrier:
        for blocks in range(14, 28):
            check_four_sheet_barrier(blocks)
            print(f'{blocks} blocks: four intact sheets separate remaining whites at round five',
                  flush=True)
    elif args.stage_ancestry:
        check_stage_ancestry()
    else:
        for blocks, cases in CASES.items():
            for sheets, expected in cases:
                check_cyclic_cost(blocks, sheets, expected)
