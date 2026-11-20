"""Verify signed prism covers using periodic sheet-band counts."""

import argparse
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


def wrapped_formula(graph, blue, sheets, budget, *, band_through=BAND_WIDTH,
                    require_minimal=True, compact_bands=False, sheet_cap=None):
    bounds = residual_bounds(sheets, budget, band_through)
    if bounds is None:
        return None
    cap = budget - bounds.get(sheets - 1, 0)
    if sheet_cap is not None:
        cap = min(cap, sheet_cap)
    if cap < 1:
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

    for width, lower in sorted(bounds.items()):
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


def check_wrapped_budget(blocks, sheets, budget, band_through):
    graph, blue, *_ = CHECKS['signed_prism_cover'](blocks, sheets)
    clauses = wrapped_formula(graph, blue, sheets, budget, band_through=band_through,
                              require_minimal=False, compact_bands=True)
    if clauses is not None:
        with Solver(name='cadical195', bootstrap_with=clauses) as solver:
            if solver.solve():
                raise AssertionError(('A wrapped fort exists', blocks, sheets, budget))
    print(f'{blocks} blocks, {sheets} sheets: no wrapped fort of cost {budget}', flush=True)


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


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--wrapped', type=int, nargs=4, action='append',
                      metavar=('BLOCKS', 'SHEETS', 'BUDGET', 'BAND_WIDTH'),
                      help='exclude a wrapped fort using the specified certified sheet bands')
    mode.add_argument('--insertion-obstruction', type=int, nargs='+', choices=range(25, 29),
                      metavar='SHEETS',
                      help='exclude wrapping at cost 24 when insertion is blocked at 24 blocks')
    args = parser.parse_args()
    if args.wrapped:
        for case in args.wrapped:
            check_wrapped_budget(*case)
    elif args.insertion_obstruction:
        for sheets in args.insertion_obstruction:
            check_insertion_obstruction(sheets)
    else:
        for blocks, cases in CASES.items():
            for sheets, expected in cases:
                check_cyclic_cost(blocks, sheets, expected)
