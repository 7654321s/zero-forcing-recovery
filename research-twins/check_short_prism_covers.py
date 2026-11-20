"""Verify the small signed prism covers using periodic sheet-band counts."""

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


def residual_bounds(sheets, budget):
    # Full periods in a band contribute exactly budget seeds per period.
    bounds = {}
    for width in range(10, BAND_WIDTH + 1):
        periods, residual = divmod(width, sheets)
        lower = width - 4 - periods * budget
        if lower > 0:
            if not residual:
                return None
            bounds[residual] = max(lower, bounds.get(residual, 0))
    return bounds


def wrapped_formula(graph, blue, sheets, budget):
    bounds = residual_bounds(sheets, budget)
    if bounds is None:
        return None
    cap = budget - bounds.get(sheets - 1, 0)
    if cap < 1:
        return None
    order = len(graph)
    neighbors = [tuple(members(row)) for row in graph]
    clauses = list(WRAPPED['BLOCK']['fort_clauses'](graph, range(order)))
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
        for sheet in range(sheets):
            window = [flag for j in range(width) for flag in flags[(sheet + j) % sheets]]
            if lower > len(window):
                return None
            count = CardEnc.atleast(lits=window, bound=lower, top_id=top, encoding=EncType.seqcounter)
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


if __name__ == '__main__':
    for blocks, cases in CASES.items():
        for sheets, expected in cases:
            check_cyclic_cost(blocks, sheets, expected)
