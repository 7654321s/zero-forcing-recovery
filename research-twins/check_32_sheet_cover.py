"""Certify the wrapped-fort bounds at 27 through 32 sheets."""

import argparse
from itertools import product
from pathlib import Path
import runpy

from pysat.card import CardEnc, EncType
from pysat.solvers import Solver


CV = runpy.run_path(str(Path(__file__).with_name('check_33_sheet_profiles.py')))
BLOCK, STRIP, LOSS, CHECKS = (CV[name] for name in ('BLOCK', 'STRIP', 'LOSS', 'CHECKS'))
members, mask = STRIP['members'], STRIP['mask']
SHEETS = 32
BUDGET = 23
SHEET_CAP = 4
CASES = {
    27: ((21, 3), (22, 4), (23, 5)),
    28: ((20, 2), (21, 3), (22, 4), (23, 5)),
    29: ((21, 3), (22, 4), (23, 5)),
    30: ((21, 3), (22, 4), (23, 5)),
    31: ((22, 4), (23, 5)),
    32: ((23, 4),),
}


def thresholds(seed_vars, top, clauses, cap):
    """Encode the exact prefix thresholds up to and including cap + 1."""
    previous = []
    for u in seed_vars:
        current = []
        for j in range(min(len(previous) + 1, cap + 1)):
            top += 1
            flag = top
            current.append(flag)
            stay = previous[j:j + 1]
            if stay:
                clauses.append([-stay[0], flag])
            step = previous[j - 1:j] if j else []
            clauses.append([-u, *(-v for v in step), flag])
            clauses.append([-flag, *stay, u])
            if step:
                clauses.append([-flag, *stay, step[0]])
        previous = current
    if len(previous) > cap:
        clauses.append([-previous[-1]])
    return previous[:cap], top


def check_thresholds(cap=SHEET_CAP):
    clauses = []
    seeds = list(range(1, 7))
    flags, _ = thresholds(seeds, len(seeds), clauses, cap)
    with Solver(name='cadical195', bootstrap_with=clauses) as solver:
        for values in product((False, True), repeat=len(seeds)):
            assumptions = [u if value else -u for u, value in zip(seeds, values)]
            count = sum(values)
            if solver.solve(assumptions=assumptions) != (count <= cap):
                raise AssertionError(('threshold cap', values))
            if count <= cap:
                for j, flag in enumerate(flags, 1):
                    opposite = -flag if count >= j else flag
                    if solver.solve(assumptions=[*assumptions, opposite]):
                        raise AssertionError(('threshold semantics', values, j))


def wrapped_formula(graph, blue, sheets=SHEETS, budget=BUDGET, cap=SHEET_CAP, *, band_through=13):
    order = len(graph)
    adjacent = [tuple(members(row)) for row in graph]
    clauses = list(BLOCK['fort_clauses'](graph, range(order)))
    clauses.extend(STRIP['minimal_fort_clauses'](adjacent))
    arrival, ancestors, _ = LOSS['nominal_cones'](graph, blue)
    for v in sorted(range(order), key=arrival.__getitem__):
        if arrival[v]:
            clauses.append([-(v + 1), *(s + 1 for s in members(ancestors[v]))])

    top = 3 * order
    counters = []
    for sheet in range(sheets):
        seeds = [v + 1 for v in range(sheet, order, sheets) if blue & (1 << v)]
        row, top = thresholds(seeds, top, clauses, cap)
        counters.append(row)
        clauses.append([v + 1 for s in (sheet, (sheet + 1) % sheets)
                        for v in range(s, order, sheets)])
    clauses.append([counters[0][0]])
    selected = [flag for row in counters for flag in row]
    total = CardEnc.equals(lits=selected, bound=budget, top_id=top, encoding=EncType.seqcounter)
    top = total.nv
    clauses.extend(total.clauses)
    for width in range(10, band_through + 1):
        for sheet in range(sheets):
            window = [flag for j in range(width) for flag in counters[(sheet + j) % sheets]]
            lower = CardEnc.atleast(lits=window, bound=width - 4, top_id=top, encoding=EncType.seqcounter)
            top = lower.nv
            clauses.extend(lower.clauses)

    empty_stages = {}
    for stage in range(1, 26):
        top += 1
        empty_stages[stage] = top
        start = BLOCK['stage_start'](stage)
        clauses.extend([-top, -(v + 1)] for v in range(start * sheets, (start + 16) * sheets))
    gaps = []
    for stage in range(1, 25):
        top += 1
        gaps.append(top)
        clauses.extend(([-top, empty_stages[stage]], [-top, empty_stages[stage + 1]]))
    clauses.append(gaps)
    return clauses


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--sheets', type=int, choices=CASES, default=SHEETS)
    parser.add_argument('--conflicts', type=int, help='optionally cap each SAT search')
    args = parser.parse_args()
    if args.conflicts is not None and args.conflicts < 1:
        parser.error('--conflicts must be positive')

    graph, blue, _, _ = CHECKS['signed_prism_cover'](26, args.sheets)
    upper = mask(v * args.sheets + sheet for v, sheet in CHECKS['FOUR_BLOCK_FORT'])
    if CHECKS['fort_cost'](graph, blue, upper) != 24:
        raise AssertionError('Missing the 24-seed upper witness')
    band_through = 16 if args.sheets == 27 else 13
    for budget, cap in CASES[args.sheets]:
        check_thresholds(cap)
        clauses = wrapped_formula(graph, blue, args.sheets, budget, cap, band_through=band_through)
        with Solver(name='cadical195', bootstrap_with=clauses) as solver:
            if args.conflicts is None:
                result = solver.solve()
            else:
                solver.conf_budget(args.conflicts)
                result = solver.solve_limited()
            if result:
                fort = mask(v - 1 for v in solver.get_model() if 0 < v <= len(graph))
                raise AssertionError(('wrapped fort', args.sheets, CHECKS['fort_cost'](graph, blue, fort)))
        if result is None:
            print(f'{args.sheets}-sheet search at budget {budget} inconclusive')
            return 2
        print(f'No wrapped {budget}-seed fort at {args.sheets} sheets')
    print(f'Valid 24-seed witness at {args.sheets} sheets')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
