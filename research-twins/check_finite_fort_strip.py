"""Search the guarded strip for a finite fort of a specified seed cost."""

import argparse
from collections import defaultdict
from itertools import combinations
from pathlib import Path
import runpy

from pysat.card import CardEnc, EncType, ITotalizer
from pysat.solvers import Solver


CHECKS = runpy.run_path(str(Path(__file__).with_name('check_cyclic_cover_saturation.py')))
MODEL = CHECKS['MODEL']
members = CHECKS['members']
mask = CHECKS['mask']
BLOCKS = 26
SHEETS = 37
CERTIFIED_BUDGET = 23


def minimal_fort_clauses(neighborhoods):
    """Require a local reason why each selected vertex cannot be removed alone."""
    order = len(neighborhoods)
    one = range(order + 1, 2 * order + 1)
    boundary = range(2 * order + 1, 3 * order + 1)
    for v, (a, b, c) in enumerate(neighborhoods):
        a, b, c = a + 1, b + 1, c + 1
        y, z = one[v], boundary[v]
        yield [-y, a, b, c]
        yield [-y, -a, -b]
        yield [-y, -a, -c]
        yield [-y, -b, -c]
        yield [-z, -(v + 1)]
        yield [-z, a, b]
        yield [-z, a, c]
        yield [-z, b, c]
        yield [-z, -a, -b, -c]
        yield [-(v + 1), y, boundary[a - 1], boundary[b - 1], boundary[c - 1]]


def add_projection_bound(clauses, seed_vars, budget, period, quotient_cost, top, *, sheets=SHEETS):
    fibers = defaultdict(list)
    for literal in seed_vars:
        base, sheet = divmod(literal - 1, sheets)
        fibers[base, sheet % period].append(literal)
    excess = budget - quotient_cost
    if excess == 0:
        for group in fibers.values():
            clauses.extend([-a, -b] for a, b in combinations(group, 2))
        return top

    repetitions = []
    for group in fibers.values():
        for i, literal in enumerate(group[1:], 1):
            top += 1
            repetitions.append(top)
            clauses.extend([-literal, -earlier, top] for earlier in group[:i])
    bound = CardEnc.atmost(lits=repetitions, bound=excess, top_id=top, encoding=EncType.seqcounter)
    clauses.extend(bound.clauses)
    return bound.nv


def strip_formula(graph, blue, budget, *, sheets=SHEETS):
    order = len(graph)
    _, arrival = MODEL['trace'](graph, blue)
    if None in arrival or max(arrival) != 2:
        raise AssertionError('Unexpected intact time in the guarded strip')
    neighbors = [tuple(members(row)) for row in graph]

    def active(v):
        return 0 < v % sheets < sheets - 1

    clauses = [[-(v + 1)] for v in range(order) if not active(v)]
    clauses.extend(minimal_fort_clauses(neighbors))
    top = 3 * order
    occupied = range(top + 1, top + 1 + sheets)
    suffix = range(top + 1 + sheets, top + 2 + 2 * sheets)
    top = suffix[-1]
    clauses.extend(([-suffix[-1]], [occupied[1]]))
    for sheet in range(sheets):
        layer = list(range(sheet + 1, order + 1, sheets)) if 0 < sheet < sheets - 1 else []
        clauses.append([-occupied[sheet], *layer])
        clauses.extend([-v, occupied[sheet]] for v in layer)
        clauses.extend(([-occupied[sheet], suffix[sheet]],
                        [-suffix[sheet + 1], suffix[sheet]],
                        [-suffix[sheet], occupied[sheet], suffix[sheet + 1]]))
        if 1 <= sheet < sheets - 1:
            clauses.append([occupied[sheet], occupied[sheet + 1], -suffix[sheet + 2]])

    roots = [0] * order
    for v in sorted(range(order), key=arrival.__getitem__):
        if not active(v):
            continue
        if blue & (1 << v):
            roots[v] = 1 << v
            continue
        source = MODEL['force_source'](graph, arrival, v)
        prerequisites = (graph[source] ^ (1 << v)) | (1 << source)
        for u in members(prerequisites):
            roots[v] |= roots[u]
        clauses.append([-(v + 1), *(u + 1 for u in members(roots[v]))])

    for v, adjacent in enumerate(neighbors):
        for u in adjacent:
            if active(u):
                clauses.append([v + 1, -(u + 1), *(w + 1 for w in adjacent if w != u and active(w))])
    seed_vars = [v + 1 for v in members(blue) if active(v)]
    top = add_projection_bound(clauses, seed_vars, budget, 10, 20, top, sheets=sheets)
    if budget > 20:
        top = add_projection_bound(clauses, seed_vars, budget, 9, 18, top, sheets=sheets)
    return clauses, seed_vars, top


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--budget', type=int, choices=range(20, 24), default=CERTIFIED_BUDGET)
    parser.add_argument('--sheets', type=int, choices=(33, SHEETS), default=SHEETS,
                        help='choose the 33-sheet bound from the wider bands or the 37-sheet strip')
    parser.add_argument('--conflicts', type=int, help='optionally cap the SAT search')
    args = parser.parse_args()
    sheets = args.sheets
    if args.conflicts is not None and args.conflicts < 1:
        parser.error('--conflicts must be positive')

    graph, blue, _, _ = CHECKS['signed_prism_cover'](BLOCKS, sheets)
    upper_witness = mask(v * sheets + sheet for v, sheet in CHECKS['FOUR_BLOCK_FORT'])
    if (CHECKS['fort_cost'](graph, blue, upper_witness) != 24
            or any(v % sheets in (0, sheets - 1) for v in members(upper_witness))):
        raise AssertionError('Missing the 24-seed upper witness')
    clauses, seed_vars, top = strip_formula(graph, blue, args.budget, sheets=sheets)
    with ITotalizer(lits=seed_vars, ubound=args.budget, top_id=top) as counter:
        with Solver(name='cadical195', bootstrap_with=clauses + counter.cnf.clauses) as solver:
            assumptions = [-counter.rhs[args.budget]]
            if args.conflicts is None:
                result = solver.solve(assumptions=assumptions)
            else:
                solver.conf_budget(args.conflicts)
                result = solver.solve_limited(assumptions=assumptions)
            if result:
                fort = mask(v - 1 for v in solver.get_model() if 0 < v <= len(graph))
                cost = CHECKS['fort_cost'](graph, blue, fort)
                if cost > args.budget or any(v % sheets in (0, sheets - 1) for v in members(fort)):
                    raise AssertionError('Invalid guarded witness')
                raise AssertionError(('fort below the certified lower bound', cost,
                                      tuple(divmod(v, sheets) for v in members(fort))))
            elif result is False:
                print(f'No finite fort of seed cost at most {args.budget}')
            else:
                print(f'Search inconclusive at budget {args.budget}')
                return 2
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
