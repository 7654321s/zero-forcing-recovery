"""Exclude projected supports of low-cost finite forts in shorter prism chains."""

import argparse
from itertools import product
from pathlib import Path
import runpy

from pysat.card import ITotalizer
from pysat.solvers import Solver


HERE = Path(__file__).resolve().parent
PROJECTION = runpy.run_path(str(HERE / 'check_finite_fort_projection.py'))
OPENING = runpy.run_path(str(HERE / 'check_prism_opening_insertion.py'))
BLOCK = OPENING['BLOCK']
members = BLOCK['members']
CERTIFIED_FIRST = 11
CERTIFIED_LAST = 23
BUDGET = 23


class Formula:
    def __init__(self, top=0):
        self.top = top
        self.true = self.fresh()
        self.clauses = [[self.true]]
        self.sums = {}
        self.comparisons = {}

    def fresh(self):
        self.top += 1
        return self.top

    def word(self, width):
        return tuple(self.fresh() for _ in range(width))

    def xor(self, a, b):
        c = self.fresh()
        self.clauses.extend(([-a, -b, -c], [-a, b, c], [a, -b, c], [a, b, -c]))
        return c

    def both(self, a, b):
        c = self.fresh()
        self.clauses.extend(([-a, -b, c], [a, -c], [b, -c]))
        return c

    def majority(self, a, b, c):
        out = self.fresh()
        self.clauses.extend(([-a, -b, out], [-a, -c, out], [-b, -c, out],
                             [a, b, -out], [a, c, -out], [b, c, -out]))
        return out

    def plus_small(self, word, amount):
        """Extend the word and add zero, one or two without overflow."""
        key = (word, amount)
        if key not in self.sums:
            bits = list((*word, -self.true))
            if amount:
                carry = self.true
                for i in range(amount - 1, len(bits)):
                    bit = bits[i]
                    bits[i] = self.xor(bit, carry)
                    carry = self.both(bit, carry)
            self.sums[key] = tuple(bits)
        return self.sums[key]

    def ge(self, first, second, offset):
        """Encode the comparison first >= second + offset."""
        key = (first, second, offset)
        if key not in self.comparisons:
            lhs = self.plus_small(first, max(0, -offset))
            rhs = self.plus_small(second, max(0, offset))
            value = self.true
            for a, b in zip(lhs, rhs):
                value = self.majority(a, -b, value)
            self.comparisons[key] = value
        return self.comparisons[key]


def check_comparators():
    formula = Formula()
    a, b = formula.word(3), formula.word(3)
    outputs = {offset: formula.ge(a, b, offset) for offset in range(-2, 3)}
    with Solver(name='cadical195', bootstrap_with=formula.clauses) as solver:
        for i, j in product(range(8), repeat=2):
            inputs = [u if n & (1 << k) else -u for word, n in ((a, i), (b, j))
                      for k, u in enumerate(word)]
            for offset, literal in outputs.items():
                wrong = literal if i < j + offset else -literal
                if solver.solve(assumptions=[*inputs, wrong]):
                    raise AssertionError(('integer comparator', i, j, offset))


def projected_formula(blocks, *, require_opening=True):
    graph, blue, _, _ = BLOCK['chain'](blocks)
    order = len(graph)
    lift = PROJECTION['neighborhoods'](order, ((u, v, -1 if (u, v) == (0, 1) else 1)
                                              for u, row in enumerate(graph)
                                              for v in members(row) if u < v))
    formula = Formula(order)
    formula.clauses.extend(BLOCK['fort_clauses'](graph, range(order)))
    if require_opening:
        formula.clauses.append([v + 1 for v in members(blue) if v < OPENING['OPENING']])
    for stage in range(1, blocks - 1):
        start = BLOCK['stage_start'](stage)
        formula.clauses.append(list(range(start + 1, start + 33)))

    width = (2 * (order - 1)).bit_length()
    for direction in (1, -1):
        rank = [formula.word(width) for _ in range(order)]
        for u, row in enumerate(lift):
            for v, shift in row:
                choices = [(u, direction * shift)]
                choices.extend((w, direction * (shift - other)) for w, other in row if w != v)
                witnesses = []
                for w, difference in choices:
                    marker = formula.fresh()
                    compare = formula.ge(rank[v], rank[w], difference)
                    formula.clauses.extend(([-marker, w + 1], [-marker, compare]))
                    witnesses.append(marker)
                formula.clauses.append([-(v + 1), *witnesses])
    return formula, [v + 1 for v in members(blue)]


def check_projected_case(blocks, budget=BUDGET, *, require_opening=True):
    if require_opening:
        OPENING['check_insertion'](blocks)
    formula, seeds = projected_formula(blocks, require_opening=require_opening)
    with ITotalizer(lits=seeds, ubound=budget, top_id=formula.top) as counter:
        with Solver(name='cadical195', bootstrap_with=formula.clauses + counter.cnf.clauses) as solver:
            if solver.solve(assumptions=[-counter.rhs[budget]]):
                raise AssertionError(('a projected support survives', blocks, budget))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--minimum-forts', action='store_true',
                      help='replay the budget-24 insertion checks for minimum forts')
    mode.add_argument('--cost-25-stage-pairs', action='store_true',
                      help='certify the empty stage pairs for finite forts of cost at most 25')
    args = parser.parse_args()
    check_comparators()
    if args.cost_25_stage_pairs:
        for blocks in (28, 29):
            BLOCK['check_band'](blocks, stages=27, budget=25)
            print(f'{blocks} blocks: the 27-stage band forces an empty pair', flush=True)
        for blocks in range(27, 14, -1):
            check_projected_case(blocks, 25, require_opening=False)
            print(f'{blocks} blocks: every finite fort of cost at most 25 has an empty stage pair',
                  flush=True)
    elif args.minimum_forts:
        OPENING['check_base_budget'](25, 24)
        print('Base obstruction at budget 24 excluded at 25 blocks', flush=True)
        for blocks in range(25, 17, -1):
            check_projected_case(blocks, 24)
            print(f'Projected obstruction at budget 24 excluded at {blocks} blocks', flush=True)
    else:
        for blocks in range(CERTIFIED_LAST, CERTIFIED_FIRST - 1, -1):
            check_projected_case(blocks)
            print(f'Projected obstruction at budget {BUDGET} excluded at {blocks} blocks', flush=True)
