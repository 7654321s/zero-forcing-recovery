"""Verify the opening insertion and the remaining base obstructions."""

from pathlib import Path
import runpy

from pysat.card import ITotalizer
from pysat.solvers import Solver


BLOCK = runpy.run_path(str(Path(__file__).with_name('check_block_stabilization.py')))
MODEL = BLOCK['MODEL']
members = BLOCK['members']
mask = BLOCK['mask']
OPENING = 18
STAGE = 16
LINKS = ((5, 20), (6, 20), (14, 18), (17, 19))


def moved(v):
    return v if v < OPENING else v + STAGE


def check_insertion(blocks):
    graph, blue, _, _ = BLOCK['chain'](blocks)
    larger, large_blue, _, _ = BLOCK['chain'](blocks + 1)
    opening_mask = (1 << OPENING) - 1
    _, arrival = MODEL['trace'](graph, blue & opening_mask)
    if any(t is None or t > 2 for t in arrival[:OPENING]):
        raise AssertionError(('opening fills from its own seeds', blocks))

    for u, v in LINKS:
        if tuple(members(graph[u] & ~opening_mask)) != (v,):
            raise AssertionError(('an opening source has additional stage neighbors', blocks, u))
    old_edges = {(moved(u), moved(v)) for u, v in BLOCK['edges'](graph)}
    new_edges = BLOCK['edges'](larger)
    removed = {(u, moved(v)) for u, v in LINKS}
    joined = {(OPENING + u, OPENING + STAGE + v) for u, v in BLOCK['PORTS']}
    blank = range(OPENING, OPENING + STAGE)
    cross_edges = {edge for edge in new_edges - old_edges
                   if any(v not in blank for v in edge)}
    if old_edges - new_edges != removed or cross_edges != set(LINKS) | joined:
        raise AssertionError(('opening insertion edges', blocks))
    added = mask(blank)
    if large_blue & ~added != mask(moved(v) for v in members(blue)):
        raise AssertionError(('opening insertion changes old seeds', blocks))


def check_base_budget(blocks):
    graph, blue, _, _ = BLOCK['chain'](blocks)
    clauses = list(BLOCK['fort_clauses'](graph, range(len(graph))))
    clauses.append([v + 1 for v in members(blue) if v < OPENING])
    for stage in range(1, blocks - 1):
        first = BLOCK['stage_start'](stage)
        clauses.append(list(range(first + 1, first + 2 * STAGE + 1)))
    seeds = [v + 1 for v in members(blue)]
    budget = 23
    with ITotalizer(lits=seeds, ubound=budget, top_id=len(graph)) as counter:
        with Solver(name='cadical195', bootstrap_with=clauses + counter.cnf.clauses) as solver:
            if solver.solve(assumptions=[-counter.rhs[budget]]):
                raise AssertionError(('base obstruction at budget 23', blocks))


if __name__ == '__main__':
    for blocks in (24, 25):
        check_insertion(blocks)
        check_base_budget(blocks)
        print(f'Opening insertion or an empty stage pair is available at {blocks} blocks')
