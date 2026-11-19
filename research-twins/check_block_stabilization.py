"""Check the stage contraction and the 25-stage band used for saturation."""

import argparse
from pathlib import Path
import runpy

from pysat.card import ITotalizer
from pysat.solvers import Solver


MODEL = runpy.run_path(str(Path(__file__).with_name('check_multiple_loss_bounds.py')))
chain = MODEL['cubic_two_round_chain_certificate']
mask = MODEL['mask']
members = MODEL['members']
PORTS = ((0, 0), (9, 2), (10, 2), (12, 1))


def stage_start(stage):
    return 18 + 16 * (stage - 1)


def edges(graph):
    return {(u, v) for u, row in enumerate(graph) for v in members(row) if u < v}


def check_contractions():
    count = 0
    for blocks in range(4, 19):
        larger, blue, _, _ = chain(blocks)
        smaller, small_blue, _, _ = chain(blocks - 1)
        source_edges = edges(larger)
        target_edges = edges(smaller)
        for stage in range(2, blocks - 1):
            start = stage_start(stage)
            removed = range(start, start + 16)

            def collapse(v):
                return v - 16 if v >= removed.stop else v

            retained = {(collapse(u), collapse(v)) for u, v in source_edges
                        if u not in removed and v not in removed}
            spliced = {(start - 16 + u, start + v) for u, v in PORTS}
            if retained & spliced or (retained | spliced) != target_edges:
                raise AssertionError(('stage contraction', blocks, stage))
            if mask(collapse(v) for v in members(blue) if v not in removed) != small_blue:
                raise AssertionError(('stage seed labels', blocks, stage))
            count += 1
    return count


def fort_clauses(graph, sources, start=0):
    for v in sources:
        neighbors = tuple(members(graph[v]))
        for u in neighbors:
            yield [v - start + 1, -(u - start + 1),
                   *(w - start + 1 for w in neighbors if w != u)]


def check_band(blocks):
    """Exclude a restricted fort of cost at most 23 occupying every stage pair."""
    graph, blue, _, _ = chain(blocks)
    start, stop = stage_start(1), stage_start(26)
    band = range(start, stop)
    active = mask(band)
    sources = [v for v in band if not graph[v] & ~active]
    clauses = list(fort_clauses(graph, sources, start))
    for stage in range(1, 25):
        a = stage_start(stage) - start + 1
        clauses.append(list(range(a, a + 32)))
    seeds = [v - start + 1 for v in members(blue & active)]
    if len(seeds) != 250:
        raise AssertionError(('seed count in stage band', len(seeds)))
    budget = 23
    with ITotalizer(lits=seeds, ubound=budget, top_id=len(band)) as counter:
        with Solver(name='cadical195', bootstrap_with=clauses + counter.cnf.clauses) as solver:
            if solver.solve(assumptions=[-counter.rhs[budget]]):
                raise AssertionError(('23 seed labels block the band', blocks))


def check_sheet_band(width, budget, pin_ends=False):
    margin = 2
    sheets = width + 2 * (margin + 1)
    graph, blue, _, _ = MODEL['cyclic_cubic_chain_lift'](chain(26), sheets, reversed_edge=(0, 1))
    order = len(graph)
    active = mask(v for v in range(order) if 0 < v % sheets < sheets - 1)
    sources = [v for v in members(active) if not graph[v] & ~active]
    clauses = [[-(v + 1)] for v in range(order) if not active & (1 << v)]
    clauses.extend(fort_clauses(graph, sources))
    first, last = margin + 1, margin + width
    for start in range(first, last):
        clauses.append([v + 1 for s in (start, start + 1) for v in range(s, order, sheets)])
    seeds = []
    for v in members(blue):
        s = v % sheets
        if first <= s <= last:
            if pin_ends and s in (first, last):
                clauses.append([-(v + 1)])
            else:
                seeds.append(v + 1)
    with ITotalizer(lits=seeds, ubound=budget, top_id=order) as counter:
        with Solver(name='cadical195', bootstrap_with=clauses + counter.cnf.clauses) as solver:
            if solver.solve(assumptions=[-counter.rhs[budget]]):
                raise AssertionError(('sheet band can be blocked', width, budget))


def check_small_cover(sheets):
    graph, blue, _, _ = MODEL['cyclic_cubic_chain_lift'](chain(26), sheets, reversed_edge=(0, 1))
    if MODEL['completion_time'](graph, blue) != 2:
        raise AssertionError(('unexpected intact time', sheets))
    clauses = list(fort_clauses(graph, range(len(graph))))
    seeds = list(members(blue))
    # Any fort meets the seed set, so rotate a seed in the fort to sheet zero.
    clauses.append([v + 1 for v in seeds if v % sheets == 0])
    for v in range(len(graph)):
        if blue & (1 << v):
            continue
        area = frontier = 1 << v
        for _ in range(4):
            larger = area
            for u in members(frontier):
                larger |= graph[u]
            frontier = larger ^ area
            area = larger
        clauses.append([-(v + 1), *(u + 1 for u in members(area & blue))])

    budget = 2 * sheets - 1
    with ITotalizer(lits=[v + 1 for v in seeds], ubound=budget, top_id=len(graph)) as counter:
        with Solver(name='cadical195', bootstrap_with=clauses + counter.cnf.clauses) as solver:
            if solver.solve(assumptions=[-counter.rhs[budget]]):
                raise AssertionError(('unexpected small blocking set', sheets, budget))
    fort_seeds = (1 << (2 * sheets)) - 1
    if fort_seeds & ~blue or MODEL['completion_time'](graph, blue ^ fort_seeds) <= len(graph):
        raise AssertionError(('missing full-fiber obstruction', sheets))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certify-sheets', type=int, nargs='+', choices=(7, 8, 9), default=(),
                        help='replay the selected small-sheet thresholds at 26 blocks')
    args = parser.parse_args()
    print(f'{check_contractions()} stage contractions checked', flush=True)
    check_band(26)
    check_band(27)
    print('Every 25-stage prefix band with at most 23 losses fills an adjacent pair', flush=True)
    for width in range(10, 14):
        check_sheet_band(width, width - 5, pin_ends=width > 10)
        print(f'A {width}-sheet band fills a pair after up to {width - 5} losses', flush=True)
    for sheets in args.certify_sheets:
        check_small_cover(sheets)
        print(f'The 26-block {sheets}-sheet cover has minimum blocking cost {2 * sheets}',
              flush=True)
