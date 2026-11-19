"""Check the finite fort inequalities for the four-sheet prism chains."""

import argparse
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path
import runpy

from pysat.card import CardEnc, EncType
from pysat.solvers import Solver


MODEL = runpy.run_path(str(Path(__file__).with_name('check_multiple_loss_bounds.py')))
members = MODEL['members']
adjacency = MODEL['adjacency']
completion_time = MODEL['completion_time']
MAX_LOSSES = 7


def find_stalled_set(graph, seeds, required, active_order, *, also_required=None, budget=MAX_LOSSES):
    """Leave vertices outside the active range fixed and allow no forces there."""
    limit = CardEnc.atmost(lits=[v + 1 for v in seeds], bound=budget,
                         top_id=len(graph), encoding=EncType.totalizer)
    clauses = limit.clauses + [[v + 1 for v in required]]
    if also_required is not None:
        clauses.append([v + 1 for v in also_required])
    for v in range(active_order):
        neighbors = tuple(members(graph[v]))
        for u in neighbors:
            if u < active_order:
                clauses.append([v + 1, -(u + 1), *(w + 1 for w in neighbors if w != u)])
    with Solver(name='glucose4', bootstrap_with=clauses) as solver:
        if solver.solve():
            white = set(solver.get_model())
            return tuple(v for v in seeds if v + 1 in white)
    return None


def verify_case(case):
    blocks, columns = case
    verify_rank_case((blocks, columns, 0))
    return case


def verify_rank_case(case):
    return verify_prism_rank_case(case, 4, MODEL['four_sheet_cubic_chain_certificate'])


def verify_prism_rank_case(case, sheets, certificate):
    blocks, columns, extra = case
    rank = sheets * (8 * blocks + 1 + columns) + 1 + extra
    graph, blue, lost, waves = certificate(blocks, rank)
    even = sheets % 2 == 0
    obstruction = (1 << (2 * sheets)) - 1
    if (len(graph) // 2 + 1 != rank or completion_time(graph, blue) != 2
            or lost.bit_count() != sheets * blocks or len(waves) != 6 * blocks + 2
            or completion_time(graph, blue ^ obstruction) <= len(graph)
            or any(row.bit_count() != 3 or (even and any((v-w) % 2 == 0 for w in members(row)))
                   for v, row in enumerate(graph))):
        raise AssertionError(('prism chain metadata or full-fiber obstruction', sheets, case))
    MODEL['check_arrival_waves'](graph, blue ^ lost, waves)

    seeds = tuple(members(blue))
    first_padding = sheets * (16 * blocks + 2)
    also_required = None
    if extra:
        a, b = MODEL['PRISM_RANK_EDGE']
        start = len(graph) - 2 * extra
        required = [sheets * a, sheets * a + 2, sheets * b + 1, sheets * b + 3, *range(start, len(graph))]
        if columns > 1:
            also_required = range(first_padding, start)
    else:
        # Rotate a required deleted seed to sheet zero in the symmetric cover.
        required = [v for v in seeds if v % sheets == 0 and (columns <= 1 or v >= first_padding)]
    witness = find_stalled_set(graph, seeds, required, len(graph), also_required=also_required, budget=2 * sheets - 1)
    if witness is not None:
        raise AssertionError(('small fort', sheets, case, witness))
    return case


def verify_long_ladders(widths=range(10, 14), budget=MAX_LOSSES):
    for width in widths:
        order = 2 * width
        rungs = [(u, u + 1) for u in range(0, order, 2)]
        rails = [(u, u + 2) for u in range(order - 2)]
        attachments = list(zip((0, 1, order - 2, order - 1), range(order, order + 4)))
        graph = adjacency(order + 4, rungs + rails + attachments)
        witness = find_stalled_set(graph, range(len(graph)), range(order), order, budget=budget)
        if witness is not None:
            raise AssertionError(('unrepaired ladder', width, witness))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--jobs', type=int, default=1)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error('--jobs must be positive')
    verify_long_ladders()
    print('Ladder widths 10 through 13 verified', flush=True)
    with ProcessPoolExecutor(max_workers=args.jobs) as pool:
        for columns in range(10):
            cases = [(blocks, columns) for blocks in range(2, 35)]
            for count, _ in enumerate(pool.map(verify_case, cases), 1):
                if count % 10 == 0 or count == len(cases):
                    print(f'Padding columns {columns}: {count}/{len(cases)} graphs', flush=True)
        for columns in range(10):
            cases = [(blocks, columns, extra) for blocks in range(2, 35) for extra in range(1, 4)]
            for count, _ in enumerate(pool.map(verify_rank_case, cases), 1):
                if count == len(cases):
                    print(f'Augmentations at padding width {columns}: {count}/{len(cases)} graphs', flush=True)


if __name__ == '__main__':
    main()
