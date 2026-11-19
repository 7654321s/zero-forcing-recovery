"""Verify the finite fort checks for the three-sheet cubic recovery chains."""

import argparse
from concurrent.futures import ProcessPoolExecutor
from itertools import combinations
from pathlib import Path
import runpy

from z3 import Bool, Not, Or, PbLe, Solver, is_true, sat, unsat


MODEL = runpy.run_path(str(Path(__file__).with_name('check_multiple_loss_bounds.py')))
adjacency = MODEL['adjacency']
completion_time = MODEL['completion_time']
mask = MODEL['mask']
members = MODEL['members']
MAX_LOSSES = 5


def verify_long_ladders():
    """Use forces inside a ladder while the four old endpoints stay fixed."""
    checked = 0
    for width in range(7, 10):
        order = 2 * width
        internal = (1 << order) - 1
        rungs = [(u, u + 1) for u in range(0, order, 2)]
        rails = [(u, u + 2) for u in range(order - 2)]
        attachments = list(zip((0, 1, order - 2, order - 1), range(order, order + 4)))
        graph = adjacency(order + 4, rungs + rails + attachments)
        for count in range(1, MAX_LOSSES + 1):
            for failed in combinations(range(len(graph)), count):
                white = mask(failed)
                if not white & internal:
                    continue
                checked += 1
                while white & internal:
                    additions = 0
                    for v in members(internal & ~white):
                        target = graph[v] & white
                        if target.bit_count() == 1:
                            additions |= target & internal
                    if not additions:
                        raise AssertionError(('ladder stall', width, failed))
                    white ^= additions
    return checked


def verify_case(case):
    blocks, columns = case
    old_order = 13 * blocks + 3 + (blocks % 2 == 0)
    rank = 3 * (old_order // 2 + columns) + 1
    graph, blue, lost, waves = MODEL['three_sheet_cubic_chain_certificate'](blocks, rank)
    if (len(graph) // 2 + 1 != rank or completion_time(graph, blue) != 2
            or lost.bit_count() != 3 * blocks or len(waves) != 6 * blocks + 2
            or completion_time(graph, blue ^ 63) <= len(graph)):
        raise AssertionError(('three-sheet chain metadata or six-loss obstruction', case))
    MODEL['check_arrival_waves'](graph, blue ^ lost, waves)

    seeds = tuple(members(blue))
    first_padding = 3 * old_order
    if blocks == 1 or columns == 0:
        required = seeds
    elif columns == 1:
        required = tuple(v for v in seeds if v >= first_padding or graph[v] >> first_padding)
    else:
        required = tuple(v for v in seeds if v >= first_padding)

    white = [Bool(f'w{v}') for v in range(len(graph))]
    solver = Solver()
    # Rotation of the three sheets can place a required omitted seed in sheet zero.
    solver.add(Or(*(white[v] for v in required if v % 3 == 0)))
    solver.add(PbLe([(white[v], 1) for v in seeds], MAX_LOSSES))
    clauses = []
    for v, row in enumerate(graph):
        neighbors = tuple(members(row))
        for u in neighbors:
            clauses.append(Or(white[v], Not(white[u]), *(white[w] for w in neighbors if w != u)))
    solver.add(*clauses)
    result = solver.check()
    if result != unsat:
        witness = solver.reason_unknown() if result != sat else tuple(
            v for v in seeds if is_true(solver.model().eval(white[v], model_completion=True)))
        raise AssertionError(('small fort not ruled out', case, result, witness))
    return case


def verify_cases(cases, jobs):
    if jobs == 1:
        for case in map(verify_case, cases):
            yield case
        return
    with ProcessPoolExecutor(max_workers=jobs) as pool:
        yield from pool.map(verify_case, cases)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--jobs', type=int, default=1)
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error('--jobs must be positive')

    unpadded = [(blocks, 0) for blocks in range(2, 34)]
    padded = [(1, columns) for columns in range(2, 7)]
    padded.extend((blocks, columns) for blocks in range(2, 34) for columns in range(1, 7))
    for phase, cases in (('Unpadded', unpadded), ('Padded', padded)):
        for count, case in enumerate(verify_cases(cases, args.jobs), 1):
            if count % 20 == 0 or count == len(cases):
                print(f'{phase}: {count}/{len(cases)} graphs, latest {case}', flush=True)
    print('Ladder loss cases:', verify_long_ladders())


if __name__ == '__main__':
    main()
