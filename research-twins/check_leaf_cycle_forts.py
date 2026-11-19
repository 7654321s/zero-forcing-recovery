"""Check exact minimum killing sizes for small leaf-cycle witnesses using python-sat."""

import argparse
from pathlib import Path
import runpy


def check_minimum(graph, blue, expected, model, solver_name):
    from pysat.card import CardEnc, EncType
    from pysat.solvers import Solver

    order = len(graph)
    members = model['members']
    initial = [v + 1 for v in members(blue)]
    fort_clauses = [list(range(1, order + 1))]
    for v, row in enumerate(graph, 1):
        neighbors = [u + 1 for u in members(row)]
        for u in neighbors:
            fort_clauses.append([v, -u, *(w for w in neighbors if w != u)])

    for bound in (expected - 1, expected):
        counter = CardEnc.atmost(initial, bound=bound, top_id=order, encoding=EncType.seqcounter)
        with Solver(name=solver_name, bootstrap_with=fort_clauses + counter.clauses) as solver:
            solved = solver.solve()
            if solved != (bound == expected):
                raise AssertionError(('unexpected search result', bound, solved))
            if solved:
                fort = model['mask'](v - 1 for v in solver.get_model() if 0 < v <= order)

    loss = blue & fort
    if (loss.bit_count() != expected
            or any((row & fort).bit_count() == 1 for v, row in enumerate(graph)
                   if not fort & (1 << v))
            or model['completion_time'](graph, blue ^ loss) <= order):
        raise AssertionError('The returned fort does not certify a killing loss')
    return list(members(loss))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--solver', default='glucose42', help='Solver name in python-sat')
    args = parser.parse_args()
    model = runpy.run_path(str(Path(__file__).with_name('check_multiple_loss_bounds.py')))
    for t, budget, padding, expected, compact in (
        (3, 2, 0, 12, False), (3, 2, 2, 12, False), (4, 2, 0, 11, False),
        (4, 2, 1, 12, False), (5, 2, 0, 11, False), (6, 2, 0, 11, False),
        (3, 1, 0, 3, True), (3, 2, 0, 4, True), (3, 3, 0, 5, True), (3, 4, 0, 6, True),
    ):
        options = dict(three_connected=True, fault_budget=budget, compact=compact)
        rank = model['cubic_single_loss_lift_rank'](t, **options) + padding
        graph, blue, _, _ = model['cubic_single_loss_lift_certificate'](
            t, cycle_rank=rank, **options
        )
        loss = check_minimum(graph, blue, expected, model, args.solver)
        print(f'intact {t + 2}, rank {rank}, minimum killing size {expected}, seeds {loss}')


if __name__ == '__main__':
    main()
