"""Replay the size-32 near boundary and check short outer windows."""

import argparse
from collections import Counter
import gzip
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
BOUNDARY = runpy.run_path(str(HERE / 'check_degree_31_boundary.py'))
CHECK = BOUNDARY['CHECK']
BLOCKS = 13
SHEETS = 38
SIZE = 32
SUPPORT_COUNTS = {'0-1-2': 46034, '0-1-2-3': 293, '0-11-12': 3061,
                  '1-2-3': 276, '10-11-12': 917, '11-12': 352}


def support(row):
    return tuple(sorted({BOUNDARY['stage'](v) for v, _ in row}))


def read_catalogue():
    with gzip.open(HERE / 'degree-32-near-catalogue.json.gz', 'rt', encoding='utf-8') as src:
        archive = json.load(src)
    if (archive['schema_version'], archive['blocks'], archive['size'],
            archive['first_sheet']) != (1, BLOCKS, SIZE, 1):
        raise AssertionError('Unexpected size-32 catalogue metadata')

    rows = tuple(tuple(map(tuple, row)) for row in archive['losses'])
    if tuple(sorted(set(rows))) != rows or any(
            len(set(row)) != SIZE or len(row) != SIZE or CHECK['normalized'](row) != row
            for row in rows):
        raise AssertionError('Unexpected size-32 catalogue entries')
    counts = Counter('-'.join(map(str, support(row))) for row in rows)
    if counts != SUPPORT_COUNTS or counts != archive['support_counts']:
        raise AssertionError(('Unexpected near-boundary stage supports', counts))
    return rows


def check_witnesses(rows):
    graph, blue, *_ = CHECK['COVER']['signed_prism_cover'](BLOCKS, SHEETS)
    _, _, cones = CHECK['LOSS_COMPONENTS']['nominal_cones'](graph, blue)
    for index, row in enumerate(rows, 1):
        lost = CHECK['mask'](v * SHEETS + sheet + 4 for v, sheet in row)
        if lost & blue != lost or lost.bit_count() != SIZE:
            raise AssertionError(('Invalid seed coordinates', row))
        fort = CHECK['remaining_white'](graph, cones, lost)
        if fort & blue != lost or any(v % SHEETS in (0, SHEETS - 1) for v in CHECK['members'](fort)):
            raise AssertionError(('Witness lacks a guarded fort', row))
        for seed in CHECK['members'](lost):
            if CHECK['remaining_white'](graph, cones, lost ^ (1 << seed)):
                raise AssertionError(('Witness has a blocking proper subset', row, seed))
        if index % 5000 == 0:
            print(f'Checked {index} witnesses and all their one-seed restorations', flush=True)
    print(json.dumps({'blocks': BLOCKS, 'size': SIZE, 'near': len(rows),
                      'one_seed_restorations': SIZE * len(rows)}), flush=True)


def check_exhaustive(rows):
    near = BOUNDARY['near_seed_stages'](BLOCKS)
    anchors = BOUNDARY['anchor_stages'](BLOCKS)
    lower, size_30 = CHECK['catalogues_through_size_30'](BLOCKS)
    size_31 = BOUNDARY['transferred_catalogue'](BLOCKS)
    smaller = [row for row in (*lower, *size_30, *size_31) if near.issuperset(support(row))]
    archive = runpy.run_path(str(HERE / 'check_degree_33_ordinary.py'))
    ordinary = archive['read_catalogues']()[2]
    ordinary = {row for row in BOUNDARY['ordinary_placements'](ordinary, BLOCKS)
                if near.issuperset(support(row))}
    known = set(rows)
    if len(smaller) != 27149 or len(ordinary) != 552 or known & ordinary:
        raise AssertionError(('Unexpected exclusion families', len(smaller), len(ordinary)))
    known.update(ordinary)

    def restrict(clauses, seeds, order, sheets):
        return BOUNDARY['restrict_stages'](clauses, seeds, order, sheets, near, (anchors,))

    print(f'Excluding {len(smaller)} smaller losses and {len(known)} size-32 losses', flush=True)
    result = CHECK['enumerate_blockers'](
        BLOCKS, smaller, known, budget=SIZE, strip_sheets=SHEETS, require_minimal_fort=True,
        restrict=restrict, stream_blockers=True)
    if result != known:
        raise AssertionError(('Uncatalogued near-boundary losses', sorted(result - known)))
    print(json.dumps({'blocks': BLOCKS, 'size': SIZE, 'additional_near_losses': 0}), flush=True)


def check_outer_windows(last_span):
    representative = 37
    anchors = BOUNDARY['anchor_stages'](representative)
    near = BOUNDARY['near_seed_stages'](representative)
    counts = {}
    for span in range(5, last_span + 1):
        blocks = max(BLOCKS, span + 4)
        lower, size_30 = CHECK['catalogues_through_size_30'](blocks)
        lower = [(row, set(support(row)))
                 for row in (*lower, *size_30, *BOUNDARY['transferred_catalogue'](blocks))]
        checked = 0
        for first in range(representative):
            window = [(first + offset) % representative for offset in range(-2, span + 1)]
            arc = set(window[2:-1])
            if not (arc & anchors and arc - near):
                continue
            exceptional = 0 if 0 in window else representative - 1
            local_exceptional = 0 if exceptional == 0 else blocks - 1
            offset = window.index(exceptional)
            mapped = [(local_exceptional + i - offset) % blocks for i in range(len(window))]
            local_arc = mapped[2:-1]
            allowed = set(local_arc)
            required = [{local_arc[0]}, {local_arc[-1]},
                        {local for remote, local in zip(window, mapped) if remote in anchors},
                        {local for remote, local in zip(window, mapped) if remote not in near}]
            required.extend(set(local_arc[i:i + 3]) for i in range(1, span - 3))
            smaller = [row for row, stages in lower if stages <= allowed]

            def restrict(clauses, seeds, order, sheets):
                selected = BOUNDARY['restrict_stages'](
                    clauses, seeds, order, sheets, allowed, required, blocks=blocks)
                for left, right in zip(local_arc[1:-1], local_arc[2:-1]):
                    clauses.append([v + 1 for v in range(order)
                                    if BOUNDARY['stage'](v // sheets) in {left, right}])
                return selected

            result = CHECK['enumerate_blockers'](
                blocks, smaller, budget=SIZE, strip_sheets=SHEETS, require_minimal_fort=True,
                restrict=restrict, stream_blockers=True)
            if result:
                raise AssertionError(('Unexpected outer losses', first, span, sorted(result)))
            checked += 1
            print(json.dumps({'blocks': representative, 'first_stage': first, 'stage_span': span,
                              'outer_losses': 0}), flush=True)
        expected = 2 * span - 6 if span <= 10 else span + 4
        if checked != expected:
            raise AssertionError(('Unexpected outer window count', span, checked))
        counts[span] = checked
    print(json.dumps({'outer_window_counts': counts, 'total': sum(counts.values())}), flush=True)


def check_far_outer_windows():
    from pysat.card import ITotalizer
    from pysat.solvers import Solver

    blocks, minimum_span = 37, 23
    stage = BOUNDARY['stage']
    graph, blue, *_ = CHECK['COVER']['signed_prism_cover'](blocks, SHEETS)
    clauses, seeds, top = CHECK['STRIP']['strip_formula'](
        graph, blue, SIZE, sheets=SHEETS, quotient_bounds=False, require_minimal=True)
    seed_groups = [[] for _ in range(blocks)]
    fort_groups = [[] for _ in range(blocks)]
    for seed in seeds:
        seed_groups[stage((seed - 1) // SHEETS)].append(seed)
    for vertex in range(len(graph)):
        fort_groups[stage(vertex // SHEETS)].append(vertex + 1)

    anchors = BOUNDARY['anchor_stages'](blocks)
    outside = set(range(blocks)) - BOUNDARY['near_seed_stages'](blocks)
    for stages in (anchors, outside):
        clauses.append([seed for i in stages for seed in seed_groups[i]])

    occupied = list(range(top + 1, top + blocks + 1))
    starts = list(range(top + blocks + 1, top + 2 * blocks + 1))
    for mark, group in zip(occupied, seed_groups):
        clauses.append([-mark, *group])
        clauses.extend([-seed, mark] for seed in group)
    clauses.append(starts)
    for i, mark in enumerate(starts):
        clauses.append([-mark, occupied[i]])
        for offset in range(1, 5):
            clauses.append([-mark, -occupied[(i - offset) % blocks]])
        for offset in range(1, minimum_span - 2):
            triple = [(i + offset + delta) % blocks for delta in range(3)]
            clauses.append([-mark, *(occupied[s] for s in triple)])
            clauses.append([-mark, *fort_groups[triple[0]], *fort_groups[triple[1]]])

    lower, size_30 = CHECK['catalogues_through_size_30'](blocks)
    smaller = (*lower, *size_30, *BOUNDARY['transferred_catalogue'](blocks))
    if len(smaller) != 30359:
        raise AssertionError('Unexpected lower-order archive size')
    print(f'Checking anchored outer arcs of span at least {minimum_span}', flush=True)
    with ITotalizer(lits=seeds, ubound=SIZE, top_id=starts[-1]) as counter:
        with Solver(name='cadical195', bootstrap_with=clauses + counter.cnf.clauses) as solver:
            for row in smaller:
                for clause in CHECK['block_translations'](row, SHEETS):
                    solver.add_clause(clause)
            if solver.solve(assumptions=[-counter.rhs[SIZE]]):
                selected = {v for v in solver.get_model() if v > 0}
                loss = CHECK['normalized'](divmod(v - 1, SHEETS) for v in seeds if v in selected)
                raise AssertionError(('Unexpected candidate after a long seed gap', loss))
    print(json.dumps({'blocks': blocks, 'minimum_seed_span': minimum_span,
                      'outer_losses': 0}), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--exhaustive', action='store_true',
                       help='exclude every further loss in the guarded near-boundary strip')
    modes.add_argument('--outer-through', type=int, choices=range(5, 34), metavar='SPAN',
                       help='exclude outer losses of lengths five through SPAN')
    modes.add_argument('--far-outer', action='store_true',
                       help='exclude all anchored outer seed arcs of span at least 23')
    args = parser.parse_args()
    if args.far_outer:
        check_far_outer_windows()
    elif args.outer_through:
        check_outer_windows(args.outer_through)
    elif args.exhaustive:
        check_exhaustive(read_catalogue())
    else:
        check_witnesses(read_catalogue())
