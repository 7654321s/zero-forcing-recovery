"""Replay and exhaust the nonordinary size-32 losses near the exceptional stages."""

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
    _, ordinary, _ = CHECK['ordinary_size_32_catalogue']()
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


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--exhaustive', action='store_true',
                        help='exclude every further loss in the guarded near-boundary strip')
    args = parser.parse_args()
    rows = read_catalogue()
    if args.exhaustive:
        check_exhaustive(rows)
    else:
        check_witnesses(rows)
