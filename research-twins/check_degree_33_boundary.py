"""Verify the degree-33 boundary windows and overlap representative."""

import argparse
import gzip
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
ORDINARY = runpy.run_path(str(HERE / 'check_degree_33_ordinary.py'))
NEAR = runpy.run_path(str(HERE / 'check_degree_32_boundary.py'))
BOUNDARY = ORDINARY['BOUNDARY']
CHECK = ORDINARY['CHECK']
STAGE_START = ORDINARY['STAGE_START']


def transferred_smaller_losses(blocks, ordinary_32):
    lower, size_30 = CHECK['catalogues_through_size_30'](blocks)
    ordinary = BOUNDARY['ordinary_placements'](ordinary_32, blocks)
    ordinary.update(tuple((v + STAGE_START(blocks - 4), s) for v, s in row)
                    for row in ordinary_32)
    first_terminal = NEAR['BLOCKS'] - 3
    shift = STAGE_START(blocks - 3) - STAGE_START(first_terminal)
    near = (tuple((v + shift if BOUNDARY['stage'](v) >= first_terminal else v, s)
                  for v, s in row) for row in NEAR['read_catalogue']())
    smaller = (*lower, *size_30, *BOUNDARY['transferred_catalogue'](blocks), *ordinary, *near)
    if len(set(smaller)) != len(smaller):
        raise AssertionError('A smaller loss was placed twice')
    return smaller


def check_overlap_representative():
    blocks = 12
    smaller = transferred_smaller_losses(blocks, ORDINARY['read_catalogues']()[2])
    if (len(smaller) != 80549
            or any(CHECK['boundary_stage_arc'](row, blocks)[1] > 4 for row in smaller)
            or max(s for row in smaller for _, s in row) != 13):
        raise AssertionError('Unexpected lower-order families in the overlap representative')
    print(f'Counting degree-33 unions of {len(smaller)} smaller losses', flush=True)
    profiles, span = CHECK['signed_union_weights'](smaller, 33)
    counts = {degree: sum(weight * multiplicity for weight, multiplicity in profile.items())
              for degree, profile in profiles.items()}
    if counts[31] != 89 * blocks + 4238 or counts[32] != 71 * blocks + 6269:
        raise AssertionError('The lower-degree coefficients differ from the certified values')
    print(json.dumps({'blocks': blocks, 'largest_sheet_span': span, 'weights': profiles[33],
                      'overlap_per_sheet': counts[33],
                      'boundary_intercept': counts[33] + 980 * blocks}), flush=True)


def check_short_outer_windows():
    blocks, representative, sheets = 13, 38, 40
    families = ORDINARY['read_catalogues']()
    smaller = transferred_smaller_losses(blocks, families[2])
    supports = [(row, set(NEAR['support'](row))) for row in smaller]

    for first, span in ((34, 3), (33, 4), (34, 4)):
        local = first - (representative - blocks)
        last = local + span - 1
        allowed = set(range(local, last + 1))
        contained = [row for row, stages in supports if stages <= allowed]

        def restrict(clauses, seeds, order, period):
            return BOUNDARY['restrict_stages'](
                clauses, seeds, order, period, allowed, ({local}, {last}), blocks=blocks)

        actual = CHECK['enumerate_blockers'](
            blocks, contained, budget=33, strip_sheets=sheets, require_minimal_fort=True,
            restrict=restrict, stream_blockers=True)
        expected = {tuple((v + STAGE_START(local), s) for v, s in row)
                    for row in families[3]} if span == 3 else set()
        if actual != expected:
            raise AssertionError(('Unexpected short outer catalogue', first, span,
                                  len(actual), len(expected)))
        print(json.dumps({'blocks': representative, 'start': first, 'span': span,
                          'losses': len(actual)}), flush=True)


def short_near_windows(blocks):
    region = [blocks - 3, blocks - 2, blocks - 1, *range(6)]
    opening = {0, 1, 2}
    anchors = BOUNDARY['anchor_stages'](blocks)
    for span in range(1, 5):
        for offset in range(len(region) - span + 1):
            arc = region[offset:offset + span]
            stages = set(arc)
            if stages & anchors and not opening <= stages:
                yield arc


def read_short_near_catalogue():
    blocks = 13
    with gzip.open(HERE / 'degree-33-short-near-catalogue.json.gz', 'rt', encoding='utf-8') as src:
        archive = json.load(src)
    if (archive['schema_version'], archive['blocks'], archive['size']) != (1, blocks, 33):
        raise AssertionError('Unexpected short near-boundary catalogue format')
    grouped = {}
    for item in archive['windows']:
        key = item['start'], item['span']
        rows = tuple(tuple(map(tuple, row)) for row in item['losses'])
        if (key in grouped or rows != tuple(sorted(set(rows))) or
                any(len(row) != 33 or len(set(row)) != 33 or CHECK['normalized'](row) != row or
                    CHECK['boundary_stage_arc'](row, blocks)[:2] != key or
                    not BOUNDARY['anchored'](row, blocks) for row in rows)):
            raise AssertionError(('Unexpected short near-boundary loss', key))
        grouped[key] = rows
    counts = {key: len(rows) for key, rows in grouped.items()}
    if counts != {(11, 2): 634, (10, 3): 1757, (11, 3): 6722, (1, 3): 420, (10, 4): 4}:
        raise AssertionError(('Unexpected short near-boundary counts', counts))
    return grouped


def check_short_near_catalogue(*, exhaustive=False):
    blocks, sheets = 13, 40
    grouped = read_short_near_catalogue()
    windows = tuple(short_near_windows(blocks))
    if len(windows) != 20:
        raise AssertionError('Unexpected number of short near-boundary windows')
    if not exhaustive:
        graph, blue, *_ = CHECK['COVER']['signed_prism_cover'](blocks, sheets)
        _, _, cones = CHECK['LOSS_COMPONENTS']['nominal_cones'](graph, blue)
        for rows in grouped.values():
            for row in rows:
                lost = CHECK['mask'](v * sheets + s + 4 for v, s in row)
                if lost & blue != lost or lost.bit_count() != 33:
                    raise AssertionError(('Invalid seed coordinates', row))
                fort = CHECK['remaining_white'](graph, cones, lost)
                if fort & blue != lost or any(v % sheets in (0, sheets - 1)
                                              for v in CHECK['members'](fort)):
                    raise AssertionError(('No guarded fort', row))
                for seed in CHECK['members'](lost):
                    if CHECK['remaining_white'](graph, cones, lost ^ (1 << seed)):
                        raise AssertionError(('A proper subset blocks recovery', row, seed))
        print(json.dumps({'checked': 9537, 'restorations': 9537 * 33}), flush=True)
        return

    families = ORDINARY['read_catalogues']()
    smaller = transferred_smaller_losses(blocks, families[2])
    supports = [(row, set(NEAR['support'](row))) for row in smaller]
    anchors = BOUNDARY['anchor_stages'](blocks)
    for arc in windows:
        allowed = set(arc)
        first, last = arc[0], arc[-1]
        contained = [row for row, stages in supports if stages <= allowed]
        known = set(grouped.get((first, len(arc)), ()))
        if arc == [2, 3, 4]:
            known.update(tuple((v + STAGE_START(2), s) for v, s in row) for row in families[3])

        def restrict(clauses, seeds, order, period):
            return BOUNDARY['restrict_stages'](
                clauses, seeds, order, period, allowed, ({first}, {last}, anchors), blocks=blocks)

        result = CHECK['enumerate_blockers'](
            blocks, contained, known, budget=33, strip_sheets=sheets, require_minimal_fort=True,
            restrict=restrict, stream_blockers=True)
        if result != known:
            raise AssertionError(('Additional short near-boundary losses', arc, len(result - known)))
        print(json.dumps({'start': first, 'span': len(arc), 'catalogued': len(known)}), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--overlap', action='store_true',
                      help='count the signed degree-33 unions in the twelve-block representative')
    mode.add_argument('--near-short', choices=('witnesses', 'exhaustive'),
                      help='replay the short near-boundary windows omitting an opening stage')
    args = parser.parse_args()
    if args.overlap:
        check_overlap_representative()
    elif args.near_short:
        check_short_near_catalogue(exhaustive=args.near_short == 'exhaustive')
    else:
        check_short_outer_windows()
