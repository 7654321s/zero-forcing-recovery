"""Verify the ordinary size-33 losses and the degree-33 overlap correction."""

import argparse
from collections import Counter
import gzip
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
BOUNDARY = runpy.run_path(str(HERE / 'check_degree_31_boundary.py'))
CHECK = BOUNDARY['CHECK']
STAGE_START = BOUNDARY['stage_start']
SHEETS = 41


def read_catalogues():
    with gzip.open(HERE / 'thirteen-block-size-30-catalogue.json.gz', 'rt', encoding='utf-8') as src:
        size_30 = {tuple((v - STAGE_START(5), s) for v, s in row)
                   for row in json.load(src)['losses']
                   if CHECK['boundary_stage_arc'](row, 13)[:2] == (5, 3)}
    _, terminal = BOUNDARY['read_boundary_catalogue']()
    size_31 = {tuple((v - STAGE_START(32), s) for v, s in row) for row in terminal}

    with gzip.open(HERE / 'ordinary-size-32-and-33-catalogue.json.gz', 'rt', encoding='utf-8') as src:
        archive = json.load(src)
    if archive['schema_version'] != 1:
        raise AssertionError('Unexpected ordinary catalogue format')
    families = [tuple(sorted(size_30)), tuple(sorted(size_31))]
    for degree, counts in ((32, {10: 8, 11: 268}), (33, {10: 3, 11: 382, 12: 35})):
        rows = tuple(tuple(map(tuple, row)) for row in archive['losses'][str(degree)])
        if rows != tuple(sorted(set(rows))) or Counter(max(s for _, s in row) for row in rows) != counts:
            raise AssertionError(('Unexpected ordinary catalogue', degree))
        families.append(rows)
    if tuple(map(len, families)) != (10, 97, 276, 420):
        raise AssertionError('Unexpected ordinary catalogue sizes')
    for degree, family in enumerate(families, 30):
        for row in family:
            stage_count = Counter(v // 16 for v, _ in row)
            if (len(set(row)) != degree or len(row) != degree or row != CHECK['normalized'](row)
                    or set(stage_count) != {0, 1, 2} or min(stage_count.values()) < 6):
                raise AssertionError(('Unexpected ordinary coordinates', degree, row))
    return families


def replay_witnesses(families, *, blocks=8, sheets=SHEETS):
    graph, blue, *_ = CHECK['COVER']['signed_prism_cover'](blocks, sheets)
    _, _, cones = CHECK['LOSS_COMPONENTS']['nominal_cones'](graph, blue)
    for degree, rows in families:
        for row in rows:
            lost = CHECK['mask']((v + STAGE_START(2)) * sheets + s + 4 for v, s in row)
            if lost & blue != lost or lost.bit_count() != degree:
                raise AssertionError(('Wrong initial seed sites', degree, row))
            white = CHECK['remaining_white'](graph, cones, lost)
            if white & blue != lost or any(v % sheets in (0, sheets - 1)
                                          for v in CHECK['members'](white)):
                raise AssertionError(('No guarded fort for witness', degree, row))
            for seed in CHECK['members'](lost):
                if CHECK['remaining_white'](graph, cones, lost ^ (1 << seed)):
                    raise AssertionError(('A proper subset blocks recovery', degree, row, seed))
        print(json.dumps({'size': degree, 'witnesses': len(rows),
                          'restorations': degree * len(rows)}), flush=True)


def check_overlap(families):
    smaller = tuple(row for family in families[:3] for row in family)
    profile, span = CHECK['signed_union_weights'](smaller, 33)
    expected = {-2: 2, -1: 1144, 0: 89, 1: 168}
    if profile[33] != expected or span != 11:
        raise AssertionError(('Unexpected degree-33 overlap', profile[33], span))
    print(json.dumps({'degree': 33, 'overlap_weights': profile[33], 'union_sheet_span': span,
                      'signed_correction': sum(w * n for w, n in profile[33].items())}), flush=True)


def check_complete_window(families, width, *, budget=33, sheets=SHEETS):
    smaller = tuple(row for family in families[:-1] for row in family)
    known = CHECK['ordinary_placements'](families[-1], width)
    blocks = width + (4 if width == budget + 1 else 5)
    result = CHECK['enumerate_blockers'](
        blocks, CHECK['ordinary_placements'](smaller, width), known,
        budget=budget, ordinary_stages=width, first_ordinary_stage=True, strip_sheets=sheets,
        require_minimal_fort=True, stream_blockers=True)
    if result != known:
        raise AssertionError(('Unexpected additional ordinary losses', budget, width, sorted(result - known)))
    print(json.dumps({'ordinary_stages': width, 'size': budget, 'additional_losses': 0,
                      f'excluded_size_{budget}': len(known)}), flush=True)


def check_finite_representative():
    band = CHECK['SPAN']['BAND']
    for blocks in (36, 37):
        band['check_band'](blocks, stages=35, budget=33)
        print(f'{blocks} blocks: the 35-stage band forces an empty adjacent pair', flush=True)
    CHECK['check_ordinary_sheet_bands'](through=21, blocks=38)
    print('38 blocks: the width-21 sheet band requires 17 losses', flush=True)


def check_wider_seed_arcs(families, *, budget=33, maximum_span=34, sheets=SHEETS):
    smaller_templates = tuple(row for family in families[:-1] for row in family)
    stage = BOUNDARY['stage']
    for span in range(4, maximum_span + 1):
        blocks = span + 6
        arc = list(range(3, 3 + span))
        allowed = set(arc)
        required = [{arc[0]}, {arc[-1]},
                    *(set(arc[i:i + 3]) for i in range(1, span - 3))]
        smaller = [tuple((v + 16, sheet) for v, sheet in row)
                   for row in CHECK['ordinary_placements'](smaller_templates, span)]

        def restrict(clauses, seeds, order, sheets):
            selected = BOUNDARY['restrict_stages'](
                clauses, seeds, order, sheets, allowed, required, blocks=blocks)
            if span == maximum_span:
                # Including the predecessor would exceed the fort span bound.
                clauses.extend([-(v + 1)] for v in range(order) if stage(v // sheets) == 2)
            for left, right in zip(arc[1:-1], arc[2:-1]):
                clauses.append([v + 1 for v in range(order)
                                if stage(v // sheets) in {left, right}])
            return selected

        known = {tuple((v + STAGE_START(3), s) for v, s in row)
                 for row in families[-1] if 1 + max(v // 16 for v, _ in row) == span}
        result = CHECK['enumerate_blockers'](
            blocks, smaller, known, budget=budget, strip_sheets=sheets, require_minimal_fort=True,
            restrict=restrict, stream_blockers=True)
        if result != known:
            raise AssertionError(('Unexpected wider ordinary loss', span, sorted(result - known)))
        print(json.dumps({'seed_span': span, 'size': budget, 'catalogued': len(known),
                          'additional_losses': 0}), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--window', type=int, choices=(3, 4, 5, 34),
                      help='check for additional losses in the given finite stage window')
    mode.add_argument('--seed-arcs', action='store_true',
                      help='exclude each wider ordinary seed arc of length four through 34')
    mode.add_argument('--bounds', action='store_true',
                      help='certify the ordinary stage and sheet bounds')
    args = parser.parse_args()
    if args.bounds:
        check_finite_representative()
    else:
        families = read_catalogues()
        if args.window:
            check_complete_window(families, args.window)
        elif args.seed_arcs:
            check_wider_seed_arcs(families)
        else:
            replay_witnesses(zip((32, 33), families[2:]))
            check_overlap(families)
