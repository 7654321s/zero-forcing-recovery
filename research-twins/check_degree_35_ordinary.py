"""Verify the ordinary size-35 witnesses and degree-35 overlap correction."""

import argparse
from collections import Counter
import gzip
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
DEGREE_34 = runpy.run_path(str(HERE / 'check_degree_34_ordinary.py'))
ORDINARY = DEGREE_34['ORDINARY']
CHECK = DEGREE_34['CHECK']
SHEETS = 44


def read_catalogue():
    with gzip.open(HERE / 'ordinary-size-35-catalogue.json.gz', 'rt', encoding='utf-8') as source:
        data = json.load(source)
    if (data['schema_version'], data['size']) != (1, 35):
        raise AssertionError('Unexpected size-35 catalogue format')
    rows = tuple(tuple(map(tuple, row)) for row in data['losses'])
    if (len(rows) != 1310 or rows != tuple(sorted(set(rows)))
            or any(len(row) != 35 or len(set(row)) != 35 or CHECK['normalized'](row) != row
                   for row in rows)):
        raise AssertionError('Unexpected ordinary size-35 catalogue entries')
    counts = Counter()
    for row in rows:
        stages = {v // 16 for v, _ in row}
        if stages not in ({0, 1, 2}, {0, 1, 2, 3}):
            raise AssertionError(('Unexpected ordinary seed stages', row))
        counts[len(stages), max(sheet for _, sheet in row)] += 1
    expected = {(3, 8): 2, (3, 9): 33, (3, 10): 32, (3, 11): 642,
                (3, 12): 594, (3, 13): 3, (4, 14): 4}
    if counts != expected:
        raise AssertionError(('Unexpected ordinary stage and sheet spans', counts))
    return rows


def check_overlap(families):
    smaller = tuple(row for f in families for row in f)
    weights, span = CHECK['signed_union_weights'](smaller, 35)
    expected = {-2: 34, -1: 4922, 0: 2911, 1: 5567, 2: 22}
    if weights[35] != expected or span != 12:
        raise AssertionError(('Unexpected degree-35 ordinary overlap', weights[35], span))
    print(json.dumps({'degree': 35, 'overlap_weights': weights[35], 'union_sheet_span': span,
                      'signed_correction': sum(w * n for w, n in weights[35].items())}), flush=True)


def check_bounds():
    band = CHECK['SPAN']['BAND']
    for blocks in (38, 39):
        band['check_band'](blocks, stages=37, budget=35)
        print(f'{blocks} blocks: the 37-stage band forces an empty adjacent pair', flush=True)
    CHECK['check_ordinary_sheet_bands'](through=21, blocks=37)
    print('37 blocks: the width-21 sheet band requires 17 losses', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--window', type=int, choices=(3, 4, 5, 36),
                      help='check for additional losses in the given finite stage window')
    mode.add_argument('--seed-arcs', action='store_true',
                      help='check ordinary seed arcs of lengths four through 36')
    mode.add_argument('--bounds', action='store_true',
                      help='certify the ordinary stage and sheet bounds')
    args = parser.parse_args()
    if args.bounds:
        check_bounds()
    else:
        smaller = (*ORDINARY['read_catalogues'](), DEGREE_34['read_catalogue']())
        rows = read_catalogue()
        families = (*smaller, rows)
        if args.window:
            ORDINARY['check_complete_window'](families, args.window, budget=35, sheets=SHEETS)
        elif args.seed_arcs:
            ORDINARY['check_wider_seed_arcs'](families, budget=35, maximum_span=36, sheets=SHEETS)
        else:
            ORDINARY['replay_witnesses'](((35, rows),), blocks=9, sheets=SHEETS)
            check_overlap(smaller)
