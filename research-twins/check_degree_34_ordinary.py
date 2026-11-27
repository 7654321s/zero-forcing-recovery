"""Verify the size-34 ordinary catalogue and its degree-34 overlaps."""

import argparse
from collections import Counter
import gzip
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
ORDINARY = runpy.run_path(str(HERE / 'check_degree_33_ordinary.py'))
CHECK = ORDINARY['CHECK']


def read_catalogue():
    with gzip.open(HERE / 'ordinary-size-34-catalogue.json.gz', 'rt', encoding='utf-8') as src:
        data = json.load(src)
    if (data['schema_version'], data['size']) != (1, 34):
        raise AssertionError('Unexpected size-34 catalogue format')

    rows = tuple(tuple(map(tuple, row)) for row in data['losses'])
    if (len(rows) != 685 or rows != tuple(sorted(set(rows)))
            or any(len(set(row)) != 34 or len(row) != 34 or CHECK['normalized'](row) != row
                   or {v // 16 for v, _ in row} != {0, 1, 2} for row in rows)):
        raise AssertionError('Unexpected ordinary size-34 catalogue entries')
    spans = Counter(max(s for _, s in row) for row in rows)
    if spans != {9: 9, 10: 9, 11: 410, 12: 257}:
        raise AssertionError(('Unexpected ordinary size-34 sheet spans', spans))
    return rows


def check_overlap(families):
    smaller = tuple(row for family in families for row in family)
    weights, span = CHECK['signed_union_weights'](smaller, 34)
    expected = {-2: 9, -1: 2362, 0: 631, 1: 1827, 2: 6}
    if weights[34] != expected or span != 12:
        raise AssertionError(('Unexpected degree-34 ordinary overlap', weights[34], span))
    print(json.dumps({'degree': 34, 'overlap_weights': weights[34], 'union_sheet_span': span,
                      'signed_correction': sum(w * n for w, n in weights[34].items())}), flush=True)


def check_bounds():
    band = CHECK['SPAN']['BAND']
    for blocks in (37, 38):
        band['check_band'](blocks, stages=36, budget=34)
        print(f'{blocks} blocks: the 36-stage band forces an empty adjacent pair', flush=True)
    CHECK['check_ordinary_sheet_bands'](through=27, blocks=36)
    print('36 blocks: the width-27 sheet band requires 23 losses', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--window', type=int, choices=(3, 4, 5, 35),
                      help='check for additional losses in the given finite stage window')
    mode.add_argument('--seed-arcs', action='store_true',
                      help='exclude wider ordinary seed arcs of lengths four through 35')
    mode.add_argument('--bounds', action='store_true',
                      help='certify the ordinary stage and sheet bounds')
    args = parser.parse_args()
    if args.bounds:
        check_bounds()
    else:
        smaller = ORDINARY['read_catalogues']()
        rows = read_catalogue()
        all_families = (*smaller, rows)
        if args.window:
            ORDINARY['check_complete_window'](all_families, args.window, budget=34)
        elif args.seed_arcs:
            ORDINARY['check_wider_seed_arcs'](all_families, budget=34, maximum_span=35)
        else:
            ORDINARY['replay_witnesses'](((34, rows),))
            check_overlap(smaller)
