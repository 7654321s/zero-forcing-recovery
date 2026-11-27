"""Verify short ordinary size-37 witnesses and cross-start exclusions."""
import argparse
from collections import Counter
import gzip
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
DEGREE_36 = runpy.run_path(str(HERE / 'check_degree_36_ordinary.py'))
DEGREE_35 = DEGREE_36['DEGREE_35']
ORDINARY = DEGREE_36['ORDINARY']
SHEETS = 47


def smaller_families():
    return (*ORDINARY['read_catalogues'](), DEGREE_35['DEGREE_34']['read_catalogue'](),
            DEGREE_35['read_catalogue'](), DEGREE_36['read_catalogue']())


def read_catalogue():
    with gzip.open(HERE / 'ordinary-size-37-short-catalogue.json.gz',
                   'rt', encoding='utf-8') as source:
        data = json.load(source)
    if (data['schema_version'], data['size']) != (1, 37):
        raise AssertionError('Unexpected size-37 catalogue format')
    rows = tuple(tuple(map(tuple, row)) for row in data['losses'])
    if len(rows) != 5909 or rows != tuple(sorted(set(rows))):
        raise AssertionError('Unexpected size-37 type count')
    profile = Counter()
    normalized = DEGREE_36['CHECK']['normalized']
    for row in rows:
        stages = {v // 16 for v, _ in row}
        if (len(row) != 37 or len(set(row)) != 37 or normalized(row) != row
                or stages not in ({0, 1, 2}, {0, 1, 2, 3})):
            raise AssertionError(('Unexpected ordinary size-37 coordinates', row))
        profile[len(stages), max(s for _, s in row)] += 1
    expected = {(3, 8): 15, (3, 9): 120, (3, 10): 202, (3, 11): 2284,
                (3, 12): 2855, (3, 13): 356, (4, 12): 2, (4, 13): 6,
                (4, 14): 63, (4, 15): 6}
    if profile != expected:
        raise AssertionError(('Unexpected stage and sheet spans', profile))
    return rows


def check_bands():
    check = DEGREE_36['CHECK']
    stage_band = check['SPAN']['BAND']['check_band']
    for blocks in (40, 41):
        stage_band(blocks, stages=39, budget=37)
        print(f'{blocks} blocks: the 39-stage band forces an empty adjacent pair', flush=True)
    check['check_ordinary_sheet_bands'](through=21, blocks=39)
    print('39 blocks: the width-21 sheet band requires 17 losses', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--different-starts', action='store_true',
                      help='exclude unions of lower losses at distinct ordinary starts')
    mode.add_argument('--window', type=int, choices=(3, 4),
                      help='exclude additional losses in the guarded stage window')
    mode.add_argument('--bands', action='store_true', help='check the stage and sheet bounds')
    args = parser.parse_args()
    if args.bands:
        check_bands()
    elif args.different_starts:
        DEGREE_36['check_no_overlaps_at_different_starts'](smaller_families(), budget=37)
    else:
        rows = read_catalogue()
        if args.window:
            ORDINARY['check_complete_window']((*smaller_families(), rows), args.window,
                                             budget=37, sheets=SHEETS)
        else:
            ORDINARY['replay_witnesses'](((37, rows),), blocks=9, sheets=SHEETS)
