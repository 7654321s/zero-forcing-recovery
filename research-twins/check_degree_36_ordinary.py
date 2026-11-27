"""Verify the complete ordinary size-36 catalogue and degree-36 overlap."""
import argparse
from collections import Counter
import gzip
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
DEGREE_35 = runpy.run_path(str(HERE / 'check_degree_35_ordinary.py'))
ORDINARY = DEGREE_35['ORDINARY']
CHECK = DEGREE_35['CHECK']
SHEETS = 45


def read_catalogue():
    with gzip.open(HERE / 'ordinary-size-36-short-catalogue.json.gz',
                   'rt', encoding='utf-8') as source:
        data = json.load(source)
    if (data['schema_version'], data['size']) != (1, 36):
        raise AssertionError('Unexpected size-36 catalogue format')
    rows = tuple(tuple(map(tuple, row)) for row in data['losses'])
    if len(rows) != 2505 or rows != tuple(sorted(set(rows))):
        raise AssertionError('Unexpected size-36 type count')
    profile = Counter()
    for row in rows:
        stages = {v // 16 for v, _ in row}
        if (len(row) != 36 or len(set(row)) != 36 or CHECK['normalized'](row) != row
                or stages not in ({0, 1, 2}, {0, 1, 2, 3})):
            raise AssertionError(('Unexpected ordinary size-36 coordinates', row))
        profile[len(stages), max(s for _, s in row)] += 1
    expected = {(3, 8): 6, (3, 9): 52, (3, 10): 71, (3, 11): 1048,
                (3, 12): 1252, (3, 13): 57, (4, 14): 19}
    if profile != expected:
        raise AssertionError(('Unexpected stage and sheet spans', profile))
    return rows


def check_no_overlaps_at_different_starts(families, *, budget=36):
    three_stage, four_stage = [], []
    for family in families:
        for row in family:
            loads = Counter(v // 16 for v, _ in row)
            if set(loads) == {0, 1, 2} and min(loads.values()) >= 6:
                three_stage.append(row)
            elif set(loads) == {0, 1, 2, 3} and min(loads[0], loads[3]) >= 2 and len(row) in (35, 36):
                four_stage.append(row)
            else:
                raise AssertionError(('The stage-count lower bounds do not apply', row))
    if (budget, len(four_stage)) not in ((36, 4), (37, 23)):
        raise AssertionError(('Unexpected scope for the distinct-start check', budget, len(four_stage)))

    # Two three-stage events at different starts of distance at least two
    # have at least twelve unshared losses. Adjacent starts add at least
    # six losses to either event. A three-stage event paired with a longer
    # event must fit inside that longer stage arc, since any unshared stage
    # adds at least six losses to a four-stage event of size at least 35.
    short = [row for row in three_stage if len(row) <= budget - 6]
    pairs = ((short, short, (1,)), (four_stage, three_stage, (1,)),
             (four_stage, four_stage, (1, 2, 3)))
    for left_rows, right_rows, offsets in pairs:
        for left in left_rows:
            left_set = set(left)
            by_label = {}
            for v, s in left:
                by_label.setdefault(v, []).append(s)
            for row in right_rows:
                for start in offsets:
                    right = tuple((v + 16 * start, s) for v, s in row)
                    shifts = {a - s for v, s in right for a in by_label.get(v, ())}
                    for offset in shifts:
                        union = left_set | {(v, s + offset) for v, s in right}
                        if len(union) <= budget:
                            raise AssertionError(('Unexpected overlap at distinct starts',
                                                  left, row, start, offset))
    print(json.dumps({'degree': budget, 'unions_at_different_starts': 0}), flush=True)


def check_overlap(families):
    check_no_overlaps_at_different_starts(families)
    lower = tuple(row for family in families for row in family)
    profiles, span = CHECK['signed_union_weights'](lower, 36)
    expected = {-2: 95, -1: 14658, 0: 10154, 1: 9376, 2: 99, 3: 1}
    if profiles[36] != expected or span != 14:
        raise AssertionError(('Unexpected degree-36 ordinary overlap', profiles[36], span))
    print(json.dumps({'degree': 36, 'overlap_weights': profiles[36], 'union_sheet_span': span,
                      'signed_correction': sum(w * n for w, n in profiles[36].items())}), flush=True)


def check_bands():
    band = CHECK['SPAN']['BAND']
    for blocks in (39, 40):
        band['check_band'](blocks, stages=38, budget=36)
        print(f'{blocks} blocks: the 38-stage band forces an empty adjacent pair', flush=True)
    CHECK['check_ordinary_sheet_bands'](through=23, blocks=38)
    print('38 blocks: the width-23 sheet band requires 19 losses', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--overlap', action='store_true', help='count the signed degree-36 unions')
    mode.add_argument('--window', type=int, choices=(3, 4, 5),
                      help='exclude additional losses in the guarded stage window')
    mode.add_argument('--seed-arcs', action='store_true', help='test for longer seed arcs')
    mode.add_argument('--bands', action='store_true', help='verify the stage and sheet bounds')
    args = parser.parse_args()
    if args.bands:
        check_bands()
    else:
        families = (*ORDINARY['read_catalogues'](), DEGREE_35['DEGREE_34']['read_catalogue'](),
                    DEGREE_35['read_catalogue']())
        if args.overlap:
            check_overlap(families)
        else:
            rows = read_catalogue()
            if args.window:
                ORDINARY['check_complete_window']((*families, rows), args.window, budget=36,
                                                 sheets=SHEETS)
            elif args.seed_arcs:
                ORDINARY['check_wider_seed_arcs']((*families, rows), budget=36, maximum_span=37,
                                                 sheets=SHEETS)
            else:
                ORDINARY['replay_witnesses'](((36, rows),), blocks=9, sheets=SHEETS)
