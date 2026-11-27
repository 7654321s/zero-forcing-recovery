"""Verify short ordinary size-37 witnesses and cross-start exclusions."""
import argparse
from collections import Counter, defaultdict
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


def check_overlap():
    check = DEGREE_36['CHECK']
    families = smaller_families()
    DEGREE_36['check_no_overlaps_at_different_starts'](families, budget=37)
    profiles, span = check['signed_union_weights'](tuple(row for group in families for row in group), 37)
    expected = {-3: 1, -2: 222, -1: 28286, 0: 29749, 1: 24414, 2: 412, 3: 2}
    if profiles[37] != expected or span != 14:
        raise AssertionError(('Unexpected degree-37 overlap', profiles[37], span))
    total = sum(weight * count for weight, count in profiles[37].items())
    print(json.dumps({'degree': 37, 'overlap_weights': profiles[37],
                      'union_sheet_span': span, 'signed_correction': total}), flush=True)


def check_first_mixed_profiles():
    # At a distance of at least four the stage supports are disjoint.
    # One sheet has room for seven stages of sixteen labels after alignment.
    sheet_width, margin = 128, 16
    bounds = {34: 50, 35: 47, 36: 46, 37: 45}
    groups = defaultdict(list)
    for family in (*smaller_families(), read_catalogue()):
        for row in family:
            loads = [0] * 4
            for vertex, _ in row:
                loads[vertex // 16] += 1
            packed = sum(1 << (sheet_width * s + v) for v, s in row)
            groups[tuple(loads)].append((row, packed))

    hits = {cutoff: set() for cutoff in bounds}
    for distance in range(1, 4):
        padding = (0,) * distance
        for left_loads, left_rows in groups.items():
            if not any(left_loads[distance:]):
                continue
            for right_loads, right_rows in groups.items():
                lower = sum(max(a, b) for a, b in
                            zip(left_loads + padding, padding + right_loads))
                degree = max(sum(left_loads), sum(right_loads))
                relevant = [cutoff for cutoff, bound in bounds.items()
                            if degree <= cutoff and lower <= bound]
                if not relevant:
                    continue
                for left, packed_left in left_rows:
                    sheets_by_label = defaultdict(list)
                    for v, s in left:
                        sheets_by_label[v].append(s)
                    first = packed_left << (margin * sheet_width)
                    stage_offset = 16 * distance
                    for right, packed_right in right_rows:
                        second = packed_right << stage_offset
                        offsets = {margin + a - s for v, s in right
                                   for a in sheets_by_label.get(v + stage_offset, ())}
                        for offset in offsets:
                            union = first | (second << (offset * sheet_width))
                            size = union.bit_count()
                            for cutoff in relevant:
                                if size < bounds[cutoff]:
                                    raise AssertionError(('A smaller mixed union exists', cutoff, size))
                                if size == bounds[cutoff]:
                                    start = ((union & -union).bit_length() - 1) // sheet_width
                                    hits[cutoff].add(union >> (sheet_width * start))
    counts = {cutoff: len(unions) for cutoff, unions in hits.items()}
    if counts != {34: 3, 35: 14, 36: 6, 37: 3}:
        raise AssertionError(('Unexpected first mixed union counts', counts))
    print(json.dumps({cutoff: {'minimum': bounds[cutoff], 'unions': count,
                               'signed_correction': -count}
                      for cutoff, count in counts.items()}), flush=True)


def check_bands():
    check = DEGREE_36['CHECK']
    stage_band = check['SPAN']['BAND']['check_band']
    for blocks in (40, 41):
        stage_band(blocks, stages=39, budget=37)
        print(f'{blocks} blocks: the 39-stage band forces an empty adjacent pair', flush=True)
    check['check_ordinary_sheet_bands'](through=23, blocks=39)
    print('39 blocks: the width-23 sheet band requires 19 losses', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--different-starts', action='store_true',
                      help='exclude unions of lower losses at distinct ordinary starts')
    mode.add_argument('--window', type=int, choices=(3, 4, 5),
                      help='exclude additional losses in the guarded stage window')
    mode.add_argument('--bands', action='store_true', help='check the stage and sheet bounds')
    mode.add_argument('--overlap', action='store_true', help='check signed unions through degree 37')
    mode.add_argument('--first-mixed', action='store_true',
                      help='check the first mixed unions of the four nested catalogues')
    args = parser.parse_args()
    if args.bands:
        check_bands()
    elif args.overlap:
        check_overlap()
    elif args.first_mixed:
        check_first_mixed_profiles()
    elif args.different_starts:
        DEGREE_36['check_no_overlaps_at_different_starts'](smaller_families(), budget=37)
    else:
        rows = read_catalogue()
        if args.window:
            ORDINARY['check_complete_window']((*smaller_families(), rows), args.window,
                                             budget=37, sheets=SHEETS)
        else:
            ORDINARY['replay_witnesses'](((37, rows),), blocks=9, sheets=SHEETS)
