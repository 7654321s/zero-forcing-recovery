"""Verify the degree-34 short outer catalogue and signed-overlap input."""
import argparse
from collections import Counter
import gzip
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
DEGREE_33 = runpy.run_path(str(HERE / 'check_degree_33_boundary.py'))
DEGREE_34 = runpy.run_path(str(HERE / 'check_degree_34_ordinary.py'))
BOUNDARY = DEGREE_33['BOUNDARY']
CHECK = DEGREE_33['CHECK']
STAGE_START = DEGREE_33['STAGE_START']
ORDINARY = DEGREE_33['ORDINARY']
BLOCKS, SHEETS = 13, 40


def transferred_size_33_losses(blocks, ordinary):
    if blocks < BLOCKS:
        raise ValueError('The transfer requires at least 13 blocks')
    near = (*DEGREE_33['read_opening_three_catalogue'](),
            *DEGREE_33['read_opening_four_catalogue'](),
            *(row for group in DEGREE_33['read_short_near_catalogue']().values() for row in group))
    first_terminal = STAGE_START(BLOCKS - 3)
    shift = STAGE_START(blocks - 3) - first_terminal
    rows = [tuple((v + shift if v >= first_terminal else v, s) for v, s in row) for row in near]
    rows.extend(tuple((v + STAGE_START(start), s) for v, s in row)
                for start in range(2, blocks - 3) for row in ordinary)
    if len(set(rows)) != len(rows) or len(rows) != 420 * blocks + 135691:
        raise AssertionError('Unexpected count of transferred size-33 losses')
    return tuple(rows)


def read_terminal_catalogue():
    with gzip.open(HERE / 'degree-34-terminal-span-four-catalogue.json.gz',
                   'rt', encoding='utf-8') as source:
        data = json.load(source)
    if (data['schema_version'], data['blocks'], data['size']) != (1, BLOCKS, 34):
        raise AssertionError('Unexpected terminal size-34 catalogue format')
    patterns = tuple(tuple(map(tuple, row)) for row in data['losses'])
    if len(patterns) != 8 or patterns != tuple(sorted(set(patterns))):
        raise AssertionError('Unexpected terminal size-34 type count')
    for row in patterns:
        if (len(row) != 34 or len(set(row)) != 34 or CHECK['normalized'](row) != row
                or CHECK['boundary_stage_arc'](row, BLOCKS)[:2] != (9, 4)):
            raise AssertionError(('Unexpected terminal size-34 coordinates', row))
    return patterns


def smaller_losses(blocks):
    families = ORDINARY['read_catalogues']()
    return (*DEGREE_33['transferred_smaller_losses'](blocks, families[2]),
            *transferred_size_33_losses(blocks, families[3]))


def check_overlap_input():
    rows = smaller_losses(BLOCKS)
    counts = Counter(map(len, rows))
    expected = {24: 5, 25: 20, 26: 97, 27: 258, 28: 741, 29: 1982,
                30: 6055, 31: 18633, 32: 53141, 33: 141151}
    if counts != expected or len(set(rows)) != len(rows):
        raise AssertionError(('Unexpected thirteen-block overlap catalogue', counts))
    stage_span = max(CHECK['boundary_stage_arc'](row, BLOCKS)[1] for row in rows)
    sheet_span = max(s for row in rows for _, s in row)
    groups = DEGREE_33['overlap_stage_components'](rows, BLOCKS, 34)
    components = list(map(len, groups))
    if (stage_span, sheet_span) != (4, 14) or components != [200484, 15171] + [803] * 8 + [4]:
        raise AssertionError(('Unexpected components or span', components, stage_span, sheet_span))
    ordinary = tuple(sorted(row for family in ORDINARY['read_catalogues']() for row in family))
    ordinary_start = min(v for row in ordinary for v, _ in row)
    for group in groups[2:-1]:
        offset = min(v for row in group for v, _ in row) - ordinary_start
        shifted = tuple(sorted(tuple((v - offset, s) for v, s in row) for row in group))
        if shifted != ordinary:
            raise AssertionError('An 803-type component is not an ordinary translate')
    small_weights, _ = CHECK['signed_union_weights'](groups[-1], 34)
    if small_weights[34] != {-1: 2}:
        raise AssertionError(('Unexpected four-type overlap profile', small_weights[34]))
    print(json.dumps({'blocks': BLOCKS, 'lower_losses': len(rows), 'components': components,
                      'stage_span': stage_span, 'sheet_span': sheet_span,
                      'small_component_correction': -4330}), flush=True)


def read_short_near_catalogue():
    with gzip.open(HERE / 'degree-34-short-near-catalogue.json.gz',
                   'rt', encoding='utf-8') as source:
        data = json.load(source)
    if (data['schema_version'], data['blocks'], data['size']) != (1, BLOCKS, 34):
        raise AssertionError('Unexpected short near size-34 catalogue format')
    windows = {}
    for entry in data['windows']:
        key = entry['start'], entry['span']
        rows = tuple(tuple(map(tuple, row)) for row in entry['losses'])
        if key in windows or rows != tuple(sorted(set(rows))) or any(
                len(row) != 34 or len(set(row)) != 34 or CHECK['normalized'](row) != row
                or CHECK['boundary_stage_arc'](row, BLOCKS)[:2] != key
                or not BOUNDARY['anchored'](row, BLOCKS) for row in rows):
            raise AssertionError(('Unexpected short near size-34 coordinates', key))
        windows[key] = rows
    counts = {key: len(rows) for key, rows in windows.items()}
    if counts != {(11, 2): 1305, (10, 3): 3893, (11, 3): 16481, (1, 3): 685, (10, 4): 74}:
        raise AssertionError(('Unexpected short near size-34 counts', counts))
    return windows


def replay_witnesses(patterns):
    graph, blue, *_ = CHECK['COVER']['signed_prism_cover'](BLOCKS, SHEETS)
    _, _, cones = CHECK['LOSS_COMPONENTS']['nominal_cones'](graph, blue)
    for row in patterns:
        loss = CHECK['mask'](v * SHEETS + s + 4 for v, s in row)
        if loss & blue != loss or loss.bit_count() != 34:
            raise AssertionError(('Invalid seed coordinates', row))
        fort = CHECK['remaining_white'](graph, cones, loss)
        if fort & blue != loss or any(v % SHEETS in (0, SHEETS - 1) for v in CHECK['members'](fort)):
            raise AssertionError(('No guarded fort', row))
        for seed in CHECK['members'](loss):
            if CHECK['remaining_white'](graph, cones, loss ^ (1 << seed)):
                raise AssertionError(('A proper subset blocks recovery', row, seed))
    print(json.dumps({'types': len(patterns), 'restorations': 34 * len(patterns)}), flush=True)


def check_short_windows(cases, *, extra_groups=()):
    by_stage = [(row, set(DEGREE_33['NEAR']['support'](row))) for row in smaller_losses(BLOCKS)]
    stage = BOUNDARY['stage']
    for arc, known in cases:
        allowed = set(arc)
        smaller = [row for row, stages in by_stage if stages <= allowed]
        required = ({arc[0]}, {arc[-1]}, *extra_groups)

        def restrict(clauses, seeds, order, period):
            selected = BOUNDARY['restrict_stages'](
                clauses, seeds, order, period, allowed, required, blocks=BLOCKS)
            if len(arc) == 4:
                middle = set(arc[1:3])
                clauses.append([v + 1 for v in range(order) if stage(v // period) in middle])
            return selected

        found = CHECK['enumerate_blockers'](
            BLOCKS, smaller, known, budget=34, strip_sheets=SHEETS, require_minimal_fort=True,
            restrict=restrict, stream_blockers=True)
        if found != known:
            raise AssertionError(('Additional short losses', arc, len(found - known)))
        print(json.dumps({'start': arc[0], 'span': len(arc), 'types': len(found)}), flush=True)


def ordinary_at(start):
    offset = STAGE_START(start)
    return {tuple((v + offset, s) for v, s in row) for row in DEGREE_34['read_catalogue']()}


def check_short_outer_windows():
    check_short_windows([([9, 10, 11], ordinary_at(9)), ([8, 9, 10, 11], set()),
                         ([9, 10, 11, 12], set(read_terminal_catalogue()))])


def check_short_near_windows(*, exhaustive):
    windows = read_short_near_catalogue()
    if not exhaustive:
        replay_witnesses(tuple(row for group in windows.values() for row in group))
        return
    cases = []
    for arc in DEGREE_33['short_near_windows'](BLOCKS):
        known = (ordinary_at(2) if arc == [2, 3, 4]
                 else set(windows.get((arc[0], len(arc)), ())))
        cases.append((arc, known))
    check_short_windows(cases, extra_groups=(BOUNDARY['anchor_stages'](BLOCKS),))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--short-outer', action='store_true', help='exhaust the three short outer arcs')
    modes.add_argument('--overlap-input', action='store_true', help='check the lower-order partition')
    modes.add_argument('--short-near', choices=('witnesses', 'exhaustive'),
                       help='check the short near-boundary catalogue or exhaust all its windows')
    args = parser.parse_args()
    if args.overlap_input:
        check_overlap_input()
    elif args.short_outer:
        check_short_outer_windows()
    elif args.short_near:
        check_short_near_windows(exhaustive=args.short_near == 'exhaustive')
    else:
        replay_witnesses(read_terminal_catalogue())
