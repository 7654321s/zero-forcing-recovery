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


def check_terminal_witnesses(patterns):
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
    print(json.dumps({'terminal_types': len(patterns), 'restorations': 34 * len(patterns)}), flush=True)


def check_short_outer_windows():
    patterns = read_terminal_catalogue()
    by_stage = [(row, set(DEGREE_33['NEAR']['support'](row))) for row in smaller_losses(BLOCKS)]
    ordinary = {tuple((v + STAGE_START(9), s) for v, s in row) for row in DEGREE_34['read_catalogue']()}
    stage = BOUNDARY['stage']
    for first, span, known in ((9, 3, ordinary), (8, 4, set()), (9, 4, set(patterns))):
        allowed = set(range(first, first + span))
        smaller = [row for row, stages in by_stage if stages <= allowed]
        last = first + span - 1

        def restrict(clauses, seeds, order, period):
            selected = BOUNDARY['restrict_stages'](
                clauses, seeds, order, period, allowed, ({first}, {last}), blocks=BLOCKS)
            if span == 4:
                clauses.append([v + 1 for v in range(order)
                                if stage(v // period) in {first + 1, first + 2}])
            return selected

        found = CHECK['enumerate_blockers'](
            BLOCKS, smaller, known, budget=34, strip_sheets=SHEETS, require_minimal_fort=True,
            restrict=restrict, stream_blockers=True)
        if found != known:
            raise AssertionError(('Additional short outer losses', first, span, len(found - known)))
        print(json.dumps({'start': first, 'span': span, 'types': len(found)}), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--short-outer', action='store_true', help='exhaust the three short outer arcs')
    modes.add_argument('--overlap-input', action='store_true', help='check the lower-order partition')
    args = parser.parse_args()
    if args.overlap_input:
        check_overlap_input()
    elif args.short_outer:
        check_short_outer_windows()
    else:
        check_terminal_witnesses(read_terminal_catalogue())
