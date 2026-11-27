"""Verify the short outer windows in the degree-33 boundary representative."""

from pathlib import Path
import json
import runpy


HERE = Path(__file__).resolve().parent
ORDINARY = runpy.run_path(str(HERE / 'check_degree_33_ordinary.py'))
NEAR = runpy.run_path(str(HERE / 'check_degree_32_boundary.py'))
BOUNDARY = ORDINARY['BOUNDARY']
CHECK = ORDINARY['CHECK']
STAGE_START = ORDINARY['STAGE_START']


def check_short_outer_windows():
    blocks, representative, sheets = 13, 38, 40
    families = ORDINARY['read_catalogues']()
    ordinary_32 = BOUNDARY['ordinary_placements'](families[2], blocks)
    ordinary_32.update(tuple((v + STAGE_START(blocks - 4), s) for v, s in row)
                       for row in families[2])
    lower, size_30 = CHECK['catalogues_through_size_30'](blocks)
    smaller = (*lower, *size_30, *BOUNDARY['transferred_catalogue'](blocks),
               *ordinary_32, *NEAR['read_catalogue']())
    if len(set(smaller)) != len(smaller):
        raise AssertionError('A smaller loss was placed twice')
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


if __name__ == '__main__':
    check_short_outer_windows()
