"""Enumerate inclusion-minimal 25-seed losses in the integer prism lift."""

import argparse
from collections import Counter
import json
from pathlib import Path
import runpy

from pysat.card import ITotalizer
from pysat.solvers import Solver


HERE = Path(__file__).resolve().parent
SPAN = runpy.run_path(str(HERE / 'check_finite_fort_span.py'))
STRIP = runpy.run_path(str(HERE / 'check_finite_fort_strip.py'))
COVER = SPAN['COVER']
mask, members = SPAN['mask'], SPAN['members']
EXPECTED_SPANS = {
    4: {7: 1, 8: 7, 9: 8, 10: 4, 11: 2},
    **dict.fromkeys(range(5, 11), {7: 1, 8: 7, 9: 8, 10: 4}),
}


def minimum_seed_sets(blocks):
    _, seeds, _ = SPAN['guarded_strip'](4, 7)
    initial = mask(v * 9 + sheet for v, sheet in COVER['FOUR_BLOCK_FORT'])
    stage_start = SPAN['BAND']['stage_start']
    _, terminal = SPAN['patterns_from_optional_vertices'](
        8, stage_start(2), SPAN['TAIL_COMMON'], SPAN['TAIL_OPTIONAL'])
    _, opening = SPAN['patterns_from_optional_vertices'](
        9, 0, SPAN['OPENING_NINE_COMMON'], SPAN['OPENING_NINE_OPTIONAL'])
    terminal_shift = stage_start(blocks - 2) - stage_start(2)
    result = [tuple(divmod(v, 9) for v in members(initial & seeds))]
    result.extend(tuple((v + terminal_shift, s) for v, s in
                        (divmod(site, 10) for site in members(pattern)))
                  for pattern in sorted(terminal))
    result.extend(tuple(divmod(v, 11) for v in members(pattern)) for pattern in sorted(opening))
    if len(set(result)) != 5 or any(len(group) != 24 for group in result):
        raise AssertionError(('Unexpected minimum seed sets', blocks))
    return result


def normalized(sites, first=None):
    if first is None:
        first = min(s for _, s in sites)
    return tuple(sorted((v, s - first + 1) for v, s in sites))


def block_translations(pattern, sheets):
    last = max(s for _, s in pattern)
    for shift in range(sheets - 1 - last):
        yield [-(v * sheets + s + shift + 1) for v, s in pattern]


def verify_inherited_patterns(blocks, minimum, templates):
    stage_start = SPAN['BAND']['stage_start']
    patterns = set()
    for template in templates:
        shift = stage_start(blocks - 2) - stage_start(3) if template[0][0] >= stage_start(3) else 0
        pattern = tuple((v + shift, s) for v, s in template)
        sheets = max(s for _, s in pattern) + 10
        graph, blue, *_ = COVER['signed_prism_cover'](blocks, sheets)
        lost = mask(v * sheets + s + 4 for v, s in pattern)
        if lost & blue != lost or lost.bit_count() != 25:
            raise AssertionError(('Unexpected inherited seeds', blocks, pattern))
        arrival = COVER['MODEL']['trace'](graph, blue & ~lost)[1]
        fort = mask(v for v, time in enumerate(arrival) if time is None)
        if COVER['fort_cost'](graph, blue, fort) != 25 or any(
                v % sheets in (0, sheets - 1) for v in members(fort)):
            raise AssertionError(('Inherited loss has no finite fort', blocks, pattern))
        for smaller in minimum:
            for delta in range(sheets):
                projection = mask(v * sheets + (s + delta) % sheets for v, s in smaller)
                if projection & lost == projection:
                    raise AssertionError(('Inherited loss contains a minimum set', blocks, pattern))
        patterns.add(pattern)
    return patterns


def enumerate_blockers(blocks, minimum, known=()):
    sheets, budget = 35, 25
    graph, blue, *_ = COVER['signed_prism_cover'](blocks, sheets)
    clauses, seeds, top = STRIP['strip_formula'](
        graph, blue, budget, sheets=sheets, quotient_bounds=False, require_minimal=False)
    for pattern in (*minimum, *sorted(known)):
        clauses.extend(block_translations(pattern, sheets))

    patterns = set(known)
    with ITotalizer(lits=seeds, ubound=budget, top_id=top) as counter:
        with Solver(name='cadical195', bootstrap_with=clauses + counter.cnf.clauses) as solver:
            while solver.solve(assumptions=[-counter.rhs[budget]]):
                selected = {v for v in solver.get_model() if v > 0}
                fort = mask(v - 1 for v in selected if v <= len(graph))
                if COVER['fort_cost'](graph, blue, fort) != budget:
                    raise AssertionError(('Unexpected fort cost', blocks))
                sites = [divmod(v - 1, sheets) for v in seeds if v in selected]
                pattern = normalized(sites)
                if pattern in patterns:
                    raise AssertionError(('Repeated loss set', blocks))
                patterns.add(pattern)
                for clause in block_translations(pattern, sheets):
                    solver.add_clause(clause)
    return patterns


def check_overlap(minimum):
    unions = {}
    for first in minimum:
        for second in minimum:
            for shift in range(-8, 9):
                moved = tuple((v, s + shift) for v, s in second)
                union = set(first) | set(moved)
                if len(union) == 25:
                    origin = min(s for _, s in union)
                    subsets = unions.setdefault(normalized(union, origin), set())
                    subsets.update((normalized(first, origin), normalized(moved, origin)))
    if sorted(map(len, unions.values())) != [2, 2]:
        raise AssertionError('Unexpected overlap of minimum blocking sets')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--blocks', choices=EXPECTED_SPANS, type=int, nargs='+',
                        default=tuple(EXPECTED_SPANS))
    args = parser.parse_args()
    templates = enumerate_blockers(5, minimum_seed_sets(5)) if any(k >= 5 for k in args.blocks) else ()
    for blocks in args.blocks:
        minimum = minimum_seed_sets(blocks)
        check_overlap(minimum)
        if blocks == 5:
            patterns = templates
        else:
            known = verify_inherited_patterns(blocks, minimum, templates) if blocks > 5 else ()
            patterns = enumerate_blockers(blocks, minimum, known)
        spans = Counter(max(s for _, s in pattern) for pattern in patterns)
        if spans != EXPECTED_SPANS[blocks]:
            raise AssertionError(('Unexpected distribution of loss spans', blocks, spans))
        print(json.dumps({'blocks': blocks, 'count': len(patterns),
                          'spans': dict(sorted(spans.items())), 'losses': sorted(patterns)}),
              flush=True)


if __name__ == '__main__':
    main()
