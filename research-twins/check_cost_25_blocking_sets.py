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
DIRECT_LAST = 14
LOCALITY_REPRESENTATIVE = 20
EXPECTED_SPANS = {
    4: {7: 1, 8: 7, 9: 8, 10: 4, 11: 2},
    **dict.fromkeys(range(5, LOCALITY_REPRESENTATIVE + 1), {7: 1, 8: 7, 9: 8, 10: 4}),
}
EXPECTED_SIZE_26_SPANS = {
    4: {7: 4, 8: 25, 9: 42, 10: 23, 11: 10},
    5: {7: 4, 8: 25, 9: 42, 10: 23, 11: 3},
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


def check_template_stages(templates):
    opening = SPAN['BAND']['stage_start'](1)
    stages = Counter(tuple(sorted({0 if v < opening else (v - opening) // 16 + 1
                                   for v, _ in template})) for template in templates)
    if stages != {(0, 1, 2): 16, (3, 4): 4}:
        raise AssertionError(('Unexpected occupied stages at five blocks', stages))


def enumerate_blockers(blocks, smaller, known=(), *, budget=25):
    sheets = budget + 10
    graph, blue, *_ = COVER['signed_prism_cover'](blocks, sheets)
    clauses, seeds, top = STRIP['strip_formula'](
        graph, blue, budget, sheets=sheets, quotient_bounds=False, require_minimal=False)
    for pattern in (*smaller, *sorted(known)):
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


def known_union_coefficients(blocks, minimum, near_minimum):
    """Count the signed unions through degree 26 generated by losses of sizes 24 and 25."""
    events = {frozenset(pattern) for pattern in (*minimum, *near_minimum)}
    unions = set(events)
    pending = list(events)
    while pending:
        union = pending.pop()
        last_sheet = max(s for _, s in union)
        for event in events:
            event_span = max(s for _, s in event)
            for shift in range(1 - event_span, last_sheet):
                moved = {(v, s + shift) for v, s in event}
                joined = union | moved
                if len(union) < len(joined) <= 26:
                    normalized_union = frozenset(normalized(joined))
                    if normalized_union not in unions:
                        unions.add(normalized_union)
                        pending.append(normalized_union)

    weights = {}
    coefficients = Counter()
    for union in sorted(unions, key=lambda sites: (len(sites), tuple(sorted(sites)))):
        last_sheet = max(s for _, s in union)
        if last_sheet > 11:
            raise AssertionError(('Unexpected span for a union through size 26', blocks, last_sheet))
        coefficient = 1
        for smaller, weight in weights.items():
            if len(smaller) < len(union):
                smaller_span = max(s for _, s in smaller)
                for shift in range(last_sheet - smaller_span + 1):
                    if all((v, s + shift) in union for v, s in smaller):
                        coefficient -= weight
        weights[union] = coefficient
        coefficients[len(union)] += coefficient

    expected = {24: 5, 25: len(near_minimum) - 2, 26: -16 if blocks == 4 else -15}
    if coefficients != expected:
        raise AssertionError(('Unexpected union coefficients', blocks, coefficients))
    return dict(sorted(coefficients.items()))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--blocks', choices=EXPECTED_SPANS, type=int, nargs='+',
                      default=tuple(EXPECTED_SPANS))
    mode.add_argument('--size-26', choices=EXPECTED_SIZE_26_SPANS, type=int, metavar='BLOCKS',
                      help='enumerate size-26 losses after excluding sizes 24 and 25')
    args = parser.parse_args()
    if args.size_26 is not None:
        blocks = args.size_26
        minimum = minimum_seed_sets(blocks)
        near = enumerate_blockers(blocks, minimum)
        if Counter(max(s for _, s in p) for p in near) != EXPECTED_SPANS[blocks]:
            raise AssertionError(('Unexpected size-25 seed catalogue', blocks))
        patterns = enumerate_blockers(blocks, (*minimum, *sorted(near)), budget=26)
        spans = Counter(max(s for _, s in p) for p in patterns)
        if spans != EXPECTED_SIZE_26_SPANS[blocks]:
            raise AssertionError(('Unexpected size-26 seed catalogue', blocks, spans))
        print(json.dumps({'blocks': blocks, 'size': 26, 'count': len(patterns),
                          'spans': dict(sorted(spans.items())), 'losses': sorted(patterns)}),
              flush=True)
        return
    templates = enumerate_blockers(5, minimum_seed_sets(5)) if any(k >= 5 for k in args.blocks) else ()
    if templates:
        check_template_stages(templates)
    for blocks in args.blocks:
        minimum = minimum_seed_sets(blocks)
        check_overlap(minimum)
        if blocks == 5:
            patterns = templates
        else:
            known = verify_inherited_patterns(blocks, minimum, templates) if blocks > 5 else ()
            patterns = enumerate_blockers(blocks, minimum, known) if blocks <= DIRECT_LAST else known
        spans = Counter(max(s for _, s in pattern) for pattern in patterns)
        if spans != EXPECTED_SPANS[blocks]:
            raise AssertionError(('Unexpected distribution of loss spans', blocks, spans))
        coefficients = known_union_coefficients(blocks, minimum, patterns)
        print(json.dumps({'blocks': blocks, 'count': len(patterns),
                          'spans': dict(sorted(spans.items())), 'losses': sorted(patterns),
                          'known_union_coefficients': coefficients}),
              flush=True)


if __name__ == '__main__':
    main()
