"""Enumerate small inclusion-minimal seed losses in the integer prism lift."""

import argparse
from collections import Counter, defaultdict
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
DIRECT_SIZE_27_LAST = 13
LOCALITY_REPRESENTATIVE = 20
EXPECTED_SPANS = {
    4: {7: 1, 8: 7, 9: 8, 10: 4, 11: 2},
    **dict.fromkeys(range(5, LOCALITY_REPRESENTATIVE + 1), {7: 1, 8: 7, 9: 8, 10: 4}),
}
EXPECTED_SIZE_26_SPANS = {
    4: {7: 4, 8: 25, 9: 42, 10: 23, 11: 10},
    **dict.fromkeys(range(5, LOCALITY_REPRESENTATIVE + 1), {7: 4, 8: 25, 9: 42, 10: 23, 11: 3}),
}


EXPECTED_SIZE_27_SPANS = {
    4: {7: 5, 8: 64, 9: 110, 10: 68, 11: 28, 12: 1, 13: 1},
    **dict.fromkeys(range(5, LOCALITY_REPRESENTATIVE + 1), {7: 5, 8: 64, 9: 109, 10: 66, 11: 14}),
}


EXPECTED_SIZE_28_SPANS = {5: {7: 13, 8: 129, 9: 301, 10: 218, 11: 80}}


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


def verify_inherited_patterns(blocks, smaller, templates, *, budget=25):
    stage_start = SPAN['BAND']['stage_start']
    terminal = stage_start(3)
    shift = stage_start(blocks - 2) - terminal
    smaller = tuple(smaller)
    covers = {}
    patterns = set()
    for template in templates:
        pattern = tuple((v + shift if v >= terminal else v, s) for v, s in template)
        sheets = max(s for _, s in pattern) + 10
        if budget == 27:
            sheets = max(sheets, 31)
        if sheets not in covers:
            graph, blue, *_ = COVER['signed_prism_cover'](blocks, sheets)
            smaller_translates = tuple(
                mask(v * sheets + (s + delta) % sheets for v, s in smaller_pattern)
                for smaller_pattern in smaller for delta in range(sheets)
            )
            covers[sheets] = (graph, blue, smaller_translates)
        graph, blue, smaller_translates = covers[sheets]
        lost = mask(v * sheets + s + 4 for v, s in pattern)
        if lost & blue != lost or lost.bit_count() != budget:
            raise AssertionError(('Unexpected inherited seeds', blocks, pattern))
        arrival = COVER['MODEL']['trace'](graph, blue & ~lost)[1]
        fort = mask(v for v, time in enumerate(arrival) if time is None)
        if COVER['fort_cost'](graph, blue, fort) != budget or any(
                v % sheets in (0, sheets - 1) for v in members(fort)):
            raise AssertionError(('Inherited loss has no finite fort', blocks, pattern))
        if any(projection & lost == projection for projection in smaller_translates):
            raise AssertionError(('Inherited loss contains a smaller pattern', blocks, pattern))
        patterns.add(pattern)
    return patterns


def check_template_stages(templates, expected):
    opening = SPAN['BAND']['stage_start'](1)
    stages = Counter(tuple(sorted({0 if v < opening else (v - opening) // 16 + 1
                                   for v, _ in template})) for template in templates)
    if stages != expected:
        raise AssertionError(('Unexpected occupied stages at five blocks', stages))


def enumerate_blockers(blocks, smaller, known=(), *, budget=25, ordinary_stages=None,
                       first_ordinary_stage=False):
    sheets = budget + 10
    graph, blue, *_ = COVER['signed_prism_cover'](blocks, sheets)
    clauses, seeds, top = STRIP['strip_formula'](
        graph, blue, budget, sheets=sheets, quotient_bounds=False, require_minimal=False)
    if ordinary_stages is not None:
        stage_start = SPAN['BAND']['stage_start']
        lower, upper = stage_start(2) * sheets, stage_start(2 + ordinary_stages) * sheets
        clauses.extend([-(v + 1)] for v in range(len(graph)) if not lower <= v < upper)
        seeds = [v for v in seeds if lower <= v - 1 < upper]
        if first_ordinary_stage:
            clauses.append(list(range(lower + 1, stage_start(3) * sheets + 1)))
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


def known_union_coefficients(blocks, minimum, near_minimum, size_26=None, size_27=None, size_28=None):
    """Count unions through one degree above the supplied minimal losses."""
    budget = 26 + sum(part is not None for part in (size_26, size_27, size_28))
    losses = (*minimum, *near_minimum, *(size_26 or ()), *(size_27 or ()), *(size_28 or ()))
    events = {frozenset(pattern) for pattern in losses}
    by_label = defaultdict(list)
    for event in events:
        for v, s in event:
            by_label[v].append((event, s))
    unions = set(events)
    pending = list(events)
    while pending:
        union = pending.pop()
        if len(union) == budget:
            continue
        translations = {(event, s - t) for v, s in union for event, t in by_label[v]}
        for event, shift in translations:
            joined = union | {(v, s + shift) for v, s in event}
            if len(union) < len(joined) <= budget:
                normalized_union = frozenset(normalized(joined))
                if normalized_union not in unions:
                    unions.add(normalized_union)
                    pending.append(normalized_union)

    weights = {}
    coefficients = Counter()
    maximum_span = 13 if blocks == 4 and size_27 is not None else 11
    for union in sorted(unions, key=lambda sites: (len(sites), tuple(sorted(sites)))):
        last_sheet = max(s for _, s in union)
        if last_sheet > maximum_span:
            raise AssertionError(('Unexpected span for a small union', blocks, last_sheet))
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
    if size_26 is not None:
        expected[26] += len(size_26)
        expected[27] = -127 if blocks == 4 else -120
    if size_27 is not None:
        expected[27] += len(size_27)
        expected[28] = -417 if blocks == 4 else -399
        profile = Counter(weight for union, weight in weights.items() if len(union) == 28)
        expected_profile = {-2: 3, -1: 463, 0: 35, 1: 52} if blocks == 4 else {
            -2: 3, -1: 443, 0: 35, 1: 50,
        }
        if size_28 is not None:
            expected_profile[1] += len(size_28)
        if profile != expected_profile:
            raise AssertionError(('Unexpected order-28 weight distribution', blocks, profile))
    if size_28 is not None:
        expected[28] += len(size_28)
        expected[29] = -1585
        profile = Counter(weight for union, weight in weights.items() if len(union) == 29)
        if profile != {-2: 28, -1: 1812, 0: 124, 1: 273, 2: 5}:
            raise AssertionError(('Unexpected order-29 weight distribution', blocks, profile))
    if coefficients != expected:
        raise AssertionError(('Unexpected union coefficients', blocks, coefficients))
    return dict(sorted(coefficients.items()))


def check_size_26(blocks, *, size_27=False, size_28=False):
    size_27 = size_27 or size_28
    base = min(blocks, 5)
    minimum = minimum_seed_sets(base)
    near = enumerate_blockers(base, minimum)
    if Counter(max(s for _, s in p) for p in near) != EXPECTED_SPANS[base]:
        raise AssertionError(('Unexpected size-25 seed catalogue', base))
    patterns = enumerate_blockers(base, (*minimum, *sorted(near)), budget=26)
    if Counter(max(s for _, s in p) for p in patterns) != EXPECTED_SIZE_26_SPANS[base]:
        raise AssertionError(('Unexpected base size-26 seed catalogue', base))
    if base == 5:
        check_template_stages(patterns, {(0, 1, 2): 88, (3, 4): 9})
    templates_27 = None
    if size_27:
        templates_27 = enumerate_blockers(base, (*minimum, *sorted(near), *sorted(patterns)), budget=27)
        if base == 5:
            check_template_stages(templates_27, {(0, 1, 2): 251, (3, 4): 5, (0, 3, 4): 2})
    if blocks > base:
        minimum = minimum_seed_sets(blocks)
        near = verify_inherited_patterns(blocks, minimum, near)
        smaller = (*minimum, *sorted(near))
        known = verify_inherited_patterns(blocks, smaller, patterns, budget=26)
        patterns = enumerate_blockers(blocks, smaller, known, budget=26) if blocks <= DIRECT_LAST else known
    spans = Counter(max(s for _, s in p) for p in patterns)
    if spans != EXPECTED_SIZE_26_SPANS[blocks]:
        raise AssertionError(('Unexpected size-26 seed catalogue', blocks, spans))
    size = 26
    if size_27:
        size = 27
        all_26 = (*minimum, *sorted(near), *sorted(patterns))
        if blocks > base:
            inherited = verify_inherited_patterns(blocks, all_26, templates_27, budget=size)
            exact_27 = inherited
            if blocks <= DIRECT_SIZE_27_LAST:
                exact_27 = enumerate_blockers(blocks, all_26, inherited, budget=size)
        else:
            exact_27 = templates_27
        spans = Counter(max(s for _, s in p) for p in exact_27)
        if spans != EXPECTED_SIZE_27_SPANS[blocks]:
            raise AssertionError(('Unexpected size-27 seed catalogue', blocks, spans))
        exact_26 = patterns
        patterns = exact_27
        if size_28:
            size = 28
            patterns = enumerate_blockers(blocks, (*all_26, *sorted(exact_27)), budget=size)
            spans = Counter(max(s for _, s in p) for p in patterns)
            if spans != EXPECTED_SIZE_28_SPANS[blocks]:
                raise AssertionError(('Unexpected size-28 seed catalogue', blocks, spans))
        coefficients = known_union_coefficients(blocks, minimum, near, exact_26, exact_27,
                                                patterns if size_28 else None)
    else:
        coefficients = known_union_coefficients(blocks, minimum, near, patterns)
    print(json.dumps({'blocks': blocks, 'size': size, 'count': len(patterns),
                      'spans': dict(sorted(spans.items())), 'losses': sorted(patterns),
                      'known_union_coefficients': coefficients}),
          flush=True)


def check_ordinary_size_30(*, exhaustive=False):
    if enumerate_blockers(13, (), budget=29, ordinary_stages=8):
        raise AssertionError('A cost-29 fort fits in eight ordinary stages')
    catalogue = enumerate_blockers(8, (), budget=30, ordinary_stages=3)
    if len(catalogue) != 10:
        raise AssertionError(('Unexpected size-30 ordinary catalogue', len(catalogue)))
    stage_start = SPAN['BAND']['stage_start']
    sheets = 32
    graph, blue, *_ = COVER['signed_prism_cover'](21, sheets)
    original = stage_start(2)
    start, stop = stage_start(9), stage_start(12)
    spans = Counter()
    residual_sizes = Counter()
    restoration_rounds = Counter()
    for pattern in sorted(catalogue):
        if {(v - original) // 16 for v, _ in pattern} != {0, 1, 2}:
            raise AssertionError(('Ordinary loss misses a stage', pattern))
        lost = mask((start + v - original) * sheets + s + 7 for v, s in pattern)
        if lost & blue != lost or lost.bit_count() != 30:
            raise AssertionError(('Invalid ordinary seed coordinates', pattern))
        arrival = COVER['MODEL']['trace'](graph, blue & ~lost)[1]
        fort = mask(v for v, time in enumerate(arrival) if time is None)
        if fort & blue != lost or any(
                not start <= v // sheets < stop or v % sheets in (0, sheets - 1) for v in members(fort)):
            raise AssertionError(('Invalid ordinary closure', pattern))
        spans[max(s for _, s in pattern)] += 1
        residual_sizes[fort.bit_count()] += 1
        restoration_rounds.update(dict(SPAN['restoration_profile'](graph, blue, lost)))
    if exhaustive:
        check_ordinary_size_30_window(catalogue)
    print(json.dumps({
        'size': 30, 'ordinary_stages': 3, 'count': len(catalogue),
        'spans': dict(sorted(spans.items())), 'residual_sizes': dict(sorted(residual_sizes.items())),
        'restoration_rounds': dict(sorted(restoration_rounds.items())),
        'losses': [[(v - original, s) for v, s in pattern] for pattern in sorted(catalogue)],
    }), flush=True)


def check_ordinary_size_30_window(catalogue):
    band = SPAN['BAND']
    band['check_band'](34, stages=32, budget=30)
    print('A 32-stage ordinary band forces an empty pair at budget 30', flush=True)
    for width in range(10, 21):
        band['check_sheet_band'](width, width - 5, pin_ends=width > 10,
                                 blocks=36, subband_constraints=width >= 13)
    stage_start = band['stage_start']
    stop = stage_start(33)
    placements = {
        tuple((v + shift, sheet) for v, sheet in pattern)
        for pattern in catalogue
        for shift in range(0, stop - max(v for v, _ in pattern), 16)
    }
    if enumerate_blockers(36, (), placements, budget=30, ordinary_stages=31,
                          first_ordinary_stage=True) != placements:
        raise AssertionError('Unexpected cost-30 seed loss in the ordinary interior')
    print('The ten cost-30 losses exhaust the ordinary interior', flush=True)


def check_ordinary_threshold():
    band = SPAN['BAND']
    band['check_band'](33, stages=31, budget=29)
    print('A 31-stage ordinary band forces an empty pair at budget 29', flush=True)
    for width in range(10, 20):
        band['check_sheet_band'](width, width - 5, pin_ends=width > 10,
                                 blocks=35, subband_constraints=width >= 13)
    print('A width-19 sheet band requires at least 15 seeds at 35 blocks', flush=True)
    if enumerate_blockers(35, (), budget=29, ordinary_stages=30):
        raise AssertionError('A cost-29 fort fits in 30 ordinary stages')
    print('No finite fort of cost up to 29 is supported in the ordinary interior', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--blocks', choices=EXPECTED_SPANS, type=int, nargs='+',
                      default=tuple(EXPECTED_SPANS))
    mode.add_argument('--size-26', choices=EXPECTED_SIZE_26_SPANS, type=int, metavar='BLOCKS',
                      help='enumerate size-26 losses through 14 blocks and verify inherited patterns through 20')
    mode.add_argument('--size-27', choices=EXPECTED_SIZE_27_SPANS, type=int, metavar='BLOCKS',
                      help='enumerate size-27 losses through 13 blocks and verify inherited patterns through 20')
    mode.add_argument('--ordinary-size-30', action='store_true',
                      help='classify cost-30 forts confined to three ordinary stages by seed loss')
    mode.add_argument('--ordinary-size-30-exact', action='store_true',
                      help='verify the complete cost-30 ordinary interior catalogue')
    mode.add_argument('--size-28', choices=EXPECTED_SIZE_28_SPANS, type=int, metavar='BLOCKS',
                      help='enumerate size-28 losses at five blocks')
    mode.add_argument('--ordinary-threshold', action='store_true',
                      help='certify the absence of ordinary interior forts of cost up to 29')
    args = parser.parse_args()
    if args.ordinary_threshold:
        check_ordinary_threshold()
        return
    if args.ordinary_size_30 or args.ordinary_size_30_exact:
        check_ordinary_size_30(exhaustive=args.ordinary_size_30_exact)
        return
    if args.size_26 is not None:
        check_size_26(args.size_26)
        return
    if args.size_27 is not None:
        check_size_26(args.size_27, size_27=True)
        return
    if args.size_28 is not None:
        check_size_26(args.size_28, size_28=True)
        return
    templates = enumerate_blockers(5, minimum_seed_sets(5)) if any(k >= 5 for k in args.blocks) else ()
    if templates:
        check_template_stages(templates, {(0, 1, 2): 16, (3, 4): 4})
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
