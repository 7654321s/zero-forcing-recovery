"""Enumerate small inclusion-minimal seed losses in the integer prism lift."""

import argparse
from collections import Counter, defaultdict, deque
from itertools import combinations
import gzip
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
DIRECT_SIZE_28_LAST = 11
DIRECT_SIZE_29_LAST = 11
LOCALITY_REPRESENTATIVE = 21
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


EXPECTED_SIZE_28_SPANS = dict.fromkeys(
    range(5, LOCALITY_REPRESENTATIVE + 1), {7: 13, 8: 129, 9: 301, 10: 218, 11: 80})
EXPECTED_SIZE_29_SPANS = dict.fromkeys(
    range(5, LOCALITY_REPRESENTATIVE + 1), {7: 20, 8: 316, 9: 750, 10: 616, 11: 271, 12: 9})
EXPECTED_SIZE_30_SPANS = dict(zip(range(7, 13), (47, 679, 2001, 2136, 998, 114)))
EXPECTED_BOUNDARY_SPANS = dict(zip(range(7, 13), (47, 679, 2001, 2152, 1062, 114)))


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


def remaining_white(neighbors, intact_white, lost):
    """Compute the final white set by updating only neighbors of each force."""
    white = intact_white.copy()
    for vertex in members(lost):
        white[vertex] = 1
    counts = bytearray(sum(white[v] for v in row) for row in neighbors)
    sources = deque(u for u, count in enumerate(counts) if count == 1 and not white[u])
    while sources:
        source = sources.popleft()
        if counts[source] != 1:
            continue
        target = next(v for v in neighbors[source] if white[v])
        white[target] = 0
        if counts[target] == 1:
            sources.append(target)
        for neighbor in neighbors[target]:
            counts[neighbor] -= 1
            if counts[neighbor] == 1 and not white[neighbor]:
                sources.append(neighbor)
    return mask(v for v, remains_white in enumerate(white) if remains_white)


def verify_inherited_patterns(blocks, smaller, templates, *, budget=25, already_lifted=False):
    stage_start = SPAN['BAND']['stage_start']
    terminal = stage_start(3)
    shift = 0 if already_lifted else stage_start(blocks - 2) - terminal
    opening = stage_start(1)
    smaller = tuple(smaller)
    covers = {}
    patterns = set()
    for template in templates:
        cut = terminal
        if budget in (28, 29):
            stages = {0 if v < opening else (v - opening) // 16 + 1 for v, _ in template}
            if stages == {2, 3, 4}:
                cut = stage_start(2)
            elif stages == {0, 1, 2, 3}:
                cut = stage_start(5)
        pattern = tuple((v + shift if v >= cut else v, s) for v, s in template)
        sheets = max(max(s for _, s in pattern) + 10, {27: 31, 28: 33, 29: 36}.get(budget, 0))
        if sheets not in covers:
            graph, blue, *_ = COVER['signed_prism_cover'](blocks, sheets)
            smaller_translates = defaultdict(set)
            for smaller_pattern in smaller:
                for delta in range(sheets):
                    translated = mask(v * sheets + (s + delta) % sheets for v, s in smaller_pattern)
                    smaller_translates[translated & -translated].add(translated)
            neighbors = tuple(tuple(members(row)) for row in graph)
            white = bytearray(not (blue >> v) & 1 for v in range(len(graph)))
            covers[sheets] = (graph, blue, smaller_translates, neighbors, white)
        graph, blue, smaller_translates, neighbors, white = covers[sheets]
        lost = mask(v * sheets + s + 4 for v, s in pattern)
        if lost & blue != lost or lost.bit_count() != budget:
            raise AssertionError(('Unexpected inherited seeds', blocks, pattern))
        fort = remaining_white(neighbors, white, lost)
        if COVER['fort_cost'](graph, blue, fort) != budget or any(
                v % sheets in (0, sheets - 1) for v in members(fort)):
            raise AssertionError(('Inherited loss has no finite fort', blocks, pattern))
        if any(projection & lost == projection for seed in members(lost)
               for projection in smaller_translates.get(1 << seed, ())):
            raise AssertionError(('Inherited loss contains a smaller pattern', blocks, pattern))
        patterns.add(pattern)
    return patterns


def check_template_stages(templates, expected):
    opening = SPAN['BAND']['stage_start'](1)
    stages = Counter(tuple(sorted({0 if v < opening else (v - opening) // 16 + 1
                                   for v, _ in template})) for template in templates)
    if stages != expected:
        raise AssertionError(('Unexpected occupied stages', stages))


def enumerate_blockers(blocks, smaller, known=(), *, budget=25, ordinary_stages=None,
                       first_ordinary_stage=False, occupied_stage_pairs=False, strip_sheets=None,
                       require_minimal_fort=False, restrict=None):
    sheets = budget + 10 if strip_sheets is None else strip_sheets
    graph, blue, *_ = COVER['signed_prism_cover'](blocks, sheets)
    clauses, seeds, top = STRIP['strip_formula'](
        graph, blue, budget, sheets=sheets, quotient_bounds=False,
        require_minimal=require_minimal_fort)
    if occupied_stage_pairs:
        stage_start = SPAN['BAND']['stage_start']
        for stage in range(1, blocks - 1):
            lower = stage_start(stage) * sheets
            upper = stage_start(stage + 2) * sheets
            clauses.append(list(range(lower + 1, upper + 1)))
    if ordinary_stages is not None:
        stage_start = SPAN['BAND']['stage_start']
        lower, upper = stage_start(2) * sheets, stage_start(2 + ordinary_stages) * sheets
        clauses.extend([-(v + 1)] for v in range(len(graph)) if not lower <= v < upper)
        seeds = [v for v in seeds if lower <= v - 1 < upper]
        if first_ordinary_stage:
            clauses.append(list(range(lower + 1, stage_start(3) * sheets + 1)))
    if restrict is not None:
        seeds = restrict(clauses, seeds, len(graph), sheets)
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


def signed_union_weights(losses, budget):
    label_count = 1 + max(v for pattern in losses for v, _ in pattern)
    # At these budgets any two contributing losses intersect, so two spans bound the union span.
    margin = 2 * max(s for pattern in losses for _, s in normalized(pattern))
    margin_bits = margin * label_count
    unions = defaultdict(set)
    for row in losses:
        event = mask((s - 1) * label_count + v for v, s in normalized(row))
        unions[event.bit_count()].add(event)

    def normalize_bits(pattern):
        origin = ((pattern & -pattern).bit_length() - 1) // label_count * label_count
        return pattern >> origin

    def record(index, pattern):
        for site in members(pattern):
            sheet, label = divmod(site, label_count)
            index[label].append((pattern, sheet))

    def translated_candidates(sites, index, pivot_count):
        ordered = sorted(sites, key=lambda site: len(index[site[1]]))
        return {(pattern, margin + sheet - origin)
                for sheet, label in ordered[:pivot_count] for pattern, origin in index[label]}

    by_size = defaultdict(lambda: defaultdict(list))
    for size, events in unions.items():
        for event in events:
            record(by_size[size], event)
    for degree in range(min(unions), budget):
        for union in unions[degree]:
            sites = [divmod(site, label_count) for site in members(union)]
            padded = union << margin_bits
            for size, index in by_size.items():
                # A fitting union leaves at most budget - size sites outside this event.
                for event, offset in translated_candidates(sites, index, budget - size + 1):
                    joined = padded | (event << (offset * label_count))
                    joined_size = joined.bit_count()
                    if degree < joined_size <= budget:
                        unions[joined_size].add(normalize_bits(joined))

    by_size.clear()
    weights = {}
    profiles = defaultdict(Counter)
    for degree in sorted(unions):
        for union in unions[degree]:
            positions = list(members(union))
            sites = [divmod(site, label_count) for site in positions]
            bits = [1 << site for site in positions]
            padded = union << margin_bits
            weight = 1
            for size, index in by_size.items():
                omitted = degree - size
                if omitted <= 2:
                    for removed in combinations(bits, omitted):
                        smaller = normalize_bits(union ^ sum(removed))
                        weight -= weights.get(smaller, 0)
                    continue
                for smaller, offset in translated_candidates(sites, index, omitted + 1):
                    shifted = smaller << (offset * label_count)
                    if shifted & padded == shifted:
                        weight -= weights[smaller]
            weights[union] = weight
            profiles[degree][weight] += 1
        for union in unions[degree]:
            if weights[union]:
                record(by_size[degree], union)
    largest_span = max((row.bit_length() - 1) // label_count + 1 for row in weights)
    return profiles, largest_span


def known_union_coefficients(blocks, minimum, near_minimum, size_26=None, size_27=None, size_28=None,
                             size_29=None):
    """Count unions through one degree above the supplied minimal losses."""
    catalogue = (size_26, size_27, size_28, size_29)
    budget = 26 + sum(part is not None for part in catalogue)
    losses = (*minimum, *near_minimum, *(pattern for part in catalogue if part for pattern in part))
    profiles, span = signed_union_weights(losses, budget)
    maximum_span = 12 if size_29 is not None else 11
    if blocks == 4 and size_27 is not None:
        maximum_span = 13
    if span > maximum_span:
        raise AssertionError(('Unexpected span for a small union', blocks, span))
    coefficients = {degree: sum(weight * count for weight, count in profile.items())
                    for degree, profile in profiles.items()}

    expected = {24: 5, 25: len(near_minimum) - 2, 26: -16 if blocks == 4 else -15}
    if size_26 is not None:
        expected[26] += len(size_26)
        expected[27] = -127 if blocks == 4 else -120
    if size_27 is not None:
        expected[27] += len(size_27)
        expected[28] = -417 if blocks == 4 else -399
        profile = profiles[28]
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
        profile = profiles[29]
        if profile != {-2: 28, -1: 1812, 0: 124, 1: 273 + len(size_29 or ()), 2: 5}:
            raise AssertionError(('Unexpected order-29 weight distribution', blocks, profile))
    if size_29 is not None:
        expected[29] += len(size_29)
        expected[30] = -3861
        if profiles[30] != {-2: 73, -1: 5536, 0: 723, 1: 1743, 2: 39}:
            raise AssertionError(('Unexpected order-30 weight distribution', blocks, profiles[30]))
    if coefficients != expected:
        raise AssertionError(('Unexpected union coefficients', blocks, coefficients))
    return dict(sorted(coefficients.items()))


def check_five_block_catalogue(*, exhaustive=False):
    """Replay the finite witnesses, with optional SAT exhaustion at each size."""
    with gzip.open(HERE / 'five-block-loss-catalogue.json.gz', 'rt', encoding='utf-8') as source:
        data = json.load(source)
    if (data['schema_version'], data['blocks'], data['first_sheet']) != (1, 5, 1):
        raise AssertionError('Unexpected loss catalogue format')
    expected = (
        {7: 1, 8: 2, 9: 2}, EXPECTED_SPANS[5], EXPECTED_SIZE_26_SPANS[5],
        EXPECTED_SIZE_27_SPANS[5], EXPECTED_SIZE_28_SPANS[5], EXPECTED_SIZE_29_SPANS[5],
        EXPECTED_SIZE_30_SPANS,
    )
    if set(data['losses_by_size']) != {str(size) for size in range(24, 31)}:
        raise AssertionError('Unexpected loss catalogue sizes')
    smaller, verified = (), []
    for cost, spans in enumerate(expected, start=24):
        patterns = tuple(tuple(map(tuple, row)) for row in data['losses_by_size'][str(cost)])
        if tuple(sorted(set(patterns))) != patterns or any(
                len(row) != cost or normalized(row) != row or len(set(row)) != cost
                for row in patterns):
            raise AssertionError(('Unnormalized catalogue entry', cost))
        if Counter(max(s for _, s in row) for row in patterns) != spans:
            raise AssertionError(('Unexpected catalogue spans', cost))
        replay = verify_inherited_patterns(5, smaller, patterns, budget=cost)
        if len(replay) != len(patterns):
            raise AssertionError(('Catalogue changed during replay', cost))
        if cost == 24 and replay != set(minimum_seed_sets(5)):
            raise AssertionError('Unexpected minimum catalogue')
        if exhaustive and enumerate_blockers(5, smaller, replay, budget=cost) != replay:
            raise AssertionError(('Unlisted minimal blocking loss', cost))
        smaller += patterns
        verified.append(patterns)
    coefficients = known_union_coefficients(5, *verified[:-1])
    coefficients[30] += len(verified[-1])
    print(json.dumps({
        'blocks': 5, 'exhaustive': exhaustive,
        'counts': {cost: len(group) for cost, group in enumerate(verified, start=24)},
        'blocking_coefficients_per_sheet': coefficients,
        'size_30_joint_spans': check_boundary_joint_spans(5, verified[-1]),
    }), flush=True)


def lower_order_catalogue(blocks, catalogues):
    smaller = tuple(minimum_seed_sets(blocks))
    for budget, catalogue in enumerate(catalogues, start=25):
        if blocks > 5:
            catalogue = verify_inherited_patterns(blocks, smaller, catalogue, budget=budget)
        smaller += tuple(sorted(catalogue))
    if len(smaller) != 3103:
        raise AssertionError(('Incomplete lower-order catalogue', len(smaller)))
    return smaller


def check_five_block_size_31():
    with gzip.open(HERE / 'five-block-loss-catalogue.json.gz', 'rt', encoding='utf-8') as source:
        base = json.load(source)['losses_by_size']
    smaller = tuple(tuple(map(tuple, row)) for size in range(24, 31) for row in base[str(size)])
    if len(smaller) != 9078:
        raise AssertionError('Incomplete five-block lower-order catalogue')
    print('Five blocks: enumerating size-31 losses in a 26-sheet guarded interior', flush=True)
    patterns = enumerate_blockers(5, smaller, budget=31, strip_sheets=28,
                                  require_minimal_fort=True)
    spans = Counter(max(sheet for _, sheet in row) for row in patterns)
    print(json.dumps({'blocks': 5, 'size': 31, 'count': len(patterns),
                      'spans': dict(sorted(spans.items())),
                      'blocking_coefficient_per_sheet': len(patterns) - 13174,
                      'losses': sorted(patterns)}), flush=True)


def catalogues_through_size_30(blocks):
    with gzip.open(HERE / 'five-block-loss-catalogue.json.gz', 'rt', encoding='utf-8') as source:
        base = json.load(source)['losses_by_size']
    catalogues = [tuple(tuple(map(tuple, row)) for row in base[str(size)])
                  for size in range(25, 30)]
    smaller = lower_order_catalogue(blocks, catalogues)
    if blocks == 5:
        size_30 = tuple(tuple(map(tuple, row)) for row in base['30'])
    else:
        filename = ('six-block-size-30-catalogue.json.gz' if blocks == 6
                    else 'thirteen-block-size-30-catalogue.json.gz')
        with gzip.open(HERE / filename, 'rt', encoding='utf-8') as source:
            archive = json.load(source)
        size_30 = tuple(tuple(map(tuple, row)) for row in archive['losses'])
        if blocks not in (6, 13):
            size_30 = relocate_boundary_patterns(size_30, 13, blocks)
    return smaller, size_30


def check_degree_31_overlap(blocks):
    smaller, size_30 = catalogues_through_size_30(blocks)
    check_boundary_joint_spans(blocks, size_30)
    profile, span = signed_union_weights((*smaller, *size_30), 31)
    expected = {-2: 344, -1: 19417 + 8 * blocks, 0: 2882, 1: 6502, 2: 233, 3: 1}
    if span != 12 or profile[31] != expected:
        raise AssertionError(('Unexpected degree-31 union weights', blocks, span, profile[31]))
    correction = sum(weight * count for weight, count in profile[31].items())
    print(json.dumps({'blocks': blocks, 'degree': 31, 'maximum_span': span,
                      'weights': dict(sorted(profile[31].items())),
                      'overlap_per_sheet': correction}), flush=True)


def check_size_30_boundary(catalogues, *, blocks=13):
    smaller = lower_order_catalogue(blocks, catalogues)
    patterns = enumerate_blockers(blocks, smaller, budget=30)
    result = {
        'blocks': blocks, 'size': 30, 'count': len(patterns),
        'losses': sorted(patterns),
    }
    if blocks == 5:
        spans = Counter(max(s for _, s in pattern) for pattern in patterns)
        if spans != EXPECTED_SIZE_30_SPANS:
            raise AssertionError(('Unexpected five-block size-30 seed catalogue', spans))
        result['spans'] = dict(sorted(spans.items()))
        result['blocking_coefficient_per_sheet'] = len(patterns) - 3861
    else:
        if blocks == 13 and Counter(max(s for _, s in row) for row in patterns) != EXPECTED_BOUNDARY_SPANS:
            raise AssertionError('Unexpected representative size-30 seed catalogue')
        result['boundary_coefficient'] = len(patterns) - 10 * blocks
    print(json.dumps(result), flush=True)


def boundary_stage_arc(pattern, blocks):
    opening = SPAN['BAND']['stage_start'](1)
    stages = sorted({0 if v < opening else 1 + (v - opening) // 16 for v, _ in pattern})
    next_stages = stages[1:] + [stages[0] + blocks]
    gap, first = max((b - a - 1, b % blocks) for a, b in zip(stages, next_stages))
    return first, blocks - gap, len(stages)


def boundary_window(first, span, blocks):
    # The opening and terminal stages have distinct labels in the local window.
    start = (first - 2) % blocks
    offsets = ((stage - start) % blocks for stage in (0, blocks - 1))
    return tuple(offset if offset < span + 3 else None for offset in offsets)


def relocate_boundary_patterns(patterns, source_blocks, target_blocks):
    stage_start = SPAN['BAND']['stage_start']
    opening = stage_start(1)
    for span in range(1, 5):
        source_windows = {boundary_window(first, span, source_blocks)
                          for first in range(source_blocks)}
        target_windows = {boundary_window(first, span, target_blocks)
                          for first in range(target_blocks)}
        missing = target_windows - source_windows
        # At seven blocks this window can only occur in the occupied-pair case.
        covered_by_search = {(0, 6)} if target_blocks == 7 and span == 4 else set()
        if missing != covered_by_search:
            raise AssertionError(('Unexpected unmatched source windows', span, missing))
    relocated = set()
    for row in patterns:
        first, span, _ = boundary_stage_arc(row, source_blocks)
        if span > 4:
            raise AssertionError(('Unexpected boundary stage span', span))
        window = boundary_window(first, span, source_blocks)
        entries = []
        for vertex, sheet in row:
            stage = 0 if vertex < opening else 1 + (vertex - opening) // 16
            offset = vertex - (stage_start(stage) if stage else 0)
            entries.append(((stage - first) % source_blocks, offset, sheet))
        for new_first in range(target_blocks):
            if boundary_window(new_first, span, target_blocks) != window:
                continue
            placed = []
            for delta, offset, sheet in entries:
                stage = (new_first + delta) % target_blocks
                placed.append(((stage_start(stage) if stage else 0) + offset, sheet))
            relocated.add(tuple(sorted(placed)))
    return tuple(sorted(relocated))


def check_boundary_joint_spans(blocks, patterns):
    spans = Counter((boundary_stage_arc(row, blocks)[1], max(s for _, s in row))
                    for row in patterns)
    expected = {2: {9: 19, 10: 40, 11: 5},
                3: {7: 47, 8: 679, 9: 1982, 10: 2 * blocks + 2085,
                    11: 8 * blocks + 928, 12: 110},
                4: {10: 1, 11: 25, 12: 4}}
    if spans != {(a, b): count for a, row in expected.items() for b, count in row.items()}:
        raise AssertionError(('Unexpected joint stage and sheet spans', blocks, spans))
    return expected


def check_boundary_catalogue(*, blocks=13, exhaustive=False):
    with gzip.open(HERE / 'five-block-loss-catalogue.json.gz', 'rt', encoding='utf-8') as source:
        base = json.load(source)['losses_by_size']
    base = [tuple(tuple(map(tuple, row)) for row in base[str(size)]) for size in range(25, 30)]
    archive_blocks = 6 if blocks == 6 else 13
    archive_prefix = 'six' if archive_blocks == 6 else 'thirteen'
    archive_path = HERE / f'{archive_prefix}-block-size-30-catalogue.json.gz'
    with gzip.open(archive_path, 'rt', encoding='utf-8') as source:
        archive = json.load(source)
    if (archive['schema_version'], archive['blocks'], archive['size'], archive['first_sheet']) != (
            1, archive_blocks, 30, 1):
        raise AssertionError('Unexpected boundary catalogue format')
    patterns = tuple(tuple(map(tuple, row)) for row in archive['losses'])
    if tuple(sorted(set(patterns))) != patterns or any(
            len(set(row)) != 30 or len(row) != 30 or normalized(row) != row
            for row in patterns):
        raise AssertionError('Unnormalized boundary catalogue entry')
    if archive_blocks == 13:
        spans = Counter(max(s for _, s in row) for row in patterns)
        if spans != EXPECTED_BOUNDARY_SPANS:
            raise AssertionError(('Unexpected boundary seed spans', spans))
    smaller = lower_order_catalogue(blocks, base)
    relocated = blocks != archive_blocks
    if relocated:
        for row in smaller:
            _, span, occupied = boundary_stage_arc(row, blocks)
            if span != occupied:
                raise AssertionError('A smaller pattern has a gap in its stage support')
        patterns = relocate_boundary_patterns(patterns, archive_blocks, blocks)
    spans = Counter(max(s for _, s in row) for row in patterns)
    expected_joint = check_boundary_joint_spans(blocks, patterns)
    verified = verify_inherited_patterns(blocks, smaller, patterns, budget=30, already_lifted=True)
    if verified != set(patterns):
        raise AssertionError('Boundary catalogue changed during replay')
    if exhaustive:
        print(f'{blocks} blocks: verified {len(verified)} witnesses; checking for additional losses',
              flush=True)
        if enumerate_blockers(blocks, smaller, verified, budget=30,
                              occupied_stage_pairs=relocated) != verified:
            raise AssertionError('Unlisted boundary blocking loss')
    print(json.dumps({'blocks': blocks, 'count': len(verified), 'spans': dict(sorted(spans.items())),
                      'joint_spans': expected_joint,
                      'boundary_coefficient': len(verified) - 10 * blocks,
                      'exhaustive': exhaustive}), flush=True)


def check_size_26(blocks, *, size_27=False, size_28=False, size_29=False, size_30_representative=None):
    size_29 = size_29 or size_30_representative is not None
    size_28 = size_28 or size_29
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
    templates_28 = None
    templates_29 = None
    if size_28:
        lower = (*minimum, *sorted(near), *sorted(patterns), *sorted(templates_27))
        templates_28 = enumerate_blockers(base, lower, budget=28)
        check_template_stages(templates_28, {
            (0, 1, 2): 715, (3, 4): 12, (0, 3, 4): 6, (2, 3, 4): 5, (0, 1, 2, 3): 3,
        })
        if size_29:
            templates_29 = enumerate_blockers(base, (*lower, *sorted(templates_28)), budget=29)
            check_template_stages(templates_29, {
                (0, 1, 2): 1870, (3, 4): 20, (0, 3, 4): 52, (2, 3, 4): 28, (0, 1, 2, 3): 12,
            })
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
            patterns = templates_28
            if blocks > base:
                smaller = (*all_26, *sorted(exact_27))
                inherited = verify_inherited_patterns(blocks, smaller, templates_28, budget=size)
                patterns = inherited
                if blocks <= DIRECT_SIZE_28_LAST:
                    patterns = enumerate_blockers(blocks, smaller, inherited, budget=size,
                                                  occupied_stage_pairs=blocks >= 8)
            spans = Counter(max(s for _, s in p) for p in patterns)
            if spans != EXPECTED_SIZE_28_SPANS[blocks]:
                raise AssertionError(('Unexpected size-28 seed catalogue', blocks, spans))
        exact_28 = patterns if size_28 else None
        if size_29:
            size = 29
            patterns = templates_29
            if blocks > base:
                smaller = (*all_26, *sorted(exact_27), *sorted(exact_28))
                inherited = verify_inherited_patterns(blocks, smaller, templates_29, budget=size)
                patterns = inherited
                if blocks <= DIRECT_SIZE_29_LAST:
                    patterns = enumerate_blockers(blocks, smaller, inherited, budget=size,
                                                  occupied_stage_pairs=True)
            spans = Counter(max(s for _, s in p) for p in patterns)
            if spans != EXPECTED_SIZE_29_SPANS[blocks]:
                raise AssertionError(('Unexpected size-29 seed catalogue', blocks, spans))
            if size_30_representative is not None:
                check_size_30_boundary((near, exact_26, exact_27, exact_28, patterns),
                                       blocks=size_30_representative)
                return
        coefficients = known_union_coefficients(blocks, minimum, near, exact_26, exact_27, exact_28,
                                                patterns if size_29 else None)
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
    least_stage_seeds = 30
    for pattern in sorted(catalogue):
        stage_counts = Counter((v - original) // 16 for v, _ in pattern)
        if stage_counts.keys() != {0, 1, 2}:
            raise AssertionError(('Ordinary loss misses a stage', pattern))
        least_stage_seeds = min(least_stage_seeds, min(stage_counts.values()))
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
    if least_stage_seeds != 6:
        raise AssertionError(('Unexpected minimum stage seed count', least_stage_seeds))
    overlap_profile, union_span = signed_union_weights(catalogue, 31)
    if overlap_profile[31] != {-1: 8} or union_span != 11:
        raise AssertionError(('Unexpected ordinary degree-31 overlaps', overlap_profile, union_span))
    if exhaustive:
        check_ordinary_size_30_window(catalogue)
    print(json.dumps({
        'size': 30, 'ordinary_stages': 3, 'count': len(catalogue),
        'spans': dict(sorted(spans.items())), 'residual_sizes': dict(sorted(residual_sizes.items())),
        'restoration_rounds': dict(sorted(restoration_rounds.items())),
        'degree_31_overlap_weights': dict(overlap_profile[31]),
        'degree_31_union_span': union_span,
        'losses': [[(v - original, s) for v, s in pattern] for pattern in sorted(catalogue)],
    }), flush=True)


def check_ordinary_size_30_window(catalogue):
    band = SPAN['BAND']
    band['check_band'](34, stages=32, budget=30)
    print('A 32-stage ordinary band forces an empty pair at budget 30', flush=True)
    check_ordinary_sheet_bands()
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


def check_ordinary_sheet_bands(*, through=20, blocks=36):
    band = SPAN['BAND']
    for width in range(10, through + 1):
        band['check_sheet_band'](width, width - 5, pin_ends=width > 10,
                                 blocks=blocks, subband_constraints=width >= 13)


def ordinary_size_31_restoration(templates):
    sheets, anchor = 32, 9
    graph, seeds, *_ = COVER['signed_prism_cover'](21, sheets)
    stage_start = SPAN['BAND']['stage_start']
    neighbors = tuple(tuple(members(row)) for row in graph)
    trace = COVER['MODEL']['trace']
    intact = trace(graph, seeds)[1]
    if None in intact or max(intact) != 2:
        raise AssertionError('Unexpected intact closure in the restoration representative')
    intact_white = [{v for v, t in enumerate(intact) if t > r} for r in range(3)]

    def recover(lost):
        region = set(lost)
        added_white = set(lost)
        # At round r any change from the intact run is within distance 2r of a loss.
        for round_number in (1, 2):
            for _ in range(2):
                region.update(u for v in tuple(region) for u in neighbors[v])
            white = intact_white[round_number - 1] | added_white
            added_white = {
                v for v in (region & white) - intact_white[round_number]
                if not any(u not in white and all(w == v or w not in white for w in neighbors[u])
                           for u in neighbors[v])
            }
        white = added_white
        round_number = 2
        while white:
            sources = {u for v in white for u in neighbors[v] if u not in white}
            forced = set()
            for source in sources:
                targets = [v for v in neighbors[source] if v in white]
                if len(targets) == 1:
                    forced.add(targets[0])
            if not forced:
                return None, white
            white.difference_update(forced)
            round_number += 1
        return round_number, white

    residual, rounds, worst = Counter(), Counter(), Counter()
    for index, template in enumerate(templates):
        lost = {(v + stage_start(anchor)) * sheets + sheet + 7 for v, sheet in template}
        completion, fort = recover(lost)
        if completion is not None or {u for u in fort if (seeds >> u) & 1} != lost:
            raise AssertionError(('Unexpected surviving fort', template))
        if any(not stage_start(anchor - 1) <= v // sheets < stage_start(anchor + 3)
               or v % sheets in (0, sheets - 1) for v in fort):
            raise AssertionError(('Unguarded surviving fort', template))
        profile = Counter()
        for restored in sorted(lost):
            time, _ = recover(lost - {restored})
            if time is None:
                raise AssertionError(('A single restoration still blocks', template, restored))
            profile[time] += 1
        if index in (0, 11, 48, 96):
            direct = trace(graph, seeds & ~mask(lost))[1]
            if fort != {v for v, t in enumerate(direct) if t is None} or profile != dict(
                    SPAN['restoration_profile'](graph, seeds, mask(lost))):
                raise AssertionError(('Local and full forcing traces differ', template))
        residual[len(fort)] += 1
        rounds.update(profile)
        worst[max(profile)] += 1
    if residual != {64: 1, 66: 2, 67: 5, 68: 3, 69: 5, 70: 4, 71: 14, 72: 13,
                    73: 17, 74: 11, 75: 13, 76: 6, 77: 2, 78: 1}:
        raise AssertionError(('Unexpected ordinary fort sizes at cost 31', residual))
    if rounds != {7: 7, 8: 58, 9: 230, 10: 432, 11: 558, 12: 596, 13: 457, 14: 347,
                  15: 206, 16: 79, 17: 32, 18: 4, 20: 1}:
        raise AssertionError(('Unexpected ordinary restoration times at cost 31', rounds))
    if worst != {14: 17, 15: 28, 16: 26, 17: 22, 18: 3, 20: 1}:
        raise AssertionError(('Unexpected worst restoration times by template', worst))
    return {'residual_sizes': dict(sorted(residual.items())),
            'restoration_rounds': dict(sorted(rounds.items())),
            'worst_restoration_rounds': dict(sorted(worst.items()))}


def ordinary_degree_32_overlap(older, size_31):
    templates = (*older, *size_31)
    for row in templates:
        stage_counts = Counter(v // 16 for v, _ in row)
        if stage_counts.keys() != {0, 1, 2} or min(stage_counts.values()) < 6:
            raise AssertionError(('Unexpected ordinary template stage counts', row))
    weights, span = signed_union_weights(templates, 32)
    expected = {30: {1: 10}, 31: {-1: 8, 1: 97}, 32: {-1: 206, 0: 3, 1: 1}}
    if weights != expected or span != 11:
        raise AssertionError(('Unexpected ordinary degree-32 overlap weights', weights, span))
    return {'degree_32_overlap_weights': dict(sorted(weights[32].items())),
            'degree_32_overlap_per_start_and_sheet': sum(w * n for w, n in weights[32].items()),
            'degree_32_union_span': span}


def ordinary_placements(templates, width):
    stage_start = SPAN['BAND']['stage_start']
    return {tuple((v + stage_start(start), sheet) for v, sheet in row)
            for start in range(2, width) for row in templates}


def ordinary_size_31_catalogue():
    stage_start = SPAN['BAND']['stage_start']
    with gzip.open(HERE / 'thirteen-block-size-30-catalogue.json.gz', 'rt', encoding='utf-8') as source:
        archive = json.load(source)
    ordinary = [
        tuple((v - stage_start(5), sheet) for v, sheet in row)
        for row in archive['losses'] if boundary_stage_arc(row, 13)[:2] == (5, 3)
    ]
    if len(ordinary) != 10:
        raise AssertionError(('Unexpected number of ordinary size-30 types', len(ordinary)))

    three_stages = None
    for width in (3, 4):
        patterns = enumerate_blockers(width + 5, ordinary_placements(ordinary, width), budget=31,
                                      ordinary_stages=width,
                                      first_ordinary_stage=True)
        if width == 3:
            three_stages = patterns
        elif patterns != three_stages:
            raise AssertionError('The three-stage and four-stage size-31 catalogues differ')

    check_template_stages(three_stages, {(2, 3, 4): 97})
    spans = Counter(max(sheet for _, sheet in row) for row in three_stages)
    if spans != {10: 4, 11: 93}:
        raise AssertionError(('Unexpected ordinary size-31 sheet spans', spans))
    templates = [tuple((v - stage_start(2), sheet) for v, sheet in row)
                 for row in sorted(three_stages)]
    return ordinary, templates, spans


def check_ordinary_size_31(*, exhaustive=False, restoration=False, overlap_32=False):
    ordinary, templates, spans = ordinary_size_31_catalogue()
    if exhaustive:
        for blocks in (34, 35):
            SPAN['BAND']['check_band'](blocks, stages=33, budget=31)
            print(f'{blocks} blocks: a 33-stage band forces an empty pair at budget 31',
                  flush=True)
        check_ordinary_sheet_bands(through=22)
        known = ordinary_placements(templates, 32)
        if enumerate_blockers(36, ordinary_placements(ordinary, 32), known, budget=31,
                              ordinary_stages=32, first_ordinary_stage=True) != known:
            raise AssertionError('An additional size-31 loss survives in the ordinary interior')
    result = {
        'size': 31, 'ordinary_stage_window': 32 if exhaustive else 4,
        'exhaustive': exhaustive, 'count': len(templates),
        'spans': dict(sorted(spans.items())), 'losses': templates,
    }
    if restoration:
        result.update(ordinary_size_31_restoration(templates))
    if overlap_32:
        result.update(ordinary_degree_32_overlap(ordinary, templates))
    print(json.dumps(result), flush=True)


def check_ordinary_size_32(*, exhaustive=False):
    ordinary, size_31, _ = ordinary_size_31_catalogue()
    smaller = (*ordinary, *size_31)
    patterns = enumerate_blockers(8, ordinary_placements(smaller, 3), budget=32, ordinary_stages=3,
                                  first_ordinary_stage=True, strip_sheets=40,
                                  require_minimal_fort=True)
    check_template_stages(patterns, {(2, 3, 4): 276})
    spans = Counter(max(sheet for _, sheet in row) for row in patterns)
    if spans != {10: 8, 11: 268}:
        raise AssertionError(('Unexpected ordinary size-32 sheet spans', spans))
    stage_start = SPAN['BAND']['stage_start']
    templates = [tuple((v - stage_start(2), sheet) for v, sheet in row)
                 for row in sorted(patterns)]
    if exhaustive:
        SPAN['BAND']['check_band'](36, stages=34, budget=32)
        check_ordinary_sheet_bands(through=21, blocks=37)
        print('Certified a 33-stage and 38-sheet ordinary interior at cost 32', flush=True)
    for width in (33,) if exhaustive else (4, 5):
        blocks = 37 if exhaustive else width + 5
        known = ordinary_placements(templates, width)
        wider = enumerate_blockers(blocks, ordinary_placements(smaller, width), known,
                                    budget=32, ordinary_stages=width, first_ordinary_stage=True,
                                    strip_sheets=40, require_minimal_fort=True)
        if wider != known:
            raise AssertionError(('A new size-32 type survives', width))
    print(json.dumps({'size': 32, 'ordinary_stage_window': 33 if exhaustive else 5,
                      'exhaustive': exhaustive, 'count': len(templates),
                      'spans': dict(sorted(spans.items())), 'losses': templates}), flush=True)


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
    mode.add_argument('--ordinary-size-31', action='store_true',
                      help='verify size-31 losses within four ordinary stages')
    mode.add_argument('--ordinary-size-31-exact', action='store_true',
                      help='verify the complete ordinary size-31 loss catalogue')
    mode.add_argument('--ordinary-size-31-restoration', action='store_true',
                      help='check the single-seed restoration times of ordinary size-31 losses')
    mode.add_argument('--ordinary-size-32', action='store_true',
                      help='verify size-32 losses within five ordinary stages')
    mode.add_argument('--ordinary-size-32-exact', action='store_true',
                      help='verify the complete ordinary size-32 loss catalogue')
    mode.add_argument('--ordinary-degree-32-overlap', action='store_true',
                      help='verify degree-32 ordinary overlaps of smaller losses')
    mode.add_argument('--degree-31-overlap', type=int, choices=range(5, 15), metavar='BLOCKS',
                      help='verify the degree-31 overlap correction from the smaller losses')
    mode.add_argument('--size-28', choices=EXPECTED_SIZE_28_SPANS, type=int, metavar='BLOCKS',
                      help='verify size-28 losses from five blocks through the locality representative')
    mode.add_argument('--size-29', choices=EXPECTED_SIZE_29_SPANS, type=int, metavar='BLOCKS',
                      help='verify size-29 losses from five blocks through the locality representative')
    mode.add_argument('--size-30-boundary', action='store_true',
                      help='enumerate the 13-block representative for the size-30 boundary term')
    mode.add_argument('--boundary-catalogue',
                      choices=('witnesses', 'exhaustive', 'ten-blocks', 'nine-blocks', 'eight-blocks',
                               'seven-blocks', 'six-blocks', 'six-blocks-witnesses'),
                      help='replay or exhaust the size-30 boundary catalogues')
    mode.add_argument('--size-31-five-blocks', action='store_true',
                      help='enumerate five-block size-31 losses in the compact guarded strip')
    mode.add_argument('--size-30-five-blocks', action='store_true',
                      help='verify the 5975 size-30 seed loss types at five blocks')
    mode.add_argument('--five-block-catalogue', choices=('witnesses', 'exhaustive'),
                      help='verify the published catalogue and optionally replay SAT exhaustion')
    mode.add_argument('--ordinary-threshold', action='store_true',
                      help='certify the absence of ordinary interior forts of cost up to 29')
    args = parser.parse_args()
    if args.ordinary_threshold:
        check_ordinary_threshold()
        return
    if args.ordinary_size_32 or args.ordinary_size_32_exact:
        check_ordinary_size_32(exhaustive=args.ordinary_size_32_exact)
        return
    if args.degree_31_overlap is not None:
        check_degree_31_overlap(args.degree_31_overlap)
        return
    if args.size_31_five_blocks:
        check_five_block_size_31()
        return
    if (args.ordinary_size_31 or args.ordinary_size_31_exact or args.ordinary_size_31_restoration
            or args.ordinary_degree_32_overlap):
        check_ordinary_size_31(exhaustive=args.ordinary_size_31_exact,
                               restoration=args.ordinary_size_31_restoration,
                               overlap_32=args.ordinary_degree_32_overlap)
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
    if args.size_29 is not None:
        check_size_26(args.size_29, size_29=True)
        return
    if args.size_30_boundary or args.size_30_five_blocks:
        check_size_26(5, size_30_representative=13 if args.size_30_boundary else 5)
        return
    if args.five_block_catalogue:
        check_five_block_catalogue(exhaustive=args.five_block_catalogue == 'exhaustive')
        return
    if args.boundary_catalogue:
        blocks = {'six-blocks': 6, 'six-blocks-witnesses': 6, 'seven-blocks': 7,
                  'eight-blocks': 8, 'nine-blocks': 9, 'ten-blocks': 10}.get(args.boundary_catalogue, 13)
        check_boundary_catalogue(blocks=blocks, exhaustive=not args.boundary_catalogue.endswith('witnesses'))
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
