"""Replay the complete size-31 catalogue and verify its boundary partition."""

import argparse
from collections import Counter, defaultdict
import gzip
from itertools import combinations
import json
from pathlib import Path
import runpy

from pysat.card import ITotalizer
from pysat.solvers import Solver


HERE = Path(__file__).resolve().parent
CHECK = runpy.run_path(str(HERE / 'check_cost_25_blocking_sets.py'))
stage_start = CHECK['SPAN']['BAND']['stage_start']
size = 31
near_blocks = 13
long_blocks = 36


def stage(label):
    opening = stage_start(1)
    return 0 if label < opening else 1 + (label - opening) // 16


def near_seed_stages(blocks):
    return set(range(6)) | {blocks - 3, blocks - 2, blocks - 1}


def anchor_stages(blocks):
    return {0, 1, 2, blocks - 2, blocks - 1}


def anchored(pattern, blocks):
    anchors = anchor_stages(blocks)
    return any(stage(vertex) in anchors for vertex, _ in pattern)


def read_patterns(rows):
    patterns = tuple(tuple(map(tuple, row)) for row in rows)
    if tuple(sorted(set(patterns))) != patterns or any(
            len(row) != size or len(set(row)) != size or CHECK['normalized'](row) != row
            for row in patterns):
        raise AssertionError('Unexpected size-31 boundary catalogue entries')
    return set(patterns)


def ordinary_placements(templates, blocks):
    return CHECK['ordinary_placements'](templates, blocks - 4)


def restrict_stages(clauses, seeds, order, sheets, allowed_seeds, required_groups, *,
                    blocks=near_blocks):
    allowed_fort = allowed_seeds | {(i - 1) % blocks for i in allowed_seeds}
    seed_stages = [(u, stage((u - 1) // sheets)) for u in seeds]
    clauses.extend([u for u, i in seed_stages if i in group] for group in required_groups)
    clauses.extend([-(v + 1)] for v in range(order) if stage(v // sheets) not in allowed_fort)
    clauses.extend([-u] for u, i in seed_stages if i not in allowed_seeds)
    return [u for u, i in seed_stages if i in allowed_seeds]


def check_partitions(near, outside, ordinary_types, shift):
    stages = near_seed_stages(near_blocks)
    lower, size_30 = CHECK['catalogues_through_size_30'](near_blocks)
    smaller = (*lower, *size_30)
    near_lower = tuple(row for row in smaller if all(stage(v) in stages for v, _ in row))
    ordinary = {row for row in ordinary_placements(ordinary_types, near_blocks)
                if all(stage(v) in stages for v, _ in row)}
    if len(ordinary) != 194 or len(near_lower) != 9098 or ordinary & near:
        raise AssertionError('Unexpected reduced catalogue in the near partition')

    def restrict_near(clauses, seeds, order, sheets):
        return restrict_stages(clauses, seeds, order, sheets, stages, (anchor_stages(near_blocks),))

    known = near | ordinary
    if CHECK['enumerate_blockers'](near_blocks, near_lower, known, budget=size,
                                  restrict=restrict_near) != known:
        raise AssertionError('The near partition contains an unlisted size-31 loss')
    profile = Counter((CHECK['boundary_stage_arc'](row, near_blocks)[1],
                       max(sheet for _, sheet in row)) for row in near)
    print(json.dumps({'blocks': near_blocks, 'near_exhaustive': True, 'count': len(near),
                      'joint_spans': sorted((a, b, n) for (a, b), n in profile.items())}),
          flush=True)

    near_long = near_seed_stages(long_blocks)
    anchors = anchor_stages(long_blocks)
    counts = []
    for span in range(1, 5):
        for first in range(long_blocks):
            arc = {(first + j) % long_blocks for j in range(span)}
            if not (arc & anchors and arc - near_long):
                continue
            local_first = first - (long_blocks - near_blocks)
            local_last = local_first + span - 1
            allowed = set(range(local_first, local_last + 1))
            if not 1 <= local_first <= local_last < near_blocks:
                raise AssertionError(('Unexpected outer boundary window', first, span))
            window_lower = tuple(row for row in smaller if all(stage(v) in allowed for v, _ in row))
            known = {tuple((v - shift, sheet) for v, sheet in row) for row in outside
                     if CHECK['boundary_stage_arc'](row, long_blocks)[:2] == (first, span)}

            def restrict_window(clauses, seeds, order, sheets):
                return restrict_stages(clauses, seeds, order, sheets, allowed,
                                       ({local_first}, {local_last}))

            if CHECK['enumerate_blockers'](near_blocks, window_lower, known, budget=size,
                                          strip_sheets=37, restrict=restrict_window) != known:
                raise AssertionError(('An unlisted boundary loss survives', first, span))
            counts.append((first, span, len(known)))
    if counts != [(32, 3, 97), (31, 4, 0), (32, 4, 0)]:
        raise AssertionError(('Unexpected outer boundary counts', counts))
    print(json.dumps({'outside_exhaustive_at_span_at_most_four': counts}), flush=True)


def check_long_stage_span():
    blocks, sheets = long_blocks, 39
    lower, size_30 = CHECK['catalogues_through_size_30'](blocks)
    graph, blue, *_ = CHECK['COVER']['signed_prism_cover'](blocks, sheets)
    clauses, seeds, top = CHECK['STRIP']['strip_formula'](
        graph, blue, size, sheets=sheets, quotient_bounds=False, require_minimal=True)
    groups = [[] for _ in range(blocks)]
    for u in seeds:
        groups[stage((u - 1) // sheets)].append(u)
    clauses.append([u for i in anchor_stages(blocks) for u in groups[i]])
    occupied = list(range(top + 1, top + blocks + 1))
    top += blocks
    for marker, group in zip(occupied, groups):
        clauses.append([-marker, *group])
        clauses.extend([-u, marker] for u in group)
    separated = list(range(top + 1, top + blocks + 1))
    top += blocks
    for i, marker in enumerate(separated):
        clauses.append([-marker, occupied[i]])
        clauses.append([-marker, *(occupied[(i + d) % blocks] for d in range(4, blocks - 3))])
    clauses.append(separated)
    for row in (*lower, *size_30):
        clauses.extend(CHECK['block_translations'](row, sheets))
    print('36 blocks: checking anchored seed supports spanning at least five stages', flush=True)
    with ITotalizer(lits=seeds, ubound=size, top_id=top) as counter:
        with Solver(name='cadical195', bootstrap_with=clauses + counter.cnf.clauses) as solver:
            if solver.solve(assumptions=[-counter.rhs[size]]):
                raise AssertionError('An anchored size-31 loss spans at least five stages')
    print(json.dumps({'blocks': blocks, 'maximum_stage_span': 4}), flush=True)


def read_boundary_catalogue():
    with gzip.open(HERE / 'degree-31-boundary-catalogue.json.gz', 'rt', encoding='utf-8') as src:
        archive = json.load(src)
    if (archive['schema_version'], archive['size'], archive['first_sheet'],
            archive['near_blocks'], archive['long_blocks']) != (1, size, 1, near_blocks, long_blocks):
        raise AssertionError('Unexpected size-31 boundary catalogue metadata')
    near = read_patterns(archive['near'])
    outside = read_patterns(archive['outside'])
    if len(near) != 17857 or len(outside) != 97:
        raise AssertionError('Unexpected sizes of the boundary witness catalogues')
    if any(not anchored(row, near_blocks) or
           any(stage(v) not in near_seed_stages(near_blocks) for v, _ in row) for row in near):
        raise AssertionError('Witness outside the near partition')
    if any(not anchored(row, long_blocks) or
           all(stage(v) in near_seed_stages(long_blocks) for v, _ in row) or
           CHECK['boundary_stage_arc'](row, long_blocks)[:2] != (32, 3) for row in outside):
        raise AssertionError('Witness outside the complementary boundary partition')
    return near, outside


def long_catalogue(near, outside, ordinary_types):
    ordinary = ordinary_placements(ordinary_types, long_blocks)
    shift = stage_start(long_blocks - 3) - stage_start(near_blocks - 3)
    lifted_near = {tuple((v + shift if stage(v) >= near_blocks - 3 else v, sheet)
                         for v, sheet in row) for row in near}
    candidates = ordinary | lifted_near | outside
    if len(ordinary) != 2910 or len(candidates) != len(ordinary) + len(near) + len(outside):
        raise AssertionError('The long representative has duplicate boundary placements')
    return candidates, shift


def check_boundary_catalogue(*, partitions=False):
    near, outside = read_boundary_catalogue()
    _, ordinary_types, _ = CHECK['ordinary_size_31_catalogue']()
    translated = {tuple((v + stage_start(32), sheet) for v, sheet in row)
                  for row in ordinary_types}
    if outside != translated:
        raise AssertionError('The terminal window differs from the ordinary templates')
    candidates, shift = long_catalogue(near, outside, ordinary_types)

    smaller, size_30 = CHECK['catalogues_through_size_30'](long_blocks)
    print(f'{long_blocks} blocks: checking {len(candidates)} distinct size-31 witnesses', flush=True)
    verified = CHECK['verify_inherited_patterns'](
        long_blocks, (*smaller, *size_30), sorted(candidates), budget=size, already_lifted=True)
    if verified != candidates:
        raise AssertionError('The size-31 witness catalogue changed during replay')
    if partitions:
        check_partitions(near, outside, ordinary_types, shift)
    print(json.dumps({'blocks': long_blocks, 'size': size, 'witnesses': len(verified),
                      'ordinary': len(verified) - len(near) - len(outside),
                      'near': len(near), 'outside': len(outside)}),
          flush=True)


def transferred_catalogue(blocks):
    near, outside = read_boundary_catalogue()
    ordinary = [tuple((v - stage_start(32), sheet) for v, sheet in row) for row in outside]
    source, _ = long_catalogue(near, outside, ordinary)
    transferred = CHECK['relocate_boundary_patterns'](source, long_blocks, blocks)
    if len(transferred) != 97 * blocks + 17372:
        raise AssertionError(('Unexpected transferred size-31 count', blocks))
    return transferred


def check_short_catalogue(blocks):
    known = set(transferred_catalogue(blocks))
    lower, size_30 = CHECK['catalogues_through_size_30'](blocks)
    smaller = (*lower, *size_30)
    print(f'{blocks} blocks: checking {len(known)} size-31 witnesses', flush=True)
    verified = CHECK['verify_inherited_patterns'](
        blocks, smaller, sorted(known), budget=size, already_lifted=True)
    if verified != known:
        raise AssertionError(('The short witness catalogue changed during replay', blocks))
    if CHECK['enumerate_blockers'](blocks, smaller, known, budget=size, strip_sheets=37,
                                  require_minimal_fort=True,
                                  occupied_stage_pairs=blocks < 13) != known:
        raise AssertionError(('An unlisted size-31 loss survives', blocks))
    print(json.dumps({'blocks': blocks, 'size': size, 'count': len(known), 'exhaustive': True}),
          flush=True)


def check_five_blocks(*, exhaustive=False):
    blocks = 5
    with gzip.open(HERE / 'five-block-size-31-catalogue.json.gz', 'rt', encoding='utf-8') as src:
        archive = json.load(src)
    if (archive['schema_version'], archive['blocks'], archive['size'],
            archive['first_sheet']) != (1, blocks, size, 1):
        raise AssertionError('Unexpected five-block size-31 catalogue metadata')
    known = read_patterns(archive['losses'])
    by_stage = defaultdict(set)
    for row in known:
        by_stage[tuple(sorted({stage(v) for v, _ in row}))].add(row)
    support_counts = {''.join(map(str, stages)): len(rows) for stages, rows in by_stage.items()}
    spans = Counter(max(sheet for _, sheet in row) for row in known)
    if (len(known) != 17858 or support_counts != archive['stage_support_counts']
            or {str(k): v for k, v in spans.items()} != archive['sheet_spans']):
        raise AssertionError('Unexpected five-block size-31 catalogue counts')

    sheets = 28
    graph, blue, *_ = CHECK['COVER']['signed_prism_cover'](blocks, sheets)
    _, _, cones = CHECK['LOSS_COMPONENTS']['nominal_cones'](graph, blue)
    print(f'{blocks} blocks: checking {len(known)} witnesses and their one-seed restorations',
          flush=True)
    for row in sorted(known):
        lost = CHECK['mask'](v * sheets + sheet + 4 for v, sheet in row)
        if lost & blue != lost or lost.bit_count() != size:
            raise AssertionError(('Invalid five-block seed coordinates', row))
        fort = CHECK['remaining_white'](graph, cones, lost)
        if fort & blue != lost or any(v % sheets in (0, sheets - 1) for v in CHECK['members'](fort)):
            raise AssertionError(('Five-block witness lacks a guarded fort', row))
        for seed in CHECK['members'](lost):
            if CHECK['remaining_white'](graph, cones, lost ^ (1 << seed)):
                raise AssertionError(('Five-block witness has a blocking proper subset', row, seed))
    if exhaustive:
        lower, size_30 = CHECK['catalogues_through_size_30'](blocks)
        smaller = (*lower, *size_30)
        for width in range(1, blocks + 1):
            for stages in combinations(range(blocks), width):
                permitted = set(stages)
                contained = tuple(row for row in smaller if all(stage(v) in permitted for v, _ in row))
                expected = by_stage.get(stages, set())

                def restrict_mask(clauses, seeds, order, sheets):
                    return restrict_stages(clauses, seeds, order, sheets, permitted,
                                           tuple({i} for i in stages), blocks=blocks)

                result = CHECK['enumerate_blockers'](blocks, contained, expected, budget=size,
                                                     strip_sheets=sheets, require_minimal_fort=True,
                                                     restrict=restrict_mask)
                if result != expected:
                    raise AssertionError(('Unlisted five-block size-31 loss', stages))
                print(f'Stage support {stages}: {len(result)}', flush=True)
    print(json.dumps({'blocks': blocks, 'size': size, 'count': len(known),
                      'exhaustive': exhaustive, 'blocking_coefficient_per_sheet': len(known) - 13174,
                      'single_restorations': size * len(known),
                      'sheet_spans': dict(sorted(spans.items()))}), flush=True)


def check_degree_32_overlap_representative():
    blocks = 12
    size_31 = transferred_catalogue(blocks)
    lower, size_30 = CHECK['catalogues_through_size_30'](blocks)
    losses = (*lower, *size_30, *size_31)
    print(f'{blocks} blocks: counting order-32 unions of {len(losses)} smaller losses', flush=True)
    weights, span = CHECK['signed_union_weights'](losses, 32)
    summed = {degree: sum(w * n for w, n in profile.items())
              for degree, profile in weights.items()}
    expected = {-4: 8, -3: 1, -2: 1451, -1: 69612, 0: 11764,
                1: 25206, 2: 771, 3: 15, 4: 3}
    if span != 13 or summed[31] != 89 * blocks + 4238 or weights[32] != expected:
        raise AssertionError(('Unexpected overlaps in the degree-32 representative', span, summed))
    print(json.dumps({'blocks': blocks, 'maximum_sheet_span': span, 'weights': weights[32],
                      'overlap_per_sheet': summed[32], 'boundary_intercept': summed[32] + 205 * blocks}),
          flush=True)


def check_degree_32_outer_windows():
    blocks = 13
    representative = 37
    lower, size_30 = CHECK['catalogues_through_size_30'](blocks)
    smaller = (*lower, *size_30, *transferred_catalogue(blocks))
    _, ordinary, _ = CHECK['ordinary_size_32_catalogue']()
    counts = []
    for first, span in ((33, 3), (32, 4), (33, 4)):
        local = first - (representative - blocks)
        last = local + span - 1
        allowed = set(range(local, last + 1))
        contained = tuple(row for row in smaller if all(stage(v) in allowed for v, _ in row))

        def restrict_window(clauses, seeds, order, sheets):
            return restrict_stages(clauses, seeds, order, sheets, allowed, ({local}, {last}))

        result = CHECK['enumerate_blockers'](blocks, contained, budget=32, strip_sheets=38,
                                             require_minimal_fort=True, restrict=restrict_window)
        expected = {tuple((v + stage_start(local), sheet) for v, sheet in row)
                    for row in ordinary} if span == 3 else set()
        if result != expected:
            raise AssertionError(('Unexpected size-32 outer catalogue', first, span, len(result)))
        counts.append((first, span, len(result)))
    print(json.dumps({'blocks': representative, 'outside_windows': counts}), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--partitions', action='store_true',
                       help='also exhaust the boundary windows of span at most four')
    modes.add_argument('--long-stage-span', action='store_true',
                       help='exclude all anchored losses of stage span at least five')
    modes.add_argument('--short-catalogue', type=int, choices=range(7, 14), metavar='BLOCKS',
                       help='verify a complete shorter-chain size-31 catalogue')
    modes.add_argument('--five-blocks', choices=('witnesses', 'exhaustive'),
                       help='replay the five-block size-31 catalogue and optionally exhaust its stage supports')
    modes.add_argument('--degree-32-overlap', action='store_true',
                       help='count degree-32 overlaps in the transferred 12-block catalogue')
    modes.add_argument('--degree-32-outer-windows', action='store_true',
                       help='verify the three short outer windows at size 32')
    args = parser.parse_args()
    if args.long_stage_span:
        check_long_stage_span()
    elif args.short_catalogue:
        check_short_catalogue(args.short_catalogue)
    elif args.five_blocks:
        check_five_blocks(exhaustive=args.five_blocks == 'exhaustive')
    elif args.degree_32_overlap:
        check_degree_32_overlap_representative()
    elif args.degree_32_outer_windows:
        check_degree_32_outer_windows()
    else:
        check_boundary_catalogue(partitions=args.partitions)
