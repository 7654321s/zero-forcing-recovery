"""Replay the complete size-31 catalogue and verify its boundary partition."""

import argparse
from collections import Counter
import gzip
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


def restrict_stages(clauses, seeds, order, sheets, allowed_seeds, required_groups):
    allowed_fort = allowed_seeds | {(i - 1) % near_blocks for i in allowed_seeds}
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


def check_boundary_catalogue(*, partitions=False):
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

    _, ordinary_types, _ = CHECK['ordinary_size_31_catalogue']()
    ordinary = ordinary_placements(ordinary_types, long_blocks)
    translated = {tuple((v + stage_start(32), sheet) for v, sheet in row)
                  for row in ordinary_types}
    if outside != translated:
        raise AssertionError('The terminal window differs from the ordinary templates')
    shift = stage_start(long_blocks - 3) - stage_start(near_blocks - 3)
    lifted_near = {tuple((v + shift if stage(v) >= near_blocks - 3 else v, sheet)
                         for v, sheet in row) for row in near}
    candidates = ordinary | lifted_near | outside
    if len(ordinary) != 2910 or len(candidates) != len(ordinary) + len(near) + len(outside):
        raise AssertionError('The long representative has duplicate boundary placements')

    smaller, size_30 = CHECK['catalogues_through_size_30'](long_blocks)
    print(f'{long_blocks} blocks: checking {len(candidates)} distinct size-31 witnesses', flush=True)
    verified = CHECK['verify_inherited_patterns'](
        long_blocks, (*smaller, *size_30), sorted(candidates), budget=size, already_lifted=True)
    if verified != candidates:
        raise AssertionError('The size-31 witness catalogue changed during replay')
    if partitions:
        check_partitions(near, outside, ordinary_types, shift)
    print(json.dumps({'blocks': long_blocks, 'size': size, 'witnesses': len(verified),
                      'ordinary': len(ordinary), 'near': len(near), 'outside': len(outside)}),
          flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument('--partitions', action='store_true',
                       help='also exhaust the boundary windows of span at most four')
    modes.add_argument('--long-stage-span', action='store_true',
                       help='exclude all anchored losses of stage span at least five')
    args = parser.parse_args()
    if args.long_stage_span:
        check_long_stage_span()
    else:
        check_boundary_catalogue(partitions=args.partitions)
