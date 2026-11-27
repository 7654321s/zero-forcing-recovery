"""Verify the degree-33 boundary windows and overlap representative."""

import argparse
from collections import Counter, defaultdict
import gzip
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
ORDINARY = runpy.run_path(str(HERE / 'check_degree_33_ordinary.py'))
NEAR = runpy.run_path(str(HERE / 'check_degree_32_boundary.py'))
BOUNDARY = ORDINARY['BOUNDARY']
CHECK = ORDINARY['CHECK']
STAGE_START = ORDINARY['STAGE_START']


def transferred_smaller_losses(blocks, ordinary_32):
    lower, size_30 = CHECK['catalogues_through_size_30'](blocks)
    ordinary = BOUNDARY['ordinary_placements'](ordinary_32, blocks)
    ordinary.update(tuple((v + STAGE_START(blocks - 4), s) for v, s in row)
                    for row in ordinary_32)
    first_terminal = NEAR['BLOCKS'] - 3
    shift = STAGE_START(blocks - 3) - STAGE_START(first_terminal)
    near = (tuple((v + shift if BOUNDARY['stage'](v) >= first_terminal else v, s)
                  for v, s in row) for row in NEAR['read_catalogue']())
    smaller = (*lower, *size_30, *BOUNDARY['transferred_catalogue'](blocks), *ordinary, *near)
    if len(set(smaller)) != len(smaller):
        raise AssertionError('A smaller loss was placed twice')
    return smaller


def overlap_stage_components(losses, blocks, budget):
    # A joining union contains at least the larger count in every stage.
    profiles = defaultdict(list)
    stage = BOUNDARY['stage']
    for row in losses:
        counts = [0] * blocks
        for vertex, _ in row:
            counts[stage(vertex)] += 1
        profiles[tuple(counts)].append(row)
    keys = sorted(profiles, key=lambda counts: len(profiles[counts]), reverse=True)
    sizes = tuple(map(sum, keys))
    supports = [sum(1 << i for i, n in enumerate(counts) if n) for counts in keys]
    parents = list(range(len(keys)))
    weights = [len(profiles[counts]) for counts in keys]

    def root(index):
        while parents[index] != index:
            parents[index] = parents[parents[index]]
            index = parents[index]
        return index

    for i, p in enumerate(keys):
        for j in range(i):
            a, b = root(i), root(j)
            if a == b or not supports[i] & supports[j]:
                continue
            remaining = 2 * budget - sizes[i] - sizes[j]
            for x, y in zip(p, keys[j]):
                remaining -= abs(x - y)
                if remaining < 0:
                    break
            if remaining >= 0:
                if weights[a] < weights[b]:
                    a, b = b, a
                parents[b] = a
                weights[a] += weights[b]
    groups = defaultdict(list)
    for i, counts in enumerate(keys):
        groups[root(i)].extend(profiles[counts])
    return sorted(groups.values(), key=len, reverse=True)


def check_overlap_representative():
    blocks = 12
    families = ORDINARY['read_catalogues']()
    smaller = transferred_smaller_losses(blocks, families[2])
    if (len(smaller) != 80549
            or any(CHECK['boundary_stage_arc'](row, blocks)[1] > 4 for row in smaller)
            or max(s for row in smaller for _, s in row) != 13):
        raise AssertionError('Unexpected lower-order families in the overlap representative')
    groups = overlap_stage_components(smaller, blocks, 33)
    if list(map(len, groups)) != [71003, 6058, 424] + [383] * 8:
        raise AssertionError('Unexpected degree-33 overlap components')

    ordinary = tuple(sorted(row for family in families[:3] for row in family))
    profiles = defaultdict(Counter)
    ordinary_weights, span = CHECK['signed_union_weights'](ordinary, 33)
    for group in groups[3:]:
        offset = min(v for row in group for v, _ in row) - min(v for row in ordinary for v, _ in row)
        shifted = tuple(sorted(tuple((v - offset, s) for v, s in row) for row in group))
        if shifted != ordinary:
            raise AssertionError('A small overlap component differs from the ordinary placements')
        for degree, weights in ordinary_weights.items():
            profiles[degree].update(weights)

    for group, expected in ((groups[2], -477), (groups[1], -12063), (groups[0], None)):
        labels = {v: i for i, v in enumerate(sorted({v for row in group for v, _ in row}))}
        dense = [tuple((labels[v], s) for v, s in row) for row in group]
        print(f'Counting degree-33 unions of the {len(group)}-loss component', flush=True)
        weights, component_span = CHECK['signed_union_weights'](dense, 33)
        subtotal = sum(w * n for w, n in weights[33].items())
        if expected is not None and subtotal != expected:
            raise AssertionError(('Unexpected overlap subtotal', len(group), subtotal))
        print(json.dumps({'losses': len(group), 'signed_subtotal': subtotal}), flush=True)
        span = max(span, component_span)
        for degree, profile in weights.items():
            profiles[degree].update(profile)

    counts = {degree: sum(weight * multiplicity for weight, multiplicity in profile.items())
              for degree, profile in profiles.items()}
    if counts[31] != 89 * blocks + 4238 or counts[32] != 71 * blocks + 6269:
        raise AssertionError('The lower-degree coefficients differ from the certified values')
    print(json.dumps({'blocks': blocks, 'largest_sheet_span': span, 'weights': profiles[33],
                      'overlap_per_sheet': counts[33],
                      'boundary_intercept': counts[33] + 980 * blocks}), flush=True)


def check_short_outer_windows():
    blocks, representative, sheets = 13, 38, 40
    families = ORDINARY['read_catalogues']()
    smaller = transferred_smaller_losses(blocks, families[2])
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


def short_near_windows(blocks):
    region = [blocks - 3, blocks - 2, blocks - 1, *range(6)]
    opening = {0, 1, 2}
    anchors = BOUNDARY['anchor_stages'](blocks)
    for span in range(1, 5):
        for offset in range(len(region) - span + 1):
            arc = region[offset:offset + span]
            stages = set(arc)
            if stages & anchors and not opening <= stages:
                yield arc


def read_short_near_catalogue():
    blocks = 13
    with gzip.open(HERE / 'degree-33-short-near-catalogue.json.gz', 'rt', encoding='utf-8') as src:
        archive = json.load(src)
    if (archive['schema_version'], archive['blocks'], archive['size']) != (1, blocks, 33):
        raise AssertionError('Unexpected short near-boundary catalogue format')
    grouped = {}
    for item in archive['windows']:
        key = item['start'], item['span']
        rows = tuple(tuple(map(tuple, row)) for row in item['losses'])
        if (key in grouped or rows != tuple(sorted(set(rows))) or
                any(len(row) != 33 or len(set(row)) != 33 or CHECK['normalized'](row) != row or
                    CHECK['boundary_stage_arc'](row, blocks)[:2] != key or
                    not BOUNDARY['anchored'](row, blocks) for row in rows)):
            raise AssertionError(('Unexpected short near-boundary loss', key))
        grouped[key] = rows
    counts = {key: len(rows) for key, rows in grouped.items()}
    if counts != {(11, 2): 634, (10, 3): 1757, (11, 3): 6722, (1, 3): 420, (10, 4): 4}:
        raise AssertionError(('Unexpected short near-boundary counts', counts))
    return grouped


def replay_near_witnesses(rows, blocks, sheets):
    graph, blue, *_ = CHECK['COVER']['signed_prism_cover'](blocks, sheets)
    _, _, cones = CHECK['LOSS_COMPONENTS']['nominal_cones'](graph, blue)
    for row in rows:
        lost = CHECK['mask'](v * sheets + s + 4 for v, s in row)
        if lost & blue != lost or lost.bit_count() != 33:
            raise AssertionError(('Invalid seed coordinates', row))
        fort = CHECK['remaining_white'](graph, cones, lost)
        if fort & blue != lost or any(v % sheets in (0, sheets - 1)
                                      for v in CHECK['members'](fort)):
            raise AssertionError(('No guarded fort', row))
        for seed in CHECK['members'](lost):
            if CHECK['remaining_white'](graph, cones, lost ^ (1 << seed)):
                raise AssertionError(('A proper subset blocks recovery', row, seed))
    print(json.dumps({'checked': len(rows), 'restorations': len(rows) * 33}), flush=True)


def check_opening_four_catalogue(*, exhaustive=False):
    blocks, sheets = 13, 40
    with gzip.open(HERE / 'degree-33-opening-span-four-catalogue.json.gz', 'rt',
                   encoding='utf-8') as src:
        archive = json.load(src)
    if (archive['schema_version'], archive['blocks'], archive['size']) != (1, blocks, 33):
        raise AssertionError('Unexpected opening-window catalogue format')
    rows = tuple(tuple(map(tuple, row)) for row in archive['losses'])
    if (len(rows) != 847 or rows != tuple(sorted(set(rows))) or
            any(len(row) != 33 or len(set(row)) != 33 or CHECK['normalized'](row) != row or
                CHECK['boundary_stage_arc'](row, blocks)[:2] != (0, 4) for row in rows)):
        raise AssertionError('Unexpected size-33 opening-window losses')
    if not exhaustive:
        replay_near_witnesses(rows, blocks, sheets)
        return

    allowed = {0, 1, 2, 3}
    families = ORDINARY['read_catalogues']()
    smaller = [row for row in transferred_smaller_losses(blocks, families[2])
               if allowed.issuperset(NEAR['support'](row))]

    def restrict(clauses, seeds, order, period):
        return BOUNDARY['restrict_stages'](
            clauses, seeds, order, period, allowed, ({0}, {3}), blocks=blocks)

    known = set(rows)
    result = CHECK['enumerate_blockers'](
        blocks, smaller, known, budget=33, strip_sheets=sheets, require_minimal_fort=True,
        restrict=restrict, stream_blockers=True)
    if result != known:
        raise AssertionError(('Additional four-stage opening losses', len(result - known)))
    print(json.dumps({'start': 0, 'span': 4, 'catalogued': len(known)}), flush=True)


def read_opening_three_catalogue():
    with gzip.open(HERE / 'degree-33-opening-span-three-catalogue.json.gz', 'rt',
                   encoding='utf-8') as src:
        archive = json.load(src)
    if (archive['schema_version'], archive['blocks'], archive['size']) != (1, 13, 33):
        raise AssertionError('Unexpected three-stage opening catalogue format')
    rows = tuple(tuple(map(tuple, row)) for row in archive['losses'])
    if len(rows) != 127407 or rows != tuple(sorted(set(rows))):
        raise AssertionError('Unexpected number of three-stage opening losses')
    observed = Counter()
    stage = BOUNDARY['stage']
    for row in rows:
        support = Counter(stage(v) for v, _ in row)
        if (len(row) != 33 or len(set(row)) != 33 or CHECK['normalized'](row) != row
                or set(support) != {0, 1, 2}):
            raise AssertionError('Unexpected three-stage opening coordinates')
        observed[tuple(support[i] for i in range(3))] += 1
    expected = {(a, b, 33-a-b) for a in range(1, 32) for b in range(1, 33-a)}
    profiles = {tuple(item['counts']): item['types'] for item in archive['profiles']}
    if (len(archive['profiles']) != 496 or profiles.keys() != expected
            or any(observed[key] != n for key, n in profiles.items())):
        raise AssertionError('Unexpected counts of the three-stage opening profiles')
    return rows


def check_opening_triple_geometry():
    cover = CHECK['COVER']['signed_prism_cover']
    full, full_blue, *_ = cover(13, 5)
    compact, compact_blue, *_ = cover(6, 5)
    stage = BOUNDARY['stage']
    mapping = {}
    for old, new in ((11, 4), (12, 5), (0, 0), (1, 1), (2, 2), (3, 3)):
        source = [v for v in range(len(full) // 5) if stage(v) == old]
        target = [v for v in range(len(compact) // 5) if stage(v) == new]
        if len(source) != len(target):
            raise AssertionError('Different sizes of corresponding opening stages')
        mapping.update(zip(source, target))
    for v, image in mapping.items():
        if stage(v) not in {12, 0, 1, 2}:
            continue
        for s in range(5):
            u, w = 5 * v + s, 5 * image + s
            neighbors = {(mapping[neighbor], sheet)
                         for site in CHECK['members'](full[u])
                         for neighbor, sheet in (divmod(site, 5),)}
            if (neighbors != {divmod(site, 5) for site in CHECK['members'](compact[w])}
                    or bool(full_blue & (1 << u)) != bool(compact_blue & (1 << w))):
                raise AssertionError('The compact opening window changes an incident edge or seed')


def check_opening_three_catalogue(*, exhaustive=False):
    rows = read_opening_three_catalogue()
    if not exhaustive:
        replay_near_witnesses(rows, 13, 40)
        return

    from pysat.card import ITotalizer
    from pysat.solvers import Solver

    check_opening_triple_geometry()
    blocks, sheets, budget, seed_anchor = 6, 44, 33, 5
    stages = {0, 1, 2}
    graph, blue, *_ = CHECK['COVER']['signed_prism_cover'](blocks, sheets)
    clauses, seeds, top = CHECK['STRIP']['strip_formula'](
        graph, blue, budget, sheets=sheets, quotient_bounds=False, require_minimal=True,
        anchor_fort=False)
    seeds = BOUNDARY['restrict_stages'](
        clauses, seeds, len(graph), sheets, stages, ({0}, {1}, {2}), blocks=blocks)
    clauses.extend([-u] for u in seeds if (u - 1) % sheets < seed_anchor)
    seeds = [u for u in seeds if (u - 1) % sheets >= seed_anchor]
    clauses.append([u for u in seeds if (u - 1) % sheets == seed_anchor])
    smaller = [row for row in transferred_smaller_losses(13, ORDINARY['read_catalogues']()[2])
               if stages.issuperset(NEAR['support'](row))]
    if len(smaller) != 71003:
        raise AssertionError('Unexpected lower-order opening catalogue')
    print(f'Excluding {len(smaller)} smaller types and {len(rows)} anchored size-33 types',
          flush=True)
    with ITotalizer(lits=seeds, ubound=budget, top_id=top) as counter:
        with Solver(name='cadical195', bootstrap_with=clauses + counter.cnf.clauses) as solver:
            for row in smaller:
                last = max(s for _, s in row)
                for shift in range(seed_anchor - 1, sheets - 1 - last):
                    solver.add_clause([-(v * sheets + s + shift + 1) for v, s in row])
            for row in rows:
                solver.add_clause([-(v * sheets + s + seed_anchor) for v, s in row])
            if solver.solve(assumptions=[-counter.rhs[budget]]):
                chosen = {v for v in solver.get_model() if v > 0}
                loss = CHECK['normalized'](divmod(v - 1, sheets) for v in seeds if v in chosen)
                raise AssertionError(('Additional three-stage opening loss', loss))
    print(json.dumps({'start': 0, 'span': 3, 'catalogued': len(rows)}), flush=True)


def check_short_near_catalogue(*, exhaustive=False):
    blocks, sheets = 13, 40
    grouped = read_short_near_catalogue()
    windows = tuple(short_near_windows(blocks))
    if len(windows) != 20:
        raise AssertionError('Unexpected number of short near-boundary windows')
    if not exhaustive:
        rows = tuple(row for group in grouped.values() for row in group)
        replay_near_witnesses(rows, blocks, sheets)
        return

    families = ORDINARY['read_catalogues']()
    smaller = transferred_smaller_losses(blocks, families[2])
    supports = [(row, set(NEAR['support'](row))) for row in smaller]
    anchors = BOUNDARY['anchor_stages'](blocks)
    for arc in windows:
        allowed = set(arc)
        first, last = arc[0], arc[-1]
        contained = [row for row, stages in supports if stages <= allowed]
        known = set(grouped.get((first, len(arc)), ()))
        if arc == [2, 3, 4]:
            known.update(tuple((v + STAGE_START(2), s) for v, s in row) for row in families[3])

        def restrict(clauses, seeds, order, period):
            return BOUNDARY['restrict_stages'](
                clauses, seeds, order, period, allowed, ({first}, {last}, anchors), blocks=blocks)

        result = CHECK['enumerate_blockers'](
            blocks, contained, known, budget=33, strip_sheets=sheets, require_minimal_fort=True,
            restrict=restrict, stream_blockers=True)
        if result != known:
            raise AssertionError(('Additional short near-boundary losses', arc, len(result - known)))
        print(json.dumps({'start': first, 'span': len(arc), 'catalogued': len(known)}), flush=True)


def check_empty_near_windows():
    blocks, sheets = 13, 39
    region = [blocks - 3, blocks - 2, blocks - 1, *range(6)]
    windows = [[blocks - 1, 0, 1, 2]]
    windows.extend(region[i:i + span]
                   for span in range(5, 10) for i in range(len(region) - span + 1))
    families = ORDINARY['read_catalogues']()
    stage = BOUNDARY['stage']
    smaller = [(row, set(NEAR['support'](row)))
               for row in transferred_smaller_losses(blocks, families[2])]
    cases = [(arc, set(arc)) for arc in windows]
    cases.append(([0, 1, 2], {0, 2}))
    for arc, allowed in cases:
        required = [{arc[0]}, {arc[-1]},
                    *(set(arc[i:i + 3]) for i in range(1, len(arc) - 3))]
        contained = [row for row, stages in smaller if stages <= allowed]

        def restrict(clauses, seeds, order, period):
            selected = BOUNDARY['restrict_stages'](
                clauses, seeds, order, period, allowed, required, blocks=blocks)
            for left, right in zip(arc[1:-1], arc[2:-1]):
                clauses.append([v + 1 for v in range(order)
                                if stage(v // period) in {left, right}])
            return selected

        result = CHECK['enumerate_blockers'](
            blocks, contained, budget=33, strip_sheets=sheets, require_minimal_fort=True,
            restrict=restrict, stream_blockers=True)
        if result:
            raise AssertionError(('Unexpected additional near-boundary losses', arc, len(result)))
        print(json.dumps({'start': arc[0], 'span': len(arc), 'allowed': sorted(allowed),
                          'catalogued': 0}), flush=True)


def check_outer_windows(last_span):
    ordinary_32 = ORDINARY['read_catalogues']()[2]
    NEAR['check_outer_windows'](
        last_span, representative=38, budget=33, sheets=39,
        rows_for_blocks=lambda blocks: transferred_smaller_losses(blocks, ordinary_32))


def check_far_outer_windows():
    blocks = 38
    smaller = transferred_smaller_losses(blocks, ORDINARY['read_catalogues']()[2])
    if len(smaller) != 90507:
        raise AssertionError('Unexpected lower-order archive size at 38 blocks')
    NEAR['check_far_outer_windows'](blocks=blocks, sheets=39, budget=33, smaller=smaller)


def check_middle_outer_windows():
    from pysat.card import CardEnc, EncType, ITotalizer
    from pysat.solvers import Solver

    blocks, sheets, budget = 38, 39, 33
    stage = BOUNDARY['stage']
    graph, blue, *_ = CHECK['COVER']['signed_prism_cover'](blocks, sheets)
    clauses, seeds, top = CHECK['STRIP']['strip_formula'](
        graph, blue, budget, sheets=sheets, quotient_bounds=False, require_minimal=True)
    seed_groups = [[] for _ in range(blocks)]
    fort_groups = [[] for _ in range(blocks)]
    for seed in seeds:
        seed_groups[stage((seed - 1) // sheets)].append(seed)
    for vertex in range(len(graph)):
        if 0 < vertex % sheets < sheets - 1:
            fort_groups[stage(vertex // sheets)].append(vertex + 1)
    anchors = BOUNDARY['anchor_stages'](blocks)
    outside = set(range(blocks)) - BOUNDARY['near_seed_stages'](blocks)
    for stages in (anchors, outside):
        clauses.append([u for i in stages for u in seed_groups[i]])

    inside, occupied, fort, starts = [
        list(range(top + i * blocks + 1, top + (i + 1) * blocks + 1)) for i in range(4)]
    top = starts[-1]
    for i in range(blocks):
        prev, following, third = (i - 1) % blocks, (i + 1) % blocks, (i + 2) % blocks
        clauses.extend(([-occupied[i], *seed_groups[i]], [-fort[i], *fort_groups[i]]))
        clauses.extend([-seed, occupied[i]] for seed in seed_groups[i])
        clauses.extend([-vertex, fort[i]] for vertex in fort_groups[i])
        clauses.extend(([-occupied[i], inside[i]], [-fort[i], inside[i], inside[following]]))
        # A single cyclic 0-to-1 transition determines the arc start.
        clauses.extend(([-starts[i], inside[i]], [-starts[i], -inside[prev]],
                        [starts[i], -inside[i], inside[prev]], [-starts[i], occupied[i]],
                        [-inside[i], inside[following], occupied[i]]))
        clauses.append([-inside[i], -inside[following], fort[i], fort[following]])
        clauses.append([-inside[i], -inside[following], -inside[third],
                        occupied[i], occupied[following], occupied[third]])

    for encode, variables, bound in ((CardEnc.equals, starts, 1),
                                     (CardEnc.atleast, inside, 14),
                                     (CardEnc.atmost, inside, 22)):
        requirement = encode(variables, bound=bound, top_id=top, encoding=EncType.seqcounter)
        clauses.extend(requirement.clauses)
        top = requirement.nv
    smaller = transferred_smaller_losses(blocks, ORDINARY['read_catalogues']()[2])
    if len(smaller) != 90507:
        raise AssertionError('Unexpected lower-order archive size at 38 blocks')
    print('Checking anchored outer arcs of spans 14 through 22', flush=True)
    with ITotalizer(lits=seeds, ubound=budget, top_id=top) as counter:
        with Solver(name='cadical195', bootstrap_with=clauses + counter.cnf.clauses) as solver:
            for row in smaller:
                for clause in CHECK['block_translations'](row, sheets):
                    solver.add_clause(clause)
            if solver.solve(assumptions=[-counter.rhs[budget]]):
                chosen = {v for v in solver.get_model() if v > 0}
                loss = CHECK['normalized'](divmod(v - 1, sheets) for v in seeds if v in chosen)
                raise AssertionError(('Unexpected middle outer loss', loss))
    print(json.dumps({'blocks': blocks, 'spans': [14, 22], 'outer_losses': 0}), flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--overlap', action='store_true',
                      help='count the signed degree-33 unions in the twelve-block representative')
    mode.add_argument('--near-short', choices=('witnesses', 'exhaustive'),
                      help='replay the short near-boundary windows omitting an opening stage')
    mode.add_argument('--near-empty', action='store_true',
                      help='exclude longer near arcs and the terminal opening window')
    mode.add_argument('--outer-far', action='store_true',
                      help='exclude anchored outer arcs of span at least 23')
    mode.add_argument('--outer-through', type=int, choices=range(5, 15),
                      metavar='SPAN', help='exclude anchored outer arcs from span five')
    mode.add_argument('--opening-four', choices=('witnesses', 'exhaustive'),
                      help='check the size-33 opening window of span four')
    mode.add_argument('--outer-middle', action='store_true',
                      help='exclude anchored outer arcs of spans 14 through 22 together')
    mode.add_argument('--opening-three', choices=('witnesses', 'exhaustive'),
                      help='replay the complete three-stage opening catalogue')
    args = parser.parse_args()
    if args.overlap:
        check_overlap_representative()
    elif args.outer_middle:
        check_middle_outer_windows()
    elif args.outer_through:
        check_outer_windows(args.outer_through)
    elif args.outer_far:
        check_far_outer_windows()
    elif args.near_empty:
        check_empty_near_windows()
    elif args.opening_three:
        check_opening_three_catalogue(exhaustive=args.opening_three == 'exhaustive')
    elif args.opening_four:
        check_opening_four_catalogue(exhaustive=args.opening_four == 'exhaustive')
    elif args.near_short:
        check_short_near_catalogue(exhaustive=args.near_short == 'exhaustive')
    else:
        check_short_outer_windows()
