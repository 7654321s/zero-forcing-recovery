"""Check fort witnesses and saturated blocking numbers in signed cyclic covers."""

from collections import defaultdict
from itertools import combinations, pairwise
from pathlib import Path
import runpy

from pysat.card import ITotalizer
from pysat.solvers import Solver


MODEL = runpy.run_path(str(Path(__file__).with_name('check_multiple_loss_bounds.py')))
members = MODEL['members']
mask = MODEL['mask']
SEED_WINDOW = range(-3, 3)
TWO_BLOCK_FORT = (
    (0, 3), (3, 1), (3, 3), (4, 1), (5, 4), (6, 2), (6, 3), (6, 4), (7, 3),
    (9, 4), (9, 5), (11, 3), (12, 2), (12, 3), (13, 4), (14, 3), (14, 4),
    (15, 3), (15, 5), (16, 3), (16, 5), (17, 4), (18, 6), (19, 6), (20, 3),
    (21, 6), (22, 3), (25, 5), (26, 5), (27, 5), (28, 6), (29, 5), (29, 6),
)

THREE_BLOCK_FORT = (
    (0, 1), (2, 2), (3, 2), (4, 1), (4, 2), (5, 3), (6, 2), (7, 2),
    (11, 4), (12, 2), (14, 4), (16, 3), (16, 4), (18, 4), (20, 4),
    (22, 2), (23, 4), (24, 4), (26, 4), (27, 4), (27, 5), (28, 4), (29, 5),
    (32, 6), (33, 6), (34, 6), (35, 4), (36, 6), (37, 5), (38, 3), (38, 4),
    (39, 6), (40, 4), (40, 6), (41, 5), (42, 6), (43, 6), (44, 6), (45, 7),
    (46, 6), (48, 8), (49, 8),
)
FOUR_BLOCK_FORT = (
    (0, 1), (3, 1), (5, 2), (6, 1), (6, 2), (7, 1), (9, 2), (9, 3), (12, 1),
    (13, 2), (15, 3), (18, 3), (18, 4), (19, 4), (21, 4), (22, 1), (26, 3),
    (27, 3), (27, 4), (28, 3), (28, 4), (29, 4), (31, 4), (35, 3), (36, 5),
    (37, 5), (37, 6), (38, 4), (39, 3), (39, 4), (39, 5), (40, 3), (40, 4),
    (41, 4), (42, 5), (43, 4), (43, 5), (44, 4), (44, 5), (45, 5),
    (47, 5), (47, 6), (48, 5), (48, 6), (48, 7), (49, 5),
)


def signed_prism_cover(blocks, sheets):
    base = MODEL['cubic_two_round_chain_certificate'](blocks)
    return MODEL['cyclic_cubic_chain_lift'](base, sheets, reversed_edge=(0, 1))


def fort_cost(graph, blue, fort):
    if not fort or any((row & fort).bit_count() == 1 for v, row in enumerate(graph) if not fort & (1 << v)):
        raise AssertionError('Expected a nonempty fort')
    return (blue & fort).bit_count()


def check_witnesses():
    for sheets in (2, 6, 8, 9, 12, 106):
        graph, blue, _, _ = signed_prism_cover(2, sheets)
        fort = mask({sheets * v + sheet % sheets for v, sheet in TWO_BLOCK_FORT})
        cost = fort_cost(graph, blue, fort)
        if cost > 16 or (sheets >= 8 and cost != 16):
            raise AssertionError(('two-block fort cost', sheets, cost))


    for blocks, sheets, pairs, expected in (
        (3, 10, THREE_BLOCK_FORT, 21),
        (4, 9, FOUR_BLOCK_FORT, 24),
        (5, 9, FOUR_BLOCK_FORT, 24),
    ):
        graph, blue, _, _ = signed_prism_cover(blocks, sheets)
        white = mask(sheets * v + sheet for v, sheet in pairs)
        if fort_cost(graph, blue, white) != expected:
            raise AssertionError(('finite fort cost', blocks, expected))

    def base_edges(blocks):
        graph = MODEL['cubic_two_round_chain_certificate'](blocks)[0]
        return {(v, u) for v, row in enumerate(graph) for u in members(row) if v < u}

    four, five, six = (base_edges(k) for k in (4, 5, 6))
    support = {v for v, _ in FOUR_BLOCK_FORT}
    for changes, later in ((four - five, five - six), (five - four, six - five)):
        if any(u in support or v in support for u, v in changes):
            raise AssertionError('The stage insertion meets the fort')
        translated = {tuple(v if v == 16 else v + 16 for v in edge) for edge in changes}
        if later != translated:
            raise AssertionError('The stage insertion does not translate')


def check_seed_window():
    sheets = 11
    residues = {i % sheets for i in SEED_WINDOW}
    for blocks in range(2, 15):
        graph, blue, _, _ = signed_prism_cover(blocks, sheets)
        band = mask(v for v in members(blue) if v % sheets in residues)
        _, arrivals = MODEL['trace'](graph, band)
        if any(time is None or time > 2 for time in arrivals[::sheets]):
            raise AssertionError(('The seed window does not fill sheet zero by round two', blocks))



def band_exceptions(blocks, width, losses, deadline):
    """List deletions for which the seed band does not certify a two-sheet gap."""
    sheets = 4 * deadline + 3
    graph, blue, _, _ = signed_prism_cover(blocks, sheets)
    seed_labels = tuple(v for v in members(blue) if v % sheets < width)
    band = mask(seed_labels)
    columns = [range(s, len(graph), sheets) for s in range(width)]
    exceptions = defaultdict(set)
    for removed in combinations(seed_labels, losses):
        _, arrivals = MODEL['trace'](graph, band ^ mask(removed))
        full = [all(arrivals[v] is not None and arrivals[v] <= deadline for v in column)
                for column in columns]
        if any(left and right for left, right in pairwise(full)):
            continue
        pairs = sorted((v % sheets, v // sheets) for v in removed)
        exceptions[tuple(sheet for sheet, _ in pairs)].add(tuple(v for _, v in pairs))
    return exceptions


def gap_profiles(sheets, budget):
    """Enumerate feasible loss spacings up to rotating the choice of first seed."""
    first_margin = 7 * budget - 3 * sheets

    def extend(gaps, remaining):
        if len(gaps) == budget:
            x, y = gaps[-2:]
            a, b = gaps[:2]
            tail_margins = (7 - x - y - a, 7 - y - a - b)
            if min(tail_margins) < 0 or sum(tail_margins) != remaining or y + a > 6:
                return
            if all(gaps <= gaps[i:] + gaps[:i] for i in range(1, budget)):
                yield gaps
            return
        x, y = gaps[-2:]
        smallest = max(gaps[0], 7 - x - y - remaining)
        largest = min(4, 6 - y, 7 - x - y)
        for z in range(smallest, largest + 1):
            yield from extend((*gaps, z), remaining - (7 - x - y - z))

    for first in range(5):
        for second in range(first, min(4, 6 - first) + 1):
            yield from extend((first, second), first_margin)


def permits_wrapping_fort(sheets, gaps, seed_labels, four_exceptions, six_exceptions):
    """Check necessary local conditions on the base labels of the lost seeds."""
    by_sheet = [[] for _ in range(sheets)]
    position = 0
    for i, gap in enumerate(gaps):
        by_sheet[position].append(i)
        position = (position + gap) % sheets
    domains = [set(seed_labels) for _ in gaps]
    relations = []
    for start in range(sheets):
        local = [(j, i) for j in range(6) for i in by_sheet[(start + j) % sheets]]
        short = [(j, i) for j, i in local if j < 4]
        if len(short) == 1:
            (offset, i), = short
            domains[i].intersection_update(label for (label,) in four_exceptions.get((offset,), ()))
            if not domains[i]:
                return False
        if len(local) == 2:
            (left, i), (right, j) = local
            allowed = six_exceptions.get((left, right))
            if not allowed:
                return False
            relations.append((i, j, allowed))

    while True:
        before = sum(map(len, domains))
        for i, j, pairs in relations:
            supported = [(a, b) for a, b in pairs if a in domains[i] and b in domains[j]]
            if not supported:
                return False
            domains[i].intersection_update(a for a, _ in supported)
            domains[j].intersection_update(b for _, b in supported)
        if sum(map(len, domains)) == before:
            return True


def check_wrapping_lower_bound():
    four_exceptions = band_exceptions(2, 4, 1, 13)
    six_exceptions = band_exceptions(2, 6, 2, 13)
    if any(left == right for left, right in six_exceptions):
        raise AssertionError('The two-loss exceptions must occupy two different sheets')
    _, seeds, _, _ = signed_prism_cover(2, 2)
    labels = sorted({v // 2 for v in members(seeds)})
    for sheets in range(31, 36):
        checked = 0
        for budget in range((3 * sheets + 6) // 7, 16):
            for gaps in gap_profiles(sheets, budget):
                if permits_wrapping_fort(sheets, gaps, labels, four_exceptions, six_exceptions):
                    raise AssertionError(('wrapping profile survived', sheets, budget, gaps))
                checked += 1
        print(f'{sheets} sheets: {checked} possible loss spacings excluded', flush=True)


def check_nonwrapping_lower_bound(blocks, budget, width, losses, solver_name):
    """Exclude a low-cost fort between two empty guard sheets."""
    sheets = width * budget // (losses + 1) + width + 1
    graph, blue, _, _ = signed_prism_cover(blocks, sheets)
    order = len(graph)
    active = mask(v for v in range(order) if 0 < v % sheets < sheets - 1)
    occupied = list(range(order + 1, order + sheets + 1))
    suffix = list(range(order + sheets + 1, order + 2 * sheets + 2))
    clauses = [[-suffix[-1]], [occupied[1]]]
    clauses.extend([-(v + 1)] for v in range(order) if not active & (1 << v))
    for s, hit in enumerate(occupied):
        layer = [v + 1 for v in range(s, order, sheets) if active & (1 << v)]
        clauses.append([-hit, *layer])
        clauses.extend([-literal, hit] for literal in layer)
        tail, next_tail = suffix[s:s+2]
        clauses.extend(([-hit, tail], [-next_tail, tail], [-tail, hit, next_tail]))
        if 1 <= s < sheets - 1:
            # Retain just one component separated by gaps of two empty layers.
            clauses.append([hit, occupied[s+1], -suffix[s+2]])

    for v, row in enumerate(graph):
        if active & (1 << v) and not blue & (1 << v):
            area = 1 << v
            for _ in range(4):
                for u in members(area):
                    area |= graph[u]
            # A two-round nominal force needs a failed seed within distance four.
            clauses.append([-(v + 1), *(u + 1 for u in members(area & blue & active))])
        neighbors = tuple(members(row))
        for u in members(row & active):
            clauses.append([v + 1, -(u + 1), *(w + 1 for w in neighbors if w != u)])

    seeds = [v + 1 for v in members(blue & active)]
    with ITotalizer(lits=seeds, ubound=budget, top_id=suffix[-1]) as counter:
        clauses.extend(counter.cnf.clauses)
        clauses.append([-counter.rhs[budget]])
        with Solver(name=solver_name, bootstrap_with=clauses) as solver:
            if solver.solve():
                white = set(solver.get_model())
                witness = tuple(v for v in members(blue) if v + 1 in white)
                raise AssertionError(('unexpected small nonwrapping fort', witness))


if __name__ == '__main__':
    check_witnesses()
    print('Explicit forts of costs sixteen, twenty-one and twenty-four verified', flush=True)
    check_seed_window()
    print('Six-sheet seed window verified through fourteen blocks', flush=True)
    for blocks, width, losses, deadline in ((2, 4, 0, 8), (2, 6, 1, 6), (2, 7, 2, 13),
                                            (3, 6, 2, 18), (4, 6, 2, 18)):
        if band_exceptions(blocks, width, losses, deadline):
            raise AssertionError(('A local seed band failed', blocks, width, losses))
    print('Local seed bands verified', flush=True)
    check_wrapping_lower_bound()
    strips = ((2, 15, 7, 'glucose4'), (3, 20, 6, 'glucose4'), (4, 23, 6, 'cadical195'))
    for blocks, budget, width, solver_name in strips:
        check_nonwrapping_lower_bound(blocks, budget, width, 2, solver_name)
        print(f'{blocks} blocks: finite forts cost at least {budget + 1}', flush=True)
