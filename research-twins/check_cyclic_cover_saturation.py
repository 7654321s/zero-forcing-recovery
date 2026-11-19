"""Check finite forts and the two-block saturation threshold for cyclic covers."""

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

    sheets = 9
    for blocks in range(2, 10):
        graph, blue, _, _ = signed_prism_cover(blocks, sheets)
        outer = mask(v for v in range(len(graph)) if v % sheets in (0, sheets - 1))
        _, arrivals = MODEL['trace'](graph, outer)
        fort = mask(v for v, arrival in enumerate(arrivals) if arrival is None)
        cost = fort_cost(graph, blue, fort)
        if cost > 26 * blocks + 55:
            raise AssertionError(('nine-sheet fort cost', blocks, cost))

    width = sheets * 16
    stage_two = sheets * 34
    stage_three = stage_two + width
    stage_four = stage_three + width
    block_mask = (1 << width) - 1
    middle = fort >> stage_three & block_mask
    if (fort >> stage_two & block_mask != middle or fort >> stage_four & block_mask != middle
            or (blue >> stage_three & middle).bit_count() != 26 or cost != 26 * 9 + 55):
        raise AssertionError('The three interior stage patterns do not match')
    larger, larger_blue, _, _ = signed_prism_cover(10, sheets)
    prefix = (1 << stage_four) - 1
    extended = (fort & prefix) | (middle << stage_four) | ((fort & ~prefix) << width)
    if fort_cost(larger, larger_blue, extended) != cost + 26:
        raise AssertionError('Copying the middle stage changes the fort constraints')


def check_seed_window():
    sheets = 11
    residues = {i % sheets for i in SEED_WINDOW}
    for blocks in range(2, 15):
        graph, blue, _, _ = signed_prism_cover(blocks, sheets)
        band = mask(v for v in members(blue) if v % sheets in residues)
        _, arrivals = MODEL['trace'](graph, band)
        if any(time is None or time > 2 for time in arrivals[::sheets]):
            raise AssertionError(('The seed window does not fill sheet zero by round two', blocks))


def check_nonwrapping_lower_bound():
    """Rule out a cost-at-most-15 fort with a cut between two empty layers."""
    budget = 15
    sheets = (len(SEED_WINDOW) + 1) * budget + 1
    graph, blue, _, _ = signed_prism_cover(2, sheets)
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
        with Solver(name='glucose4', bootstrap_with=clauses) as solver:
            if solver.solve():
                white = set(solver.get_model())
                witness = tuple(v for v in members(blue) if v + 1 in white)
                raise AssertionError(('unexpected small nonwrapping fort', witness))


if __name__ == '__main__':
    check_witnesses()
    print('Explicit sixteen-seed and repeatable nine-sheet forts verified', flush=True)
    check_seed_window()
    print('Six-sheet seed window verified through fourteen blocks', flush=True)
    check_nonwrapping_lower_bound()
    print('Nonwrapping two-block forts require at least sixteen seeds', flush=True)
