"""Exclude the remaining wrapped forts in the 33-sheet prism cover."""

from pathlib import Path
import runpy

from pysat.card import CardEnc, EncType
from pysat.solvers import Solver


HERE = Path(__file__).resolve().parent
STRIP = runpy.run_path(str(HERE / 'check_finite_fort_strip.py'))
BLOCK = runpy.run_path(str(HERE / 'check_block_stabilization.py'))
LOSS = runpy.run_path(str(HERE / 'check_loss_components.py'))
CHECKS = STRIP['CHECKS']
members = STRIP['members']
SHEETS = 33
BAND = 13
BUDGET = 23


def seed_profiles():
    """Reconstruct profiles from the two excess units in the band counts."""
    for separation in range(SHEETS // 2 + 1):
        band_counts = [9] * SHEETS
        band_counts[0] += 1
        band_counts[separation] += 1
        offsets = [0] * SHEETS
        sheet = 0
        for _ in range(SHEETS - 1):
            next_sheet = (sheet + BAND) % SHEETS
            offsets[next_sheet] = offsets[sheet] + band_counts[(sheet + 1) % SHEETS] - band_counts[sheet]
            sheet = next_sheet
        first, remainder = divmod(BUDGET - sum(offsets), SHEETS)
        profile = tuple(first + offset for offset in offsets)
        if remainder or min(profile) < 0:
            continue
        if any(sum(profile[(i + j) % SHEETS] for j in range(w)) < w - 4
               for w in range(10, BAND + 1) for i in range(SHEETS)):
            continue
        if (sum(profile) != BUDGET or max(profile) != 1
                or [sum(profile[(i + j) % SHEETS] for j in range(BAND))
                    for i in range(SHEETS)] != band_counts):
            raise AssertionError(('unexpected profile', separation))
        yield separation, profile


def check_profiles():
    graph, blue, _, _ = CHECKS['signed_prism_cover'](26, SHEETS)
    order = len(graph)
    neighbors = [tuple(members(row)) for row in graph]
    clauses = list(BLOCK['fort_clauses'](graph, range(order)))
    clauses.extend(STRIP['minimal_fort_clauses'](neighbors))
    arrivals, supporters, _ = LOSS['nominal_cones'](graph, blue)
    for v in sorted(range(order), key=arrivals.__getitem__):
        if arrivals[v] > 0:
            clauses.append([-(v + 1), *(s + 1 for s in members(supporters[v]))])

    occupied_seeds = range(3 * order + 1, 3 * order + 1 + SHEETS)
    top = occupied_seeds[-1]
    for sheet, flag in enumerate(occupied_seeds):
        seed_vars = [v + 1 for v in range(sheet, order, SHEETS) if blue & (1 << v)]
        clauses.append([-flag, *seed_vars])
        clauses.extend([-v, flag] for v in seed_vars)
        one = CardEnc.atmost(lits=seed_vars, bound=1, top_id=top, encoding=EncType.seqcounter)
        clauses.extend(one.clauses)
        top = one.nv
        clauses.append([v + 1 for s in (sheet, (sheet + 1) % SHEETS)
                        for v in range(s, order, SHEETS)])

    # The certified 25-stage band provides an empty adjacent stage pair.
    empty = {}
    for stage in range(1, 26):
        top += 1
        empty[stage] = top
        start = BLOCK['stage_start'](stage)
        clauses.extend([-top, -(v + 1)] for v in range(start * SHEETS, (start + 16) * SHEETS))
    gaps = []
    for stage in range(1, 25):
        top += 1
        gaps.append(top)
        clauses.extend(([-top, empty[stage]], [-top, empty[stage + 1]]))
    clauses.append(gaps)

    with Solver(name='cadical195', bootstrap_with=clauses) as solver:
        count = 0
        for separation, profile in seed_profiles():
            assumptions = [flag if x else -flag for flag, x in zip(occupied_seeds, profile)]
            if solver.solve(assumptions=assumptions):
                fort = STRIP['mask'](v - 1 for v in solver.get_model() if 0 < v <= order)
                raise AssertionError(('wrapped fort', separation, CHECKS['fort_cost'](graph, blue, fort)))
            count += 1
    if count != 12:
        raise AssertionError(('incorrect number of profiles', count))
    witness = STRIP['mask'](v * SHEETS + sheet for v, sheet in CHECKS['FOUR_BLOCK_FORT'])
    if CHECKS['fort_cost'](graph, blue, witness) != 24:
        raise AssertionError('Missing the 24-seed witness')
    return count


if __name__ == '__main__':
    print(f'All {check_profiles()} wrapped seed profiles excluded at 33 sheets')
