"""Certify unbounded pendant lengths using finite palettes and terminal times."""

import argparse
from collections import Counter
from functools import lru_cache
import hashlib
from itertools import combinations, product
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
bounded = runpy.run_path(str(HERE / 'verify_short_path_mixtures_complete.py'))
lift = runpy.run_path(str(HERE / 'verify_leaf_lifts.py'))
branch = bounded['branch']
tools = bounded['tools']
bits = branch['bits']
neighbors = branch['neighbors']
attach = branch['attach_path']
from_word = bounded['mixtures']['ring_from_word']


def trace(adj, blue):
    full = (1 << len(adj))-1
    arrival = [None] * len(adj)
    for v in neighbors(blue):
        arrival[v] = 0
    elapsed = 0
    while blue != full:
        added = 0
        for v in neighbors(blue):
            w = adj[v] & ~blue
            if w.bit_count() == 1:
                added |= w
        if not added:
            return len(adj)+1, tuple(arrival)
        elapsed += 1
        for v in neighbors(added):
            arrival[v] = elapsed
        blue |= added
    return elapsed, tuple(arrival)


def solve(adj, arms, variable, required, extra_limit):
    """Return certified subsets of longest arms and the remaining marked cases."""
    full = (1 << len(adj))-1
    infinity = len(adj)+1
    ends = {i: arms[i][-1] for i in variable}
    tests = tuple(bounded['arc_forts'](adj))

    @lru_cache(maxsize=None)
    def timing(blue):
        return trace(adj, blue)

    @lru_cache(maxsize=None)
    def restorable_with_white_stub(blue, end):
        return (not blue & (1 << end) or bool(adj[end] & blue)
                or lift['forces_except'](adj, blue, end))

    def fits(blue, killing, unresolved):
        h1, h2 = neighbors(killing)
        restricted = (blue, blue ^ (1 << h1), blue ^ (1 << h2))
        clocks = [timing(x) for x in restricted]
        early = max(elapsed for elapsed, _ in clocks)
        if early >= infinity:
            return

        double = blue ^ killing
        base_patterns = (*restricted, double)
        safe = {i for i, v in ends.items()
                if all(timing(x)[1][v] in (0, 1) for x in base_patterns)
                and restorable_with_white_stub(blue, v)}
        if any(i not in safe and blue & (1 << end) for i, end in ends.items()):
            return

        singles = {v: timing(blue ^ (1 << v)) for v in neighbors(blue)}
        if any(t == infinity for t, _ in singles.values()):
            return
        assert timing(double)[0] == infinity
        for v, (late, delays) in sorted(singles.items(), key=lambda item: -item[1][0]):
            if late <= early:
                break
            neutral = {i for i in safe if delays[ends[i]] <= 1}
            white = set(variable) - neutral
            if any(blue & (1 << ends[i]) for i in white):
                continue
            early_at = {i: max(times[ends[i]] for _, times in clocks) for i in white}
            covered = [a for a in sorted(unresolved)
                       if all(delays[ends[i]] > early_at[i]
                              or (a in white and delays[ends[a]] > early_at[i])
                              for i in white)]
            if covered:
                yield dict(blue=blue, killing=killing, slow=1 << v,
                           restricted_deadline=early, slow_completion_time=late,
                           neutral=sorted(neutral), white=sorted(white), maxima=covered,
                           boundary_deadlines=early_at,
                           slow_boundary={i: delays[ends[i]] for i in white})

    unresolved = set(required)
    result = []
    for extra in range(extra_limit+1):
        for fort in tests:
            outside = full ^ fort
            inside_pairs = tuple(bits(pair) for pair in combinations(neighbors(fort), 2))
            for added_white in combinations(neighbors(outside), extra):
                blue_outside = outside ^ bits(added_white)
                for killing in inside_pairs:
                    for proof in fits(blue_outside | killing, killing, unresolved):
                        unresolved.difference_update(proof['maxima'])
                        result.append(proof)
                        if not unresolved:
                            return result, unresolved
    return result, unresolved


def paths(adj):
    ring = branch['cycle_vertices'](adj)
    _, children = branch['tree_structure'](adj, ring)
    at = bounded['mixtures']['dense']['paths_at'](children, ring)
    return [at[v] for v in sorted(at)]


def replay(adj, arms, proof, time, extended=False):
    tools['verify_certificate'](time, adj, proof['blue'], proof['killing'], proof['slow'],
                                proof['restricted_deadline'], proof['slow_completion_time'])
    if not extended:
        return
    for index, a in enumerate(proof['maxima']):
        growing = proof['neutral'] + proof['white']
        increments = {i: (1 + (i+index)%4 if i != a else 5) for i in growing}
        blue = proof['blue']
        enlarged = adj.copy()
        for i in growing:
            start = len(enlarged)
            attach(enlarged, arms[i][-1], increments[i])
            if i in proof['neutral']:
                blue |= bits(range(start, len(enlarged)))
        early = max([proof['restricted_deadline']]
                    + [proof['boundary_deadlines'][i]+increments[i] for i in proof['white']])
        late = max([proof['slow_completion_time']]
                   + [proof['slow_boundary'][i]+increments[i] for i in proof['white']])
        tools['verify_certificate'](time, enlarged, blue, proof['killing'], proof['slow'], early, late)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    pinned_time = runpy.run_path(str(branch['BASELINE']))['completion_time']
    counts = Counter()
    entries = []
    unresolved = []

    def visit(gaps, lengths, variable, required, depth):
        adj = from_word(gaps, lengths)
        arms = paths(adj)
        proofs, missing = solve(adj, arms, variable, required, 1 if depth == 0 else 2)
        for proof in proofs:
            replay(adj, arms, proof, pinned_time,
                   extended=depth > 0 or counts['certificates'] % 13 == 0)
            entries.append(dict(gaps=gaps, minimum_lengths=lengths, **proof))
            counts['certificates'] += 1
        counts['nodes'] += 1
        if not missing:
            return

        if depth == 0:
            extra, missing = solve(adj, arms, variable, missing, 2)
            for proof in extra:
                replay(adj, arms, proof, pinned_time, extended=True)
                entries.append(dict(gaps=gaps, minimum_lengths=lengths, **proof))
                counts['certificates'] += 1
            if not missing:
                return

        if depth >= 2:
            unresolved.append(dict(gaps=gaps, minimum_lengths=lengths,
                                   variable=variable, marked_maxima=sorted(missing)))
            return

        counts['splits'] += 1
        for size in range(1, len(variable)+1):
            for grow in combinations(variable, size):
                marks = missing.intersection(grow)
                if marks:
                    newer = tuple(L+(i in grow) for i, L in enumerate(lengths))
                    visit(gaps, newer, grow, marks, depth+1)

    for count in range(3, 6):
        for gaps in product(range(4), repeat=count):
            if gaps != bounded['uniform']['canonical'](gaps) or count+sum(gaps) < 5:
                continue
            actions = tuple(bounded['stabilizer'](gaps))
            for lengths in product((1, 2), repeat=count):
                if max(lengths) == 1 or any(tuple(lengths[i] for i in perm) < lengths
                                           for perm in actions[1:]):
                    continue
                variable = tuple(i for i, L in enumerate(lengths) if L == 2)
                visit(gaps, lengths, variable, set(variable), 0)
                counts['layouts'] += 1
        print(json.dumps({'sites': count, 'counts': dict(counts),
                          'unresolved': len(unresolved)}), flush=True)

    report = {'status': 'passed' if not unresolved else 'partial',
              'counts': dict(counts), 'unresolved': unresolved,
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'certificates': entries}
    with args.output.open('x', encoding='utf-8') as output:
        output.write(json.dumps(report, indent=2) + '\n')


if __name__ == '__main__':
    main()
