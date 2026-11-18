"""Independently check padding certificates and coverage of all unbounded length cases."""

import argparse
from collections import defaultdict
import hashlib
from itertools import combinations, product
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
generation = runpy.run_path(str(HERE / 'verify_path_padding_reduction.py'))
branch = generation['branch']
neighbors = branch['neighbors']
bits = branch['bits']
verify = generation['tools']['verify_certificate']
intact_without = generation['lift']['forces_except']


def round_once(adj, blue):
    additions = 0
    white = ((1 << len(adj))-1) ^ blue
    for v in neighbors(blue):
        targets = adj[v] & white
        if targets and targets & (targets-1) == 0:
            additions |= targets
    return blue | additions


def first_arrivals(adj, blue, destinations):
    times = {}
    t = 0
    while len(times) < len(destinations):
        times.update((v, t) for v in destinations if v not in times and blue & (1 << v))
        t += 1
        after = round_once(adj, blue)
        if len(times) < len(destinations):
            assert after != blue
        blue = after
    return times


def equiv(gaps, lengths):
    n = len(gaps)
    for k in range(n):
        for sign in (1, -1):
            at = [(k + sign*j) % n for j in range(n)]
            gp = tuple(gaps[(i-(sign < 0)) % n] for i in at)
            yield gp, tuple(lengths[i] for i in at)


def validate_group(key, rows, time):
    gaps, lengths, variables = key
    adj = list(branch['family']['cycle_graph'](len(gaps)+sum(gaps)))
    ends = []
    p = 0
    for g, length in zip(gaps, lengths):
        ends.append(branch['attach_path'](adj, p, length))
        p += g+1
    proven = set()
    for row in rows:
        blue, H, slow = (row[x] for x in ('blue', 'killing', 'slow'))
        assert 0 < blue < 1 << len(adj) and (H | slow) & ~blue == 0
        assert H.bit_count() == 2 and slow.bit_count() == 1
        verify(time, adj, blue, H, slow, row['restricted_deadline'], row['slow_completion_time'])
        restricted = [blue, *[blue ^ (1 << h) for h in neighbors(H)]]
        neutral, white = (set(row[x]) for x in ('neutral', 'white'))
        assert neutral.isdisjoint(white) and neutral | white == set(variables)
        for i in neutral:
            bit = 1 << ends[i]
            for pattern in (*restricted, blue ^ H, blue ^ slow):
                assert round_once(adj, pattern) & bit
            assert not blue & bit or adj[ends[i]] & blue or intact_without(adj, blue, ends[i])
        assert not blue & bits(ends[i] for i in white)
        early = [first_arrivals(adj, pattern, [ends[i] for i in white]) for pattern in restricted]
        late = first_arrivals(adj, blue ^ slow, [ends[i] for i in white])
        deadlines = {i: max(ins[ends[i]] for ins in early) for i in white}
        assert {str(i): deadlines[i] for i in white} == row['boundary_deadlines']
        assert {str(i): late[ends[i]] for i in white} == row['slow_boundary']
        for a in row['maxima']:
            assert a in variables
            assert all(late[ends[i]] > deadlines[i]
                       or (a in white and late[ends[a]] > deadlines[i]) for i in white)
            proven.add(a)
    return proven


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    folder = Path(__file__).resolve().parent
    source = (folder / 'path-padding-reduction-replay.json').read_bytes()
    report = json.loads(source)
    assert report['status'] == 'passed' and not report['unresolved']
    assert report['script_sha256'] == hashlib.sha256(
        (folder / 'verify_path_padding_reduction.py').read_bytes()).hexdigest()
    time = runpy.run_path(str(branch['BASELINE']))['completion_time']
    groups = defaultdict(list)
    for row in report['certificates']:
        key = (tuple(row['gaps']), tuple(row['minimum_lengths']),
               tuple(sorted(row['neutral'] + row['white'])))
        groups[key].append(row)
    covered = {k: validate_group(k, rows, time) for k, rows in groups.items()}

    visited = set()
    splits = []
    known = 0
    for count in range(3, 6):
        for gaps in product(range(4), repeat=count):
            if count+sum(gaps) < 5 or min(g for g, _ in equiv(gaps, gaps)) != gaps:
                continue
            for lengths in product((1, 2), repeat=count):
                if max(lengths) == 1 or min(equiv(gaps, lengths)) != (gaps, lengths):
                    continue
                variables = tuple(i for i,L in enumerate(lengths) if L == 2)
                key = gaps, lengths, variables
                known += 1
                if key in covered:
                    visited.add(key)
                absent = set(variables) - covered.get(key, set())
                if not absent:
                    continue
                # The exact base, with all increments zero, has lengths in {1,2}.
                splits.append(dict(gaps=gaps, lengths=lengths, maxima=sorted(absent)))
                for size in range(1, len(variables)+1):
                    for growing in combinations(variables, size):
                        relevant = absent.intersection(growing)
                        if not relevant:
                            continue
                        next_lengths = tuple(x + (i in growing) for i, x in enumerate(lengths))
                        child = gaps, next_lengths, growing
                        assert relevant <= covered[child], (child, relevant)
                        visited.add(child)
    assert visited == set(covered)
    answer = dict(status='passed', initial_layouts=known, checked_palette_groups=len(groups),
                  checked_certificates=sum(map(len, groups.values())), splits=splits,
                  certificate_file_sha256=hashlib.sha256(source).hexdigest(),
                  checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    with args.output.open('x', encoding='utf-8') as out:
        json.dump(answer, out, indent=2)
        out.write('\n')
    print(json.dumps(answer, indent=2))


if __name__ == '__main__':
    main()
