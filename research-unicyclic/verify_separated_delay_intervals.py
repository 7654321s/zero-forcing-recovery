"""Replay disjoint local killing and delayed remote intervals."""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random
import runpy


HERE = Path(__file__).resolve().parent
dense = runpy.run_path(str(HERE / 'verify_dense_path_sites.py'))
branch = dense['branch']
tools = dense['tools']
bits = branch['bits']
with_paths = dense['with_paths']
partial = dense['partial_path']


def candidates(adj):
    cycle = branch['cycle_vertices'](adj)
    _, children = branch['tree_structure'](adj, cycle)
    paths = dense['paths_at'](children, cycle)
    full = (1 << len(adj)) - 1
    for a, outer in sorted(paths.items()):
        length = len(outer)
        if length < 2:
            continue
        order = tools['cycle_order'](adj, cycle, a)
        for ring in (order, order[:1] + order[:0:-1]):
            y, t = ring[1:3]
            if any(not children[v] for v in children[t]):
                continue
            middle = paths.get(y, [])
            if (children[y] and not middle) or len(middle) > length:
                continue
            remote_white = bits(outer + middle) | (1 << y)
            span = ring[5:-2]
            positions = [i for i, v in enumerate(span) if children[v]]
            for index in range(len(positions)-1):
                i, j = positions[index:index+2]
                p, q = span[i], span[j]
                if p not in paths or q not in paths:
                    continue
                gap = j-i-1
                left = paths[p]
                right = paths[q]
                if gap in (1, 2, 3):
                    if max(len(left), len(right)) > 2*length-1:
                        continue
                    if gap == 1:
                        white = partial(left, True) | partial(right, False)
                        killing = (left[0], span[i+1])
                    else:
                        white = partial(left, False) | partial(right, False)
                        killing = (span[i+1], span[j-1])
                    case = f'two_intervals_gap_{gap}'
                elif gap == 0 and index+2 < len(positions) and positions[index+2] == j+1:
                    x = q
                    q = span[j+1]
                    if q not in paths:
                        continue
                    right = paths[q]
                    if max(len(left), len(right), len(paths[x])) > 2*length-1:
                        continue
                    white = partial(left, True) | partial(right, False)
                    if len(paths[x]) == 1:
                        white |= 1 << x
                        second = paths[x][0]
                    else:
                        white |= bits(paths[x]) ^ bits(paths[x][:-1:2])
                        second = x
                    killing = (left[0], second)
                    case = 'two_intervals_middle'
                else:
                    continue
                yield dense['record'](case, full, white | remote_white, killing, t,
                                      length+1, length+2)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    time = runpy.run_path(str(branch['BASELINE']))['completion_time']
    rng = random.Random(103362)
    counts = Counter()

    def verify(adj, cert):
        tools['verify_certificate'](time, adj, cert['blue'], cert['killing'], cert['slow'],
                                    cert['restricted_deadline'], cert['slow_completion_time'])
        counts[cert['case']] += 1

    placement_replays = 0
    for n in range(9, 29):
        for _ in range(21):
            size = rng.randrange(9, n+1)
            sites = sorted(rng.sample(range(n), size))
            adj = with_paths(n, {v: [2] for v in sites})
            cert = (next(dense['staggered_candidates'](adj), None)
                    or next(candidates(adj), None)
                    or next(remote_long(adj), None))
            assert cert, (n, sites)
            verify(adj, cert)
            placement_replays += 1

    for gap in (0, 1, 2, 3):
        n = 16+gap
        for length in (2, 3, 9, 38):
            for middle in (0, 1, 2):
                placements = {0: [length], 2: [2, 3], 7: [length]}
                if middle:
                    placements[1] = [middle]
                if gap:
                    placements[8+gap] = [length]
                else:
                    placements.update({8: [1], 9: [length]})
                adj = with_paths(n, placements)
                desired = 'two_intervals_middle' if not gap else f'two_intervals_gap_{gap}'
                cert = next(c for c in candidates(adj) if c['case'] == desired)
                verify(adj, cert)
    assert all(counts[k] for k in ('two_intervals_middle', 'two_intervals_gap_1',
                                   'two_intervals_gap_2', 'two_intervals_gap_3'))
    report = {'status': 'passed', 'placement_replays': placement_replays,
              'grid_counts': dict(counts),
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    with args.output.open('x', encoding='utf-8') as output:
        output.write(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


def remote_long(adj):
    for cert in dense['remote']['interval']['candidates'](adj):
        yield {**cert, 'case': 'long_interval'}


if __name__ == '__main__':
    main()
