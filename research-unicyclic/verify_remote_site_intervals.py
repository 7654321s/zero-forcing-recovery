"""Replay local killing pairs with a remote long path on the cycle."""

import argparse
from collections import Counter
import hashlib
import json
from itertools import combinations
from pathlib import Path
import random
import runpy


HERE = Path(__file__).resolve().parent
interval = runpy.run_path(str(HERE / 'verify_long_interval_ports.py'))
branch = interval['branch']
tools = branch['tools']
attach = branch['attach_path']
bits = branch['bits']
neighbors = branch['neighbors']


def local_candidates(adj):
    cycle = branch['cycle_vertices'](adj)
    _, children = branch['tree_structure'](adj, cycle)
    paths = {}
    for v in cycle:
        arms = branch['pendant_paths'](v, children)
        if arms is not None and len(arms) == 1:
            paths[v] = arms[0]
    full = (1 << len(adj)) - 1
    for a, remote in sorted(paths.items()):
        length = len(remote)
        if length < 5:
            continue
        for p, left in sorted(paths.items()):
            if p == a or len(left) > length:
                continue
            order = tools['cycle_order'](adj, cycle, p)
            for ring in (order, order[:1] + order[:0:-1]):
                distance = next(i for i, v in enumerate(ring[1:], 1) if children[v])
                if distance == 1 and children[ring[2]]:
                    q = ring[2]
                    inner = ring[1]
                    if inner not in paths or inner == a or len(paths[inner]) > length:
                        continue
                elif 2 <= distance <= 4:
                    q = ring[distance]
                    inner = None
                else:
                    continue
                if q == a or q not in paths or len(paths[q]) > length:
                    continue
                if any(v in cycle and not children[v]
                       for v in neighbors(adj[a] & adj[q])):
                    continue
                right = paths[q]
                white = bits(remote) | (bits(left) ^ bits(left[:1] + left[1:-1:2]))
                white |= bits(right) ^ bits(right[1:-1:2])
                if inner is not None:
                    center = paths[inner]
                    if len(center) == 1:
                        white |= 1 << inner
                        second = center[0]
                        case = 'short_middle_path'
                    else:
                        white |= bits(center) ^ bits(center[:-1:2])
                        second = inner
                        case = 'deep_middle_path'
                else:
                    second = ring[distance-1]
                    if distance > 2:
                        white |= 1 << ring[1]
                    case = f'bare_interval_{distance-1}'
                slow = next(v for v in neighbors(adj[a]) if v in cycle)
                yield dict(case=case, centers=[a, p, q], blue=full ^ white,
                           killing=bits((left[0], second)), slow=1 << slow,
                           restricted_deadline=length)


def with_paths(n, placements):
    adj = list(branch['family']['cycle_graph'](n))
    for site, lengths in placements.items():
        for length in lengths:
            attach(adj, site, length)
    return adj


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    time = runpy.run_path(str(branch['BASELINE']))['completion_time']
    counts = Counter()
    constructions = 0

    def verify(adj, cert):
        delayed = time(adj, cert['blue'] ^ cert['slow'])
        assert delayed < len(adj)+1
        tools['verify_certificate'](time, adj, cert['blue'], cert['killing'], cert['slow'],
                                    cert['restricted_deadline'], delayed)
        counts[cert['case']] += 1

    # Every placement of seven sites on rings of length seven through eleven.
    rng = random.Random(20261118)
    for n in range(7, 12):
        for sites in combinations(range(n), 7):
            for extra in (False, True):
                placements = {site: [rng.randrange(1, 6)] for site in sites}
                marked = rng.choice(sites)
                placements[marked] = [5]
                if extra:
                    other = rng.choice([s for s in sites if s != marked])
                    placements[other] = [1, 4]
                adj = with_paths(n, placements)
                cert = next(local_candidates(adj), None)
                if cert is None:
                    cert = next(interval['candidates'](adj), None)
                    assert cert is not None, (n, placements)
                    cert['case'] = 'long_interval'
                verify(adj, cert)
                constructions += 1

    # Explicitly exercise each local form with an exterior of variable length.
    for gap in range(4):
        for middle in (1, 2, 5, 17):
            for length in (5, 17, 62):
                if middle > length:
                    continue
                q = max(2, gap+1)
                n = q+8
                placements = {0: [length], q: [length], q+4: [length], q+6: [3, 2]}
                if gap == 0:
                    placements[1] = [middle]
                adj = with_paths(n, placements)
                matches = [c for c in local_candidates(adj) if c['centers'] == [q+4, 0, q]]
                assert matches, (gap, middle, length)
                for cert in matches:
                    verify(adj, cert)

    assert set(counts) >= {'bare_interval_1', 'bare_interval_2', 'bare_interval_3',
                           'short_middle_path', 'deep_middle_path'}
    report = dict(status='passed', complete_placement_replays=constructions, grid_counts=dict(counts),
                  script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    with args.output.open('x', encoding='utf-8') as output:
        output.write(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
