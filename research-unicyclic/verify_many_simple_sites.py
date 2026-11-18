"""Replay longest-path comparisons with balanced short cycle gaps."""

import argparse
from collections import Counter
import hashlib
from itertools import product
import json
from pathlib import Path
import random
import runpy


HERE = Path(__file__).resolve().parent
short = runpy.run_path(str(HERE / 'verify_short_path_mixtures.py'))
dense = short['dense']
branch = short['branch']
tools = short['tools']
bits = short['bits']
partial = dense['partial_path']
neighbors = branch['neighbors']


def templates(adj):
    cycle = branch['cycle_vertices'](adj)
    _, children = branch['tree_structure'](adj, cycle)
    paths = dense['paths_at'](children, cycle)
    full = (1 << len(adj))-1
    for a, outer in sorted(paths.items()):
        M = len(outer)
        if M < 3:
            continue
        roots = tools['cycle_order'](adj, cycle, a)
        forbidden = {a, next(v for v in roots[1:] if children[v]),
                     next(v for v in roots[:0:-1] if children[v])}
        for p, left in sorted(paths.items()):
            if p in forbidden or len(left) > M:
                continue
            order = tools['cycle_order'](adj, cycle, p)
            for ring in (order, order[:1] + order[:0:-1]):
                i = next(i for i, v in enumerate(ring[1:], 1) if children[v])
                x = None
                if i == 1:
                    x, q = ring[1:3]
                    if x not in paths or x in forbidden or len(paths[x]) > M:
                        continue
                elif 2 <= i <= 4:
                    q = ring[i]
                else:
                    continue
                if q not in paths or q in forbidden or len(paths[q]) > M:
                    continue
                right = paths[q]
                white = bits(outer) | partial(right, False)
                if x is not None:
                    middle = paths[x]
                    if len(middle) == 1:
                        white |= 1 << x
                        second = middle[0]
                    else:
                        white |= bits(middle) ^ bits(middle[:-1:2])
                        second = x
                    white |= partial(left, True)
                    H = (left[0], second)
                    case = 'three_consecutive_sites'
                elif i == 2:
                    white |= partial(left, True)
                    H = (left[0], ring[1])
                    case = 'one_bare_vertex'
                else:
                    white |= partial(left, False)
                    H = (ring[1], ring[i-1])
                    case = f'{i-1}_bare_vertices'
                slow = next(v for v in neighbors(adj[a]) if v in cycle)
                yield dense['record'](case, full, white, H, slow, M, None)


def graph_with_exception(gaps, lengths, pos):
    n = len(gaps) + sum(gaps)
    vertices = [0]
    for gap in gaps[:-1]:
        vertices.append(vertices[-1] + gap + 1)
    placements = {v: [L] for v, L in zip(vertices, lengths)}
    if pos is not None:
        placements[vertices[pos]] = [1, 3]
    return dense['with_paths'](n, placements)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    time = runpy.run_path(str(branch['BASELINE']))['completion_time']
    counts = Counter()
    rng = random.Random(23770)

    def verify(adj, c):
        late = time(adj, c['blue'] ^ c['slow'])
        assert late < len(adj)+1
        tools['verify_certificate'](time, adj, c['blue'], c['killing'], c['slow'],
                                    c['restricted_deadline'], late)
        counts[c['case']] += 1

    for size, exception, gap in product((6, 9, 13), (False, True), (0, 1, 2, 3, 6)):
        if size < 9 and exception:
            continue
        for _ in range(40):
            lengths = [rng.randrange(1, 9) for _ in range(size)]
            lengths[0] = rng.choice((3, 4, 17, 61))
            e = rng.randrange(1, size) if exception else None
            gaps = [gap]*size if _ % 2 == 0 else [rng.randrange(gap+1) for _ in range(size)]
            adj = graph_with_exception(gaps, lengths, e)
            c = next(templates(adj), None) or next(short['separated']['remote_long'](adj), None)
            assert c, (gaps, lengths, e)
            verify(adj, c)

    assert all(counts[x] for x in ('three_consecutive_sites', 'one_bare_vertex',
                                   '2_bare_vertices', '3_bare_vertices', 'long_interval'))
    report = {'status': 'passed', 'grid_counts': dict(counts),
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    with args.output.open('x', encoding='utf-8') as output:
        output.write(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
