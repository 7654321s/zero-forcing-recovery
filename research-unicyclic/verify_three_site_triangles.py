"""Replay the classification of triangular cores with all three sites occupied."""

import argparse
from collections import Counter
import hashlib
from itertools import product
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
stem = runpy.run_path(str(HERE / 'verify_short_fork_stems.py'))
triangle = stem['triangle']
branch = stem['branch']
pair = stem['pair']
tools = stem['tools']
bits = stem['bits']
attach = stem['attach']
record = stem['record']


def rooted_vertices(children, root):
    pending = [root]
    while pending:
        v = pending.pop()
        yield v
        pending.extend(children[v])


def candidates(adj):
    cycle = branch['cycle_vertices'](adj)
    if len(cycle) != 3:
        return
    parent, children = branch['tree_structure'](adj, cycle)
    if not all(children[v] for v in cycle):
        return
    pure = {v: arms[0] for v in cycle
            if (arms := branch['pendant_paths'](v, children)) is not None and len(arms) == 1}
    if len(pure) != 2:
        return
    a = next(iter(cycle - pure.keys()))
    b, c = sorted(pure, key=lambda v: (-len(pure[v]), v))
    m = len(pure[b])
    full = (1 << len(adj)) - 1

    for u in rooted_vertices(children, a):
        local = sorted(pair['path_arms'](children, u), key=len)
        for arm in local:
            bound = 1 + (m+1)//2
            if len(arm) <= bound:
                continue
            whites = bits(arm[1:])
            for remote in pure.values():
                whites |= bits(remote) ^ bits(remote[:-1:2])
            yield record('long_arm_against_ring_pair', list(branch['neighbors'](whites)), full,
                         (b, c), u, max(bound, len(arm)-1), len(arm))
        if len(local) < 2:
            continue
        short, long = local[:2]
        if len(long) <= 2*m - 1:
            white = list(pure[b])
            for arm in (short, long):
                kept = set(arm[:1] + arm[1:-1:2])
                white.extend(v for v in arm if v not in kept)
            yield record('small_fork_against_path', white, full,
                         (short[0], long[0]), a, m, m+1)
        if m != 1 or len(long) != 2:
            continue
        if u == a:
            if len(short) == 1 and sum(len(x) == 1 for x in local) == 1:
                yield record('two_white_cycle_leaves', [long[0], pure[b][0], pure[c][0]], full,
                             (short[0], long[-1]), b, 2, 3)
            if len(short) == 2:
                yield record('one_blue_cycle_leaf', [a, *long, pure[c][0]], full,
                             (b, pure[b][0]), c, 3, 4)
            continue
        if len(children[u]) != 2 or len(short) != 1:
            continue
        spine = [u]
        tips = []
        while spine[-1] != a:
            low = spine[-1]
            high = parent[low]
            sides = [v for v in children[high] if v != low]
            if not all(len(children[v]) == 1 and not children[children[v][0]] for v in sides):
                break
            tips.extend(children[v][0] for v in sides)
            spine.append(high)
        if spine[-1] == a:
            distance = len(spine) - 1
            yield record('stem_with_third_site_blue', spine + tips + [pure[b][0], long[-1]],
                         full, (short[0], long[0]), b, distance+2, distance+3)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    data = (HERE / 'unicyclic-through-11.json').read_bytes()
    time = runpy.run_path(str(branch['BASELINE']))['completion_time']
    counts = Counter()
    records = []
    audited = 0
    older = ('branch-witness', 'two-pendant-centers', 'compressed-pendant-pair',
             'two-site-exhaustion')
    prior = {r['graph_index'] for name in older
             for r in json.loads((HERE / f'{name}-replay.json').read_bytes())['census_certificates']}

    def verify(adj, cert):
        actual = time(adj, cert['blue'] ^ cert['slow'])
        assert actual < len(adj)+1
        tools['verify_certificate'](time, adj, cert['blue'], cert['killing'], cert['slow'],
                                    cert['restricted_deadline'], actual)
        assert actual == cert['slow_completion_time']

    for index, g in enumerate(json.loads(data)['graphs']):
        if g['cycle_length'] != 3:
            continue
        adj = tools['adjacency'](g['order'], g['edges'])
        cycle = branch['cycle_vertices'](adj)
        _, children = branch['tree_structure'](adj, cycle)
        if not all(children[v] for v in cycle):
            continue
        matches = list(candidates(adj)) + list(stem['candidates'](adj))
        for cert in matches:
            assert not g['every_minimum_support'], index
            verify(adj, cert)
            records.append({'graph_index': index, **cert})
        if not g['every_minimum_support'] and not branch['twins'](adj):
            if any(len(ch) > 1 for ch in children.values()):
                assert matches or index in prior, index
        audited += 1

    for depth, (small, long), sides, (b, c) in product(
            (0, 1, 3, 13, 61), ((1, 2), (2, 2), (1, 3), (2, 4), (1, 13)),
            (False, True), ((1, 1), (1, 2), (2, 2), (2, 5), (4, 9))):
        adj = list(branch['family']['cycle_graph'](3))
        u = attach(adj, 0, depth)
        attach(adj, u, small)
        attach(adj, u, long)
        attach(adj, 1, b)
        attach(adj, 2, c)
        if sides:
            for side in [0, *range(3, 3+depth-1)] if depth else [0]:
                attach(adj, side, 2)
        matches = list(candidates(adj))
        assert matches or (depth and (small, long, b, c) == (2, 2, 1, 1))
        for cert in matches:
            verify(adj, cert)
            counts[cert['case']] += 1

    report = {'status': 'passed', 'census_checked': len(records), 'three_site_triangles': audited,
              'grid_counts': dict(counts), 'census_sha256': hashlib.sha256(data).hexdigest(),
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'census_certificates': records}
    with args.output.open('x', encoding='utf-8') as output:
        output.write(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'census_certificates'}, indent=2))


if __name__ == '__main__':
    main()
