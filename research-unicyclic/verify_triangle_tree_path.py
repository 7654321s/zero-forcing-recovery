"""Replay further two-attachment certificates on triangular cores."""

import argparse
from collections import Counter
import hashlib
from itertools import product
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
pair = runpy.run_path(str(HERE / 'verify_two_pendant_centers.py'))
branch = pair['branch']
tools = branch['tools']
bits = branch['bits']
attach = branch['attach_path']
cycle_graph = branch['family']['cycle_graph']


def record(case, blue, killing, slow, early, late):
    return dict(case=case, blue=blue, killing=bits(killing), slow=1 << slow,
                restricted_deadline=early, slow_completion_time=late)


def triangle_certificates(adj):
    cycle = branch['cycle_vertices'](adj)
    if len(cycle) != 3:
        return
    parent, children = branch['tree_structure'](adj, cycle)
    bare = [v for v in cycle if not children[v]]
    if len(bare) != 1:
        return
    c = bare[0]
    full = (1 << len(adj)) - 1
    for b in sorted(cycle - {c}):
        remote = branch['pendant_paths'](b, children)
        if remote is None or len(remote) != 1:
            continue
        path = remote[0]
        a = next(iter(cycle - {b, c}))
        todo = [a]
        while todo:
            u = todo.pop()
            todo.extend(children[u])
            arms = sorted(pair['path_arms'](children, u), key=len)
            for arm in arms:
                if len(arm) >= len(path) + 2:
                    blue = full ^ bits(path + arm[1:])
                    yield record('longer_branch', blue, (b, c), u,
                                 max(len(path)+1, len(arm)-1), len(arm))
            if len(arms) < 2:
                continue
            short, long = arms[:2]
            if len(long) <= 2*len(path) - 1:
                white = bits(path)
                for arm in (short, long):
                    white |= bits(arm) ^ bits(arm[:1] + arm[1:-1:2])
                yield record('root_loss', full ^ white, (short[0], long[0]), a,
                             len(path), len(path)+1)
            if len(path) != 1 or len(long) != 2:
                continue
            if u == a:
                if len(short) == 1 and sum(len(x) == 1 for x in arms) == 1:
                    blue = full ^ bits((long[0], path[0]))
                    yield record('cycle_fork_short_long', blue, (short[0], long[-1]), c, 2, 3)
                elif len(short) == 2:
                    blue = full ^ bits([b, *long])
                    yield record('cycle_fork_equal', blue, short, c, 3, 4)
                continue
            if len(children[u]) != 2 or len(short) != 1:
                continue
            stem = [u]
            shorter_sides = []
            while stem[-1] != a:
                child = stem[-1]
                preceding = parent[child]
                for side in children[preceding]:
                    if side == child:
                        continue
                    if len(children[side]) == 1 and not children[children[side][0]]:
                        shorter_sides.append(children[side][0])
                    else:
                        break
                else:
                    stem.append(preceding)
                    continue
                break
            if stem[-1] != a:
                continue
            depth = len(stem) - 1
            blue = full ^ bits(stem + shorter_sides + [path[0], long[-1]])
            yield record('stem_without_side_leaves', blue, (short[0], long[0]), b,
                         depth+2, depth+3)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    data = (HERE / 'unicyclic-through-11.json').read_bytes()
    time = runpy.run_path(str(branch['BASELINE']))['completion_time']
    counts = Counter()
    records = []

    def verify(adj, cert):
        tools['verify_certificate'](time, adj, cert['blue'], cert['killing'], cert['slow'],
                                    cert['restricted_deadline'], cert['slow_completion_time'])

    for index, g in enumerate(json.loads(data)['graphs']):
        adj = tools['adjacency'](g['order'], g['edges'])
        for cert in triangle_certificates(adj):
            assert not g['every_minimum_support'], index
            verify(adj, cert)
            records.append({'graph_index': index, **cert})

    for depth, small, long, remote, side in product((0, 1, 2, 5, 13, 97), (1, 2, 3),
                                                    (2, 3, 4, 9, 17), (1, 2, 3, 5, 17),
                                                    (False, True)):
        if small > long:
            continue
        adj = list(cycle_graph(3))
        u = attach(adj, 0, depth)
        attach(adj, u, small)
        attach(adj, u, long)
        attach(adj, 1, remote)
        if side:
            for v in [0, *range(3, 3+depth-1)] if depth else [0]:
                attach(adj, v, 2)
        matches = list(triangle_certificates(adj))
        if remote >= 2 or long >= 3 or (remote == 1 and long == 2 and (not depth or small == 1)):
            assert matches, (depth, small, long, remote, side)
        for cert in matches:
            verify(adj, cert)
            counts[cert['case']] += 1

    report = {'status': 'passed', 'census_certificates': records,
              'census_checked': len(records), 'grid_counts': dict(counts),
              'census_sha256': hashlib.sha256(data).hexdigest(),
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    with args.output.open('x', encoding='utf-8') as output:
        output.write(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'census_certificates'}, indent=2))


if __name__ == '__main__':
    main()
