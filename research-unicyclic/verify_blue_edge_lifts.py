"""Replay blue edge subdivisions and their shallow-attachment applications."""

import argparse
import hashlib
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
branch = runpy.run_path(str(HERE / 'verify_branch_witnesses.py'))
bits = branch['bits']
attach = branch['attach_path']
cycle_graph = branch['family']['cycle_graph']
verify = branch['tools']['verify_certificate']

# Each row gives the cycle length, sites, guarded edge, blue set, H, slow vertex, and times.
BASES = {
    'triple_on_4': (4, (0, 1, 2), None, (0, 1, 3, 4), (1, 4), 0, 2, 3),
    'triple_on_5': (5, (0, 1, 2), None, (1, 2, 3, 5), (1, 5), 2, 3, 4),
    'triple_on_6': (6, (0, 1, 2), (4, 5), (0, 1, 2, 4, 5, 6), (1, 6), 2, 2, 3),
    'pairs_on_6': (6, (0, 1, 3, 4), None, (0, 2, 5, 6, 7), (6, 7), 2, 3, 4),
    'pairs_on_7': (7, (0, 1, 3, 4), (5, 6), (1, 2, 4, 5, 6, 8), (1, 8), 2, 3, 4),
}


def subdivide(adj, x, y, vertices):
    assert vertices >= 1 and adj[x] & (1 << y)
    adj[x] ^= 1 << y
    adj[y] ^= 1 << x
    inserted = range(len(adj), len(adj) + vertices)
    last = attach(adj, x, vertices)
    adj[last] |= 1 << y
    adj[y] |= 1 << last
    return inserted


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    time = runpy.run_path(str(branch['BASELINE']))['completion_time']
    records = {}
    for case, (n, sites, edge, blue, killing, slow, deadline, delayed) in BASES.items():
        adj = list(cycle_graph(n))
        for site in sites:
            attach(adj, site, 1)
        blue_mask, h, z = bits(blue), bits(killing), 1 << slow
        verify(time, adj, blue_mask, h, z, deadline, delayed)
        checked = 0
        if edge is not None:
            assert all(blue_mask & (1 << v) and not (h | z) & (1 << v) for v in edge)
            assert any(not adj[v] & ~blue_mask for v in edge)
            for length in (*range(1, 25), 47, 138):
                for variant in ('bare', 'leaves', 'mixed'):
                    extended = adj.copy()
                    inserted = subdivide(extended, *edge, length)
                    for i, v in enumerate(inserted):
                        if variant == 'leaves' or (variant == 'mixed' and i % 3 != 2):
                            attach(extended, v, 1)
                        if variant == 'mixed' and i % 5 == 0:
                            attach(extended, v, 3)
                    new_blue = ((1 << len(extended)) - 1) ^ ((1 << len(adj)) - 1)
                    verify(time, extended, blue_mask | new_blue, h, z, deadline, delayed)
                    checked += 1
        records[case] = dict(cycle_length=n, sites=sites, edge=edge, blue=blue,
                             killing=killing, slow=slow, restricted_deadline=deadline,
                             slow_completion_time=delayed, extensions_checked=checked)

    report = {'status': 'passed', 'certificates': records,
              'extensions_checked': sum(r['extensions_checked'] for r in records.values()),
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    with args.output.open('x', encoding='utf-8') as output:
        output.write(json.dumps(report, indent=2) + '\n')
    print(f"Passed {len(records)} core certificates and {report['extensions_checked']} extensions.")


if __name__ == '__main__':
    main()
