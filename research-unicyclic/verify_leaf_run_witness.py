"""Replay a constant-size certificate on six consecutive attachment sites."""

import argparse
import hashlib
from itertools import product
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
branch = runpy.run_path(str(HERE / 'verify_branch_witnesses.py'))
attach = branch['attach_path']
cycle_graph = branch['family']['cycle_graph']
bits = branch['bits']
verify = branch['tools']['verify_certificate']

SHORT_CORONAS = {
    4: ((0, 2, 3, 4, 5), (4, 5), 2, 2, 3),
    5: ((0, 2, 3, 4, 5, 7), (0, 5), 3, 2, 3),
    6: ((3, 4, 5, 6, 7, 9), (3, 9), 4, 3, 4),
}


def long_witness(adj, a_leaf, d_leaf, b_leaf, w_leaf):
    # Labels 0 through 6 denote a,d,b,t,w,y,x in cycle order.
    white = bits((1, 4, 5, d_leaf, w_leaf))
    return ((1 << len(adj)) - 1) ^ white, bits((a_leaf, b_leaf)), 1 << 3, 2, 3


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    time = runpy.run_path(str(branch['BASELINE']))['completion_time']
    cases = []
    for n, (blue, killing, slow, deadline, delayed) in SHORT_CORONAS.items():
        adj = list(cycle_graph(n))
        for v in range(n):
            attach(adj, v, 1)
        verify(time, adj, bits(blue), bits(killing), 1 << slow, deadline, delayed)
        cases.append(dict(cycle_length=n, blue=blue, killing=killing, slow=slow,
                          restricted_deadline=deadline, slow_completion_time=delayed))

    checked = 0
    for n, t_length, y_length, extras in product((*range(7, 26), 37, 64, 147), (1, 2, 4),
                                                 (1, 3), ('none', 'all_leaves', 'deep')):
        adj = list(cycle_graph(n))
        if extras == 'all_leaves' and (t_length, y_length) != (1, 1):
            continue
        a_leaf = attach(adj, 0, 1)
        d_leaf = attach(adj, 1, 1)
        b_leaf = attach(adj, 2, 1)
        attach(adj, 3, t_length)
        w_leaf = attach(adj, 4, 1)
        attach(adj, 5, y_length)
        if extras == 'all_leaves':
            for v in range(6, n):
                attach(adj, v, 1)
        elif extras == 'deep':
            for v in (0, 2, 3, 5, 6, n-1):
                attach(adj, v, 2)
        verify(time, adj, *long_witness(adj, a_leaf, d_leaf, b_leaf, w_leaf))
        checked += 1

    report = {'status': 'passed', 'short_corona_certificates': cases, 'grid_checked': checked,
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    with args.output.open('x', encoding='utf-8') as output:
        output.write(json.dumps(report, indent=2) + '\n')
    print(f'Passed {len(cases)} exact short coronas and {checked} parameter instances.')


if __name__ == '__main__':
    main()
