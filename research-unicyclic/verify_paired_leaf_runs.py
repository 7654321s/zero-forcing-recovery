"""Replay the variable-gap formula for two separated pairs of leaf sites."""

import argparse
from itertools import product
import hashlib
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
edge = runpy.run_path(str(HERE / 'verify_blue_edge_lifts.py'))
branch = edge['branch']
attach = branch['attach_path']
cycle_graph = branch['family']['cycle_graph']
bits = branch['bits']


def formula(adj, gap, a_leaf):
    # Sites are 0, 1, gap+2, gap+3 in cycle order.
    n = gap + 6
    assert gap >= 2 and len(adj) == n + 4
    return bits((0, 2, 3, 4, n-2, n-1, a_leaf)), bits((2, 4)), 1 << 3, gap, gap+1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    time = runpy.run_path(str(branch['BASELINE']))['completion_time']
    verify = edge['verify']
    checked = 0
    for gap, exterior in product((*range(2, 36), 63, 100, 147), (0, 1, 2, 5, 17)):
        n = gap + 6
        adj = list(cycle_graph(n))
        for site in (0, 1, gap+2, gap+3):
            attach(adj, site, 1)
        blue, h, z, deadline, delayed = formula(adj, gap, n)
        old_order = len(adj)
        assert blue & bits((n-2, n-1)) == bits((n-2, n-1))
        assert not (h | z) & bits((n-2, n-1))
        assert not adj[n-1] & ~blue
        if exterior:
            stops = edge['subdivide'](adj, n-2, n-1, exterior)
            for i, v in enumerate(stops):
                if i % 3 != 2:
                    attach(adj, v, 1)
                if i % 4 == 1:
                    attach(adj, v, 2)
        blue |= ((1 << len(adj)) - 1) ^ ((1 << old_order) - 1)
        verify(time, adj, blue, h, z, deadline, delayed)
        checked += 1

    report = {'status': 'passed', 'grid_checked': checked,
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    with args.output.open('x', encoding='utf-8') as output:
        output.write(json.dumps(report, indent=2) + '\n')
    print(f'Passed {checked} variable-gap and exterior instances.')


if __name__ == '__main__':
    main()
