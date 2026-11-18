"""Replay certificates for two attachment sites with a white path at one site."""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
tools = runpy.run_path(str(HERE / 'verify_site_witnesses.py'))
neighbors = tools['neighbors']
bits = tools['bits']
BASELINE = tools['BASELINE']
family = tools['family']


def attachment_vertices(adj, cycle, root):
    vertices = set()
    pending = [v for v in neighbors(adj[root]) if v not in cycle]
    while pending:
        v = pending.pop()
        if v not in vertices:
            vertices.add(v)
            pending.extend(w for w in neighbors(adj[v]) if w not in cycle and w not in vertices)
    return vertices


def is_single_path(adj, cycle, root, outside):
    return (sum(v not in cycle for v in neighbors(adj[root])) == 1
            and all(adj[v].bit_count() <= 2 for v in outside))


def robust_feed(adj, cycle, root):
    children = [v for v in neighbors(adj[root]) if v not in cycle]
    if len(children) >= 2:
        return all(adj[v].bit_count() > 1 for v in children)
    if len(children) != 1 or adj[children[0]].bit_count() <= 1:
        return False
    child = children[0]
    return all(adj[v].bit_count() > 1 for v in neighbors(adj[child]) if v != root)


def certificate(adj, cycle, root, path_site, blue_tree, path_size):
    ring = tools['cycle_order'](adj, cycle, root)
    n = len(ring)
    if ring.index(path_site) > n // 2:
        ring = ring[:1] + ring[1:][::-1]
    d = ring.index(path_site)
    length = path_size
    if d == 1:
        case, blue, killing, slow = 'adjacent', (1, 2, 3), (1, 3), 2
        fast, late = max(1 + length, (n - 1)//2), n - 2 + length
    elif n == 2*d:
        case, blue, killing, slow = 'opposite', (0, 1, n-1), (1, n-1), 0
        fast, late = d - 1 + length, d + length
    elif d == 2:
        case, blue, killing, slow = 'distance_two', (1, 2, 3), (1, 2), 3
        fast, late = n - 3 + length, n - 2 + length
    elif n == 2*d+1:
        case, blue, killing, slow = 'odd_nearly_opposite', (0, 1, n-1, n-3), (1, n-1), 0
        fast, late = d - 1 + length, d + length
    else:
        if not robust_feed(adj, cycle, root):
            return None
        ring = ring[:1] + ring[1:][::-1]
        distance = n - d
        case, blue, killing, slow = 'unequal_arcs', (1, 2, 3), (1, 3), 2
        if distance == d + 2:
            fast, late = d + length, d + 1 + length
        else:
            if distance == d + 3:
                blue = (*blue, n-2)
            fast, late = distance - 3 + length, distance - 2 + length
    return {'case': case, 'blue': bits(blue_tree) | bits(ring[i] for i in blue),
            'killing': bits(ring[i] for i in killing), 'slow': 1 << ring[slow],
            'restricted_deadline': fast, 'slow_completion_time': late}


def witness(adj, cycle, sites):
    a, b = sorted(sites)
    outside = {v: attachment_vertices(adj, cycle, v) for v in sites}
    for root, path_site in ((a, b), (b, a)):
        if is_single_path(adj, cycle, path_site, outside[path_site]):
            result = certificate(adj, cycle, root, path_site, outside[root], len(outside[path_site]))
            if result is not None:
                return result
    return None


def add_path(adj, root, length):
    v = root
    for _ in range(length):
        family['add_leaves'](adj, v, 1)
        v = len(adj) - 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    data = (HERE / 'unicyclic-through-11.json').read_bytes()
    graphs = json.loads(data)['graphs']
    time = runpy.run_path(str(BASELINE))['completion_time']
    records = []
    counts = Counter()

    def check(adj, cert):
        assert cert['killing'].bit_count() == 2 and cert['slow'].bit_count() == 1
        tools['verify_certificate'](time, adj, cert['blue'], cert['killing'], cert['slow'],
                                    cert['restricted_deadline'], cert['slow_completion_time'])

    for index, g in enumerate(graphs):
        adj = tools['adjacency'](g['order'], g['edges'])
        cycle = tools['cycle_vertices'](adj)
        if len(cycle) < 4:
            continue
        sites = {v for v in cycle if any(w not in cycle for w in neighbors(adj[v]))}
        if len(sites) != 2:
            continue
        cert = witness(adj, cycle, sites)
        if cert is not None:
            assert not g['every_minimum_support']
            check(adj, cert)
            records.append({'graph_index': index, **cert})

    for n in range(4, 41):
        cycle = set(range(n))
        bare = family['cycle_graph'](n)
        for d in range(1, n//2 + 1):
            for left in range(1, 7):
                for right in range(1, 7):
                    adj = list(bare)
                    add_path(adj, 0, left)
                    add_path(adj, d, right)
                    cert = witness(adj, cycle, {0, d})
                    if cert is not None:
                        check(adj, cert)
                        counts['two_paths'] += 1
                    else:
                        assert left <= 2 and right <= 2 and d >= 2 and n >= 2*d + 2
            for length in range(1, 5):
                adj = list(bare)
                add_path(adj, 0, 2)
                add_path(adj, 0, 3)
                add_path(adj, d, length)
                cert = witness(adj, cycle, {0, d})
                assert cert is not None
                check(adj, cert)
                counts['branch_and_path'] += 1

    report = {'status': 'passed', 'census_certificates': records,
              'census_checked': len(records), 'grid_counts': dict(counts),
              'census_sha256': hashlib.sha256(data).hexdigest(),
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    with args.output.open('x', encoding='utf-8') as output:
        output.write(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'census_certificates'}, indent=2))


if __name__ == '__main__':
    main()
