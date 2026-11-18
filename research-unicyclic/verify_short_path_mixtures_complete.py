"""Verify the bounded gap reduction for all mixtures of paths of lengths one and two."""

import argparse
from collections import Counter
from functools import lru_cache
import hashlib
from itertools import combinations, product
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
mixtures = runpy.run_path(str(HERE / 'verify_short_path_mixtures.py'))
uniform = mixtures['length_two']
branch = mixtures['branch']
tools = mixtures['tools']
bits = mixtures['bits']
neighbors = branch['neighbors']


def stabilizer(gaps):
    n = len(gaps)
    for k, direction in product(range(n), (1, -1)):
        vertices = tuple((k + direction*i) % n for i in range(n))
        edges = vertices if direction == 1 else tuple((v-1) % n for v in vertices)
        if gaps == tuple(gaps[i] for i in edges):
            yield vertices


def arc_forts(adj):
    cycle = branch['cycle_vertices'](adj)
    _, children = branch['tree_structure'](adj, cycle)
    paths = mixtures['dense']['paths_at'](children, cycle)
    forts = set()
    for p, left in paths.items():
        order = tools['cycle_order'](adj, cycle, p)
        for ring in (order, order[:1] + order[:0:-1]):
            white = bits(left)
            for i, v in enumerate(ring[1:], 1):
                white |= bits(paths.get(v, ()))
                if i > 1 and v in paths:
                    forts.add(white)
                white |= 1 << v
    return sorted(forts, key=lambda w: (w.bit_count(), w))


def finite_certificate(adj, completion_time):
    infinity = len(adj)+1
    full = (1 << len(adj))-1

    @lru_cache(maxsize=None)
    def time(blue):
        return completion_time(adj, blue)

    for fort in arc_forts(adj):
        assert all((adj[v] & fort).bit_count() != 1 for v in neighbors(full ^ fort))
        for vertex in neighbors(full ^ fort):
            outside = full ^ (fort | (1 << vertex))
            for u, v in combinations(neighbors(fort), 2):
                killing = bits((u, v))
                blue = outside | killing
                early = max(time(blue ^ (1 << u)), time(blue ^ (1 << v)))
                if early >= infinity:
                    continue
                singles = [(time(blue ^ (1 << z)), z) for z in neighbors(blue)]
                late, slow = max(singles)
                if early < late < infinity:
                    return dict(blue=blue, killing=killing, slow=1 << slow,
                                restricted_deadline=early, slow_completion_time=late)
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    time = runpy.run_path(str(branch['BASELINE']))['completion_time']
    totals = {}
    fallback = []

    for sites in range(3, 9):
        counts = Counter()
        for gaps in product(range(4), repeat=sites):
            if gaps != uniform['canonical'](gaps) or sites+sum(gaps) < 5:
                continue
            actions = tuple(stabilizer(gaps))
            for lengths in product((1, 2), repeat=sites):
                if min(lengths) == max(lengths):
                    continue
                if any(tuple(lengths[i] for i in move) < lengths for move in actions[1:]):
                    continue
                adj = mixtures['ring_from_word'](gaps, lengths)
                cert = uniform['formula'](adj) or next(mixtures['candidates'](adj), None)
                if cert is not None:
                    # These are instances of the general interval lemmas.
                    counts[cert['case']] += 1
                    continue
                cert = finite_certificate(adj, time)
                assert cert is not None, (gaps, lengths)
                tools['verify_certificate'](time, adj, cert['blue'], cert['killing'], cert['slow'],
                                            cert['restricted_deadline'], cert['slow_completion_time'])
                fallback.append(dict(gaps=gaps, lengths=lengths, **cert))
                counts['finite_certificate'] += 1
        totals[sites] = dict(counts)
        print(json.dumps({'sites': sites, 'checked': sum(counts.values()),
                          'finite_certificates': counts['finite_certificate']}), flush=True)

    report = {'status': 'passed', 'counts_by_sites': totals,
              'finite_certificates': fallback,
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    with args.output.open('x', encoding='utf-8') as output:
        output.write(json.dumps(report, indent=2) + '\n')


if __name__ == '__main__':
    main()
