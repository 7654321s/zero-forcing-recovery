"""Replay the finite gap reduction for uniform length-two attachments."""

import argparse
from collections import Counter
import hashlib
from itertools import product
import json
from pathlib import Path
import random
import runpy


HERE = Path(__file__).resolve().parent
separated = runpy.run_path(str(HERE / 'verify_separated_delay_intervals.py'))
dense = separated['dense']
branch = separated['branch']
tools = separated['tools']
bits = separated['bits']
with_paths = separated['with_paths']

# Start at site 0. Number the cycle clockwise; add the two-vertex paths by site order.
RESIDUAL = {
    (0, 2, 2): ((0, 3, 5, 6, 10), (3, 10), 6, 6, 7),
    (0, 2, 3): ((0, 3, 4, 5, 7, 12), (3, 12), 4, 5, 6),
    (0, 3, 3): ((0, 4, 5, 6, 8, 13), (4, 13), 5, 6, 7),
    (2, 2, 2): ((0, 1, 2, 3, 5, 6, 7, 8, 13, 14), (1, 2), 5, 3, 4),
    (2, 2, 3): ((0, 1, 2, 3, 5, 6, 7, 8, 9, 14, 15), (1, 2), 5, 3, 4),
    (2, 3, 3): ((0, 1, 2, 3, 5, 6, 7, 8, 9, 10, 15, 16), (1, 2), 5, 3, 4),
    (3, 3, 3): ((0, 1, 4, 5, 6, 7, 8, 9, 11, 12, 16, 17), (1, 12), 0, 5, 6),
    (0, 1, 0, 1): ((0, 2, 4, 5, 9, 12, 13), (2, 9), 5, 5, 6),
    (0, 1, 0, 2): ((0, 2, 3, 4, 6, 11, 13, 14), (2, 11), 3, 4, 5),
    (0, 1, 0, 3): ((0, 2, 3, 4, 6, 7, 12, 14, 15), (2, 12), 3, 4, 5),
    (0, 2, 0, 2): ((0, 3, 4, 5, 7, 12, 14, 15), (3, 12), 4, 5, 6),
    (0, 2, 0, 3): ((0, 3, 4, 5, 7, 8, 13, 15, 16), (3, 13), 4, 5, 6),
    (0, 2, 2, 2): ((0, 3, 4, 5, 7, 8, 9, 14, 16, 17), (3, 14), 4, 5, 6),
    (0, 2, 3, 2): ((0, 3, 4, 5, 7, 8, 9, 10, 15, 17, 18), (3, 15), 4, 5, 6),
    (0, 3, 0, 3): ((0, 4, 5, 6, 8, 9, 14, 16, 17), (4, 14), 5, 6, 7),
    (0, 1, 0, 2, 2): ((0, 2, 3, 4, 6, 7, 8, 9, 14, 16, 17, 18, 19), (2, 14), 3, 4, 5),
    (0, 1, 0, 1, 0, 1): ((0, 2, 3, 4, 6, 7, 8, 13, 15, 16, 17, 18, 19, 20), (2, 13), 3, 4, 5),
}


def canonical(word):
    return min(w[k:] + w[:k] for w in (word, word[::-1]) for k in range(len(w)))


def formula(adj):
    return (next(dense['staggered_candidates'](adj), None)
            or next(separated['candidates'](adj), None)
            or next(separated['remote_long'](adj), None)
            or dense['dense_long_candidate'](adj))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    time = runpy.run_path(str(branch['BASELINE']))['completion_time']
    counts = Counter()
    extra = Counter()
    table = {}

    def verify(adj, cert):
        delayed = cert['slow_completion_time']
        if delayed is None:
            delayed = time(adj, cert['blue'] ^ cert['slow'])
        tools['verify_certificate'](time, adj, cert['blue'], cert['killing'], cert['slow'],
                                    cert['restricted_deadline'], delayed)

    for count in range(3, 9):
        for word in product(range(4), repeat=count):
            if word != canonical(word):
                continue
            n = count + sum(word)
            if n < 5:
                continue
            sites = [0]
            for gap in word[:-1]:
                sites.append(sites[-1]+gap+1)
            adj = with_paths(n, {v: [2] for v in sites})
            cert = formula(adj)
            if cert is None:
                blue, H, z, early, late = RESIDUAL[word]
                cert = dict(case='fixed_gap_word', blue=bits(blue), killing=bits(H), slow=1 << z,
                            restricted_deadline=early, slow_completion_time=late)
                table[word] = cert
            verify(adj, cert)
            counts[cert['case']] += 1
    assert set(table) == set(RESIDUAL)

    rng = random.Random(94231)
    for count, excess, pattern in product((9, 10, 13), (0, 1, 7, 23), range(12)):
        n = count + excess
        sites = sorted(rng.sample(range(n), count))
        lengths = {v: [rng.randrange(2, 19)] for v in sites}
        if pattern == 0:
            lengths[sites[0]] = [71]
        adj = with_paths(n, lengths)
        cert = formula(adj)
        assert cert, (n, sites, lengths)
        verify(adj, cert)
        extra[cert['case']] += 1

    report = {'status': 'passed', 'gap_replays': dict(counts),
              'many_nonleaf_site_replays': dict(extra),
              'fixed_certificates': [{'gaps': w, **c} for w, c in table.items()],
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    with args.output.open('x', encoding='utf-8') as output:
        output.write(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: v for k, v in report.items() if k != 'fixed_certificates'}, indent=2))


if __name__ == '__main__':
    main()
