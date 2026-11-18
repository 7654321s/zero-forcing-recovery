"""Independently check EveryMinimumSupport on small unlabelled trees.

Uses only the Python standard library. Positive instances enumerate every forcing
colouring, every minimum killing set, and all relevant budgets. A negative instance
stops at its first explicit counterexample. This is finite evidence, not a proof
for arbitrary trees.
"""
from pathlib import Path
import argparse, hashlib, json


def subsets(mask):
    part = mask
    while True:
        yield part
        if not part:
            return
        part = (part - 1) & mask


def completion_time(adj, blue):
    full = (1 << len(adj)) - 1
    rounds = 0
    while blue != full:
        added = 0
        sources = blue
        while sources:
            bit = sources & -sources
            sources ^= bit
            white = adj[bit.bit_length()-1] & ~blue
            if white and white & (white-1) == 0:
                added |= white
        if not added:
            return len(adj) + 1  # Infinity: any successful run takes at most n rounds.
        blue |= added
        rounds += 1
    return rounds


def canonical_tree_code(adj):
    def rooted(v, parent):
        return '(' + ''.join(sorted(rooted(w, v) for w in range(len(adj))
                                    if w != parent and adj[v] >> w & 1)) + ')'
    return min(rooted(v, -1) for v in range(len(adj)))


def tree_families(maximum):
    family = {'()': (0,)}
    for n in range(1, maximum+1):
        yield n, tuple(family.values())
        extended = {}
        for adj in family.values():
            for v in range(n):
                new = list(adj) + [1 << v]
                new[v] |= 1 << n
                extended[canonical_tree_code(new)] = tuple(new)
        family = extended


def in_candidate_class(adj):
    degrees = [mask.bit_count() for mask in adj]
    if all(d <= 2 for d in degrees):
        return True
    if len(adj)-1 in degrees:
        return True
    internal = [i for i, d in enumerate(degrees) if d > 1]
    return len(internal) == 2 and all(degrees[v] >= 3 for v in internal) and bool(
        adj[internal[0]] >> internal[1] & 1)


def every_minimum_support(adj):
    n = len(adj)
    infinity = n+1
    times = [completion_time(adj, B) for B in range(1 << n)]
    checked_B = checked_H = 0
    for B, initial in enumerate(times):
        if initial == infinity:
            continue
        checked_B += 1
        losses = list(subsets(B))
        killing_size = min(D.bit_count() for D in losses if times[B ^ D] == infinity)
        killing_sets = [D for D in losses if D.bit_count() == killing_size and times[B ^ D] == infinity]
        full = [0] * killing_size
        for D in losses:
            size = D.bit_count()
            if size < killing_size:
                full[size] = max(full[size], times[B ^ D])
        for k in range(1, killing_size):
            full[k] = max(full[k], full[k-1])
        for H in killing_sets:
            checked_H += 1
            restricted = [0] * killing_size
            for D in subsets(H):
                size = D.bit_count()
                if size < killing_size:
                    restricted[size] = max(restricted[size], times[B ^ D])
            for k in range(1, killing_size):
                restricted[k] = max(restricted[k], restricted[k-1])
            for k in range(killing_size):
                if restricted[k] != full[k]:
                    return False, dict(blue=B, minimum_killing=H, minimum_killing_size=killing_size,
                        budget=k, restricted_time=restricted[k], global_time=full[k]), checked_B, checked_H
    return True, None, checked_B, checked_H


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-vertices', type=int, default=9)
    parser.add_argument('--output', type=Path, default=Path('build/classification-small-trees.json'))
    args = parser.parse_args()
    if not 1 <= args.max_vertices <= 11:
        parser.error('--max-vertices must be between 1 and 11')
    rows = []
    for n, family in tree_families(args.max_vertices):
        for adj in family:
            actual, witness, checked_B, checked_H = every_minimum_support(adj)
            expected = in_candidate_class(adj)
            if actual != expected:
                raise AssertionError(dict(adj=adj, expected=expected, actual=actual, witness=witness))
            rows.append(dict(vertices=n, adjacency_bitmasks=adj, property=actual,
                forcing_colourings_checked=checked_B, minimum_killing_sets_checked=checked_H,
                counterexample=witness))
        print(f'n={n}: {len(family)} trees checked', flush=True)
    result = dict(status='finite_classification_checks_passed', max_vertices=args.max_vertices,
        trees=len(rows), positive=sum(r['property'] for r in rows),
        forcing_colourings_checked=sum(r['forcing_colourings_checked'] for r in rows),
        minimum_killing_sets_checked=sum(r['minimum_killing_sets_checked'] for r in rows),
        script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        infinity_encoding='n+1; every finite successful propagation uses at most n rounds',
        budget_reduction='For k at least the minimum killing size, both worst times are infinite.',
        enumeration='Extend every preceding tree by one leaf; deduplicate by minimum rooted parenthesis code.',
        full_arbitrary_tree_proof=False, results=rows)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({k: v for k, v in result.items() if k != 'results'}), flush=True)


if __name__ == '__main__':
    main()
