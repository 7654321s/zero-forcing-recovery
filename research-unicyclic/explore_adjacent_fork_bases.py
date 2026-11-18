"""Search bounded fork and ring bases with certified terminal extensions."""

import argparse
from functools import lru_cache
from itertools import combinations, product
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
padding = runpy.run_path(str(HERE / "verify_path_padding_reduction.py"))
branch = padding["branch"]
attach = padding["attach"]
bits = padding["bits"]
neighbors = padding["neighbors"]


def base_graph(left, right, depth, lengths):
    order = left + right + 3
    b, c = left + 1, left + 2
    adj = list(branch["family"]["cycle_graph"](order))

    def path(root, length):
        start = len(adj)
        attach(adj, root, length)
        return tuple(range(start, len(adj)))

    stem = path(0, depth)
    u = stem[-1] if stem else 0
    short, long = path(u, 1), path(u, lengths[0])
    arms = (long, path(b, lengths[1]), path(c, lengths[2]))
    anchors = (0, *stem[:-1]) if depth else ()
    sides = {0: (stem + short + long,) if stem else (short, long),
             b: (arms[1],), c: (arms[2],)}
    forts = {bits(short + long)}
    for start in sides:
        for direction in (-1, 1):
            inside = 0
            for distance in range(1, order):
                end = (start + distance * direction) % order
                if distance >= 2 and end in sides:
                    for first, last in product(sides[start], sides[end]):
                        forts.add(bits(first + last) | inside)
                inside |= (1 << end) | bits(v for path in sides.get(end, ()) for v in path)
            forts.add(inside)
    return adj, arms, anchors, sorted(forts, key=lambda x: (x.bit_count(), x))


def search(left, right, depth, lengths, limit, grow_arm=True):
    adj, arms, anchors, forts = base_graph(left, right, depth, lengths)
    ends = {i: path[-1] for i, path in enumerate(arms)
            if (i == 0 and grow_arm) or (i != 0 and len(path) > 1)}
    full = (1 << len(adj)) - 1
    infinity = len(adj) + 1
    stem_edges = tuple(bits((v, v + 1)) for v in anchors[1:]) if depth >= 4 else ()

    @lru_cache(maxsize=80000)
    def timing(blue):
        return padding["trace"](adj, blue)

    for extra in range(limit + 1):
        for fort in forts:
            for first, second in combinations(neighbors(fort), 2):
                h1, h2 = 1 << first, 1 << second
                active_edges = tuple(e for e in stem_edges if not e & (h1 | h2))
                for removed in combinations(neighbors(full ^ fort), extra):
                    blue = full ^ fort ^ bits(removed) | h1 | h2
                    edges = tuple(e for e in active_edges if e & blue == e)
                    if depth >= 4 and not edges:
                        continue
                    restricted = tuple(timing(x) for x in (blue, blue ^ h1, blue ^ h2))
                    early = max(t for t, _ in restricted)
                    if early >= infinity:
                        continue
                    double = timing(blue ^ h1 ^ h2)
                    common = (*restricted, double)
                    if double[0] != infinity:
                        continue
                    dormant = {v for v in anchors
                               if any(row[v] not in (0, 1) for _, row in common)}
                    if any(not padding["lift"]["forces_except"](adj, blue, v)
                           for v in dormant):
                        continue
                    neutral = {i for i, v in ends.items()
                               if all(row[v] in (0, 1) for _, row in common)
                               and (not blue & (1 << v) or adj[v] & blue
                                    or padding["lift"]["forces_except"](adj, blue, v))}
                    if any(i not in neutral and blue & (1 << v) for i, v in ends.items()):
                        continue
                    singles = [(v, *timing(blue ^ (1 << v))) for v in neighbors(blue)]
                    if any(t == infinity for _, t, _ in singles):
                        continue
                    for slow, late, arrival in sorted(singles, key=lambda item: -item[1]):
                        if late <= early:
                            break
                        if depth >= 4 and not any(not e & (1 << slow) for e in edges):
                            continue
                        waiting = dormant | {v for v in anchors if arrival[v] > 1}
                        if any(not padding["lift"]["forces_except"](adj, blue, v)
                               for v in waiting - dormant):
                            continue
                        white = {i for i, v in ends.items() if i not in neutral or arrival[v] > 1}
                        if any(blue & (1 << ends[i]) for i in white):
                            continue
                        deadlines = {i: max(row[ends[i]] for _, row in restricted) for i in white}
                        delays = {i: arrival[ends[i]] for i in white}
                        side_deadlines = {v: max(row[v] for _, row in restricted)
                                          for v in waiting}
                        if any(arrival[v] <= t and (0 not in white or delays[0] <= t + 1)
                               for v, t in side_deadlines.items()):
                            continue
                        if all(delays[i] > t or (0 in white and delays[0] > t)
                               for i, t in deadlines.items()):
                            return dict(blue=blue, killing=h1 | h2, slow=slow, early=early,
                                        late=late, white=sorted(white), deadlines=deadlines,
                                        delays=delays, neutral=sorted(set(ends) - white),
                                        waiting=sorted(waiting),
                                        edge=next((e for e in edges if not e & (1 << slow)), None))
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--extra", type=int, default=2)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    reports = []
    unresolved = []
    for left, right, depth, exterior in product(
            range(3), range(13), range(5), product((1, 2), repeat=2)):
        if left > right or left + right < 2 or (left == right and exterior[0] > exterior[1]):
            continue
        lengths = (3 if exterior == (1, 1) else 4, *exterior)
        proof = search(left, right, depth, lengths, args.extra)
        if proof:
            reports.append(dict(gaps=(left, right), depth=depth, lengths=lengths, **proof))
        else:
            unresolved.append((left, right, depth, lengths))
    with args.output.open("x", encoding="utf-8") as output:
        json.dump(dict(proofs=reports, unresolved=unresolved), output, indent=2)
        output.write("\n")
    print(json.dumps(dict(covered=len(reports), unresolved=len(unresolved)),
                     separators=(",", ":")))


if __name__ == "__main__":
    main()
