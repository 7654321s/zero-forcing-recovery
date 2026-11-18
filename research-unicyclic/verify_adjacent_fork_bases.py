"""Independently check the remaining unicyclic bases and their extension conditions."""

import argparse
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
enumeration = runpy.run_path(str(HERE / "enumerate_unicyclic.py"))
simulate = runpy.run_path(str(enumeration["BASELINE"]))["completion_time"]


def vertices(mask):
    return set(enumeration["neighbors"](mask))


def mask(vertices):
    return sum(1 << v for v in vertices)


def attach(adj, start, count):
    path = []
    for _ in range(count):
        new = len(adj)
        adj[start].add(new)
        adj.append({start})
        path.append(new)
        start = new
    return path


def make_base(gaps, depth, lengths):
    n = 3 + sum(gaps)
    adj = [{(v - 1) % n, (v + 1) % n} for v in range(n)]
    stem = [0, *attach(adj, 0, depth)]
    fork = stem[-1]
    attach(adj, fork, 1)
    b = gaps[0] + 1
    ends = [attach(adj, root, length)[-1]
            for root, length in zip((fork, b, b + 1), lengths)]
    return adj, stem, ends


def trace(adj, initial, suppress=None):
    blue = set(initial)
    times = dict.fromkeys(blue, 0)
    time = 0
    while len(blue) < len(adj):
        boundaries = (adj[v] - blue for v in blue if v != suppress)
        forced = set().union(*(targets for targets in boundaries if len(targets) == 1))
        if not forced:
            break
        time += 1
        blue.update(forced)
        times.update(dict.fromkeys(forced, time))
    return times


def verify_times(adj, blue, killing, slow, early, late):
    assert len(killing) == 2 and killing <= blue and slow in blue - killing
    graph = [mask(neighbors) for neighbors in adj]
    base = mask(blue)
    deadline = simulate(graph, base)
    all_losses = {v: simulate(graph, base ^ (1 << v)) for v in blue}
    assert max(deadline, *all_losses.values()) <= len(adj)
    assert simulate(graph, base ^ mask(killing)) == len(adj) + 1
    assert max(deadline, *(all_losses[v] for v in killing)) == early
    assert all_losses[slow] == late > early


def verify_base(row):
    adj, stem, ends = make_base(row["gaps"], row["depth"], row["lengths"])
    blue, killing, slow = vertices(row["blue"]), vertices(row["killing"]), row["slow"]
    verify_times(adj, blue, killing, slow, row["early"], row["late"])

    restricted = [trace(adj, state) for state in [blue, *(blue - {v} for v in killing)]]
    delayed = trace(adj, blue - {slow})
    compared = [*restricted, delayed, trace(adj, blue - killing)]
    assert max(max(t.values()) for t in restricted) == row["early"]
    assert max(delayed.values()) == row["late"]

    white, neutral = set(row["white"]), set(row["neutral"])
    variable = {0, *(i for i in (1, 2) if row["lengths"][i] > 1)}
    assert white.isdisjoint(neutral) and white | neutral == variable
    for i in neutral:
        v = ends[i]
        assert all(t.get(v, 2) <= 1 for t in compared)
        assert v not in blue or adj[v] & blue or len(trace(adj, blue, v)) == len(adj)
    assert all(ends[i] not in blue for i in white)
    early = {i: max(t[ends[i]] for t in restricted) for i in white}
    late = {i: delayed[ends[i]] for i in white}
    assert early == {int(i): t for i, t in row["deadlines"].items()}
    assert late == {int(i): t for i, t in row["delays"].items()}
    assert all(late[i] > t or (0 in white and late[0] > t) for i, t in early.items())

    waiting = {v for v in stem[:-1] if any(t.get(v, 2) > 1 for t in compared)}
    assert waiting == set(row["waiting"])
    side_early = {v: max(t[v] for t in restricted) for v in waiting}
    for v in waiting:
        assert len(trace(adj, blue, v)) == len(adj)
        assert delayed[v] > side_early[v] or (0 in white and late[0] > side_early[v] + 1)

    if row["depth"] == 4:
        edge = vertices(row["edge"])
        assert len(edge) == 2 and edge <= blue - killing - {slow}
        assert any(edge == {a, b} for a, b in zip(stem, stem[1:]))
        assert any(adj[v] <= blue for v in edge)
    else:
        assert row["edge"] is None
    return adj, blue, killing, slow, stem, ends, side_early, delayed


def replay_extension(row, base, increments, inserted, grow_sides):
    adj, blue, killing, slow, stem, ends, side_early, delayed = base
    adj, blue = [set(neighbors) for neighbors in adj], set(blue)
    early, late = [row["early"]], [row["late"]]
    for i in (*row["neutral"], *row["white"]):
        suffix = attach(adj, ends[i], increments[i])
        if i in row["neutral"]:
            blue.update(suffix)
        else:
            early.append(row["deadlines"][str(i)] + increments[i])
            late.append(row["delays"][str(i)] + increments[i])
    max_side = (row["lengths"][0] + increments[0]) // 2
    if grow_sides and max_side >= 2:
        for index, v in enumerate(stem[:-1]):
            length = max_side if index % 2 == 0 else 2
            added = attach(adj, v, length)
            if v in side_early:
                blue.update(added[:-1:2])
                early.append(side_early[v] + (length + 1) // 2)
                late.append(delayed[v] + (length + 1) // 2)
            else:
                blue.update(added)
    if inserted:
        assert row["depth"] == 4
        u, v = sorted(vertices(row["edge"]))
        adj[u].remove(v)
        adj[v].remove(u)
        new_stem = attach(adj, u, inserted)
        last = new_stem[-1]
        adj[last].add(v)
        adj[v].add(last)
        blue.update(new_stem)
        if grow_sides and max_side >= 2:
            for w in new_stem:
                blue.update(attach(adj, w, max_side))
    verify_times(adj, blue, killing, slow, max(early), max(late))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bases", type=Path, default=HERE / "adjacent-fork-exploration-03.json")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    source = args.bases.read_bytes()
    data = json.loads(source)
    assert not data["unresolved"]
    checked = set()
    extended = 0
    for row in data["proofs"]:
        gaps, lengths = tuple(row["gaps"]), tuple(row["lengths"])
        depth = row["depth"]
        key = (gaps, depth, lengths)
        assert key not in checked
        base = verify_base(row)
        grown = tuple(3 if length == 2 else 0 for length in lengths[1:])
        for increments, inserted in (
            ((0, 0, 0), int(depth == 4)),
            ((6, *grown), 3 if depth == 4 else 0),
            ((9, grown[0], 0), 8 if depth == 4 else 0),
        ):
            replay_extension(row, base, increments, inserted, grow_sides=True)
            extended += 1
        checked.add(key)

    expected = set()
    for n in range(5, 18):
        for b in range(1, n - 1):
            gaps = (b - 1, n - b - 2)
            if not 0 <= gaps[0] <= min(2, gaps[1]) or gaps[1] > 12:
                continue
            for depth, left, right in product(range(5), (1, 2), (1, 2)):
                if gaps[0] == gaps[1] and left > right:
                    continue
                expected.add((gaps, depth, (3 if left == right == 1 else 4, left, right)))
    assert checked == expected

    report = dict(status="passed", base_certificates=len(checked), extended_replays=extended,
                  bases_sha256=sha256(source).hexdigest(),
                  verifier_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                  simulator_sha256=sha256(enumeration["BASELINE"].read_bytes()).hexdigest())
    with args.output.open("x", encoding="utf-8") as output:
        json.dump(report, output, indent=2)
        output.write("\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
