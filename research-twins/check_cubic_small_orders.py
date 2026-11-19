"""Replay the two-round single-loss census on the House of Graphs cubic lists."""

from argparse import ArgumentParser
from functools import cache, reduce
from hashlib import sha256
from itertools import combinations
from operator import and_
from pathlib import Path
from urllib.request import urlopen


CATALOG = {
    4: (1, '62073900de6d9451c02333f80b3c4de1105edb4559989fee6cfa91c1365d102b'),
    6: (2, '49a7391d96ad84fd13c8b5267ef23c215085ed317e6146e479df2bcdfd672949'),
    8: (5, '6946d13a0aec85386d47d087ad2a9f2561b05d8580f0ec937414f8d31359d34f'),
    10: (19, '0c3182bcbbfdc38fc7b84f3a1ac510834c3064524db00afeac212a3292f17c7b'),
    12: (85, '21bab16fbf7db826928315b9ca1d64684c0b1f7014b02fab0c6f2fb2f247104b'),
    14: (509, '6657f77868567a7e604a2325b5d748e5a04848b4ab75310ffa3ba695d26c66fe'),
    16: (4060, '26364c59882552ff5d35d41525aa8847ed10affed6eb5d05e94cbd0831644835'),
}
CATALOG_URL = 'https://houseofgraphs.org/data/cubics/'
EXPECTED = {
    4: (1, 5, 1, 1, ((1, 1, 0), (1, 1, 0))),
    6: (2, 52, 11, 11, ((2, 2, 0), (2, 2, 0))),
    8: (4, 579, 153, 142, ((3, 3, 1), (3, 3, 1))),
    10: (14, 7734, 2776, 2520, ((5, 4, 2), (5, 4, 2))),
    12: (57, 117877, 56242, 48635, ((6, 6, 3), (6, 6, 3))),
    14: (341, 2459572, 1402778, 1219269, ((7, 7, 4), (7, 7, 4))),
    16: (2828, 69230734, 45667818, 40237777, ((8, 8, 5), (8, 8, 5))),
}


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit
        mask ^= bit


def read_catalog(order, directory):
    filename = f'cub{order:02d}.g6'
    if directory is None:
        with urlopen(CATALOG_URL + filename, timeout=30) as reply:
            raw = reply.read()
    else:
        raw = (directory / filename).read_bytes()
    count, expected_hash = CATALOG[order]
    lines = raw.splitlines()
    if len(lines) != count or sha256(raw).hexdigest() != expected_hash:
        raise ValueError(f'Unexpected catalog bytes for {filename}')
    for row in lines:
        if row[0] != order + 63:
            raise ValueError(f'Unexpected graph order in {filename}')
        graph = [0] * order
        for index, (u, v) in enumerate((u, v) for v in range(order) for u in range(v)):
            if (row[1 + index // 6] - 63) & (32 >> (index % 6)):
                graph[u] |= 1 << v
                graph[v] |= 1 << u
        yield graph


def connected(graph, available):
    reached = pending = available & -available
    while pending:
        bit = pending & -pending
        pending ^= bit
        fresh = graph[bit.bit_length() - 1] & available & ~reached
        reached |= fresh
        pending |= fresh
    return reached == available


@cache
def initial_columns(order):
    """Column v has a set bit at every seed mask that contains vertex v."""
    domain = (1 << (1 << order)) - 1
    columns = []
    for vertex in range(order):
        width = 1 << vertex
        repetitions = domain // ((1 << (2 * width)) - 1)
        pattern = ((1 << width) - 1) << width
        columns.append(repetitions * pattern)
    return domain, tuple(columns)


def finished_by_round(graph, initial):
    """Propagate all seed masks in parallel, with one integer per vertex."""
    rules = []
    for source, row in enumerate(graph):
        a, b, c = (bit.bit_length() - 1 for bit in bits(row))
        rules.extend(((a, source, b, c), (b, source, a, c), (c, source, a, b)))
    blue = list(initial)
    finished = [reduce(and_, blue)]
    while True:
        updated = blue[:]
        for target, source, first, second in rules:
            updated[target] |= blue[source] & blue[first] & blue[second]
        if updated == blue:
            return finished
        finished.append(reduce(and_, updated))
        blue = updated


def summarize_graph(graph, records):
    n = len(graph)
    full = (1 << n) - 1
    if any(row.bit_count() != 3 for row in graph) or not connected(graph, full):
        raise ValueError('The catalog contains a graph outside the connected cubic class')
    three = all(connected(graph, full ^ a ^ b) for a, b in combinations(bits(full), 2))
    relevant = records if three else records[:1]
    domain, initial = initial_columns(n)
    finished = finished_by_round(graph, initial)
    nominal = finished[min(2, len(finished) - 1)]
    stalled = domain ^ finished[-1]

    def before_a_loss(after):
        before = 0
        for v, column in enumerate(initial):
            before |= (after & ~column) << (1 << v)
        return before

    tolerant = nominal & ~before_a_loss(stalled)
    unclassified = tolerant
    for time in range(len(finished) - 1, 0, -1):
        before = before_a_loss(finished[time] ^ finished[time - 1])
        if before & nominal:
            for record in relevant:
                record[0] = max(record[0], time)
        worst_at_time = unclassified & before
        if not worst_at_time:
            continue
        unclassified ^= worst_at_time
        for record in relevant:
            record[1] = max(record[1], time)
        best = min(record[2] for record in relevant)
        if time > best:
            cases = worst_at_time & finished[min(2, time - best - 1)]
            gap = support_gap(cases, time, best, stalled, finished, n)
            for record in relevant:
                record[2] = max(record[2], gap)
    return three, nominal.bit_count(), tolerant.bit_count()


def support_gap(cases, worst, best, stalled, finished, order):
    if not cases:
        return best
    byte_count = 1 << (order - 3)
    stalled_bytes = stalled.to_bytes(byte_count, 'little')
    deadlines = [entry.to_bytes(byte_count, 'little') for entry in finished[:worst]]

    def contains(table, coloring):
        return (table[coloring // 8] >> (coloring % 8)) & 1

    @cache
    def killing_size(blue):
        if contains(stalled_bytes, blue):
            return 0
        return 1 + min(killing_size(blue ^ bit) for bit in bits(blue))

    for bit in bits(cases):
        blue = bit.bit_length() - 1
        minimum = killing_size(blue)
        for deadline in range(worst - best):
            by_time = [seed for seed in bits(blue) if contains(deadlines[deadline], blue ^ seed)]
            if any(contains(stalled_bytes, blue ^ sum(selected))
                   for selected in combinations(by_time, minimum)):
                best = worst - deadline
                break
    killing_size.cache_clear()
    return best


def census(order, directory):
    records = ([0, 0, 0], [0, 0, 0])
    three_count = intact = tolerant = three_tolerant = 0
    for graph in read_catalog(order, directory):
        three, nominal, stable = summarize_graph(graph, records)
        three_count += three
        intact += nominal
        tolerant += stable
        three_tolerant += stable if three else 0
    return three_count, intact, tolerant, three_tolerant, tuple(map(tuple, records))


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--data', type=Path, help='Read the catalog files from this directory')
    parser.add_argument('--through', type=int, choices=(14, 16), default=16)
    args = parser.parse_args()
    for order in range(4, args.through + 1, 2):
        result = census(order, args.data)
        if result != EXPECTED[order]:
            raise AssertionError((order, result, EXPECTED[order]))
        print(order, CATALOG[order][0], *result, flush=True)


if __name__ == '__main__':
    main()
