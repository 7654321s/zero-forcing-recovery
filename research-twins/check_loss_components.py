"""Check that separated groups of deleted seeds have independent arrival traces."""

from itertools import combinations, pairwise
from pathlib import Path
from random import Random
import runpy


MODEL = runpy.run_path(str(Path(__file__).with_name('check_multiple_loss_bounds.py')))
adjacency = MODEL['adjacency']
mask = MODEL['mask']
members = MODEL['members']
trace = MODEL['trace']


def nominal_cones(graph, seeds):
    """Record the seed ancestors of one nominal cause for each vertex."""
    _, arrivals = trace(graph, seeds)
    if None in arrivals:
        raise ValueError('The intact set does not force the graph')
    supporters = [0] * len(graph)
    cones = {s: 0 for s in members(seeds)}
    for v in sorted(range(len(graph)), key=arrivals.__getitem__):
        if arrivals[v] == 0:
            supporters[v] = 1 << v
        else:
            source = MODEL['force_source'](graph, arrivals, v)
            prerequisites = (graph[source] ^ (1 << v)) | (1 << source)
            for u in members(prerequisites):
                supporters[v] |= supporters[u]
        for s in members(supporters[v]):
            cones[s] |= 1 << v
    return arrivals, supporters, cones


def seed_contacts(graph, supporters, cones):
    """Join two seed cones that meet or have graph distance at most two."""
    contacts = {}
    for s, cone in cones.items():
        neighborhood = cone
        for _ in range(2):
            enlarged = neighborhood
            for v in members(neighborhood):
                enlarged |= graph[v]
            neighborhood = enlarged
        touched = 0
        for v in members(neighborhood):
            touched |= supporters[v]
        contacts[s] = touched & ~(1 << s)
    return contacts


def loss_components(contacts, losses):
    while losses:
        frontier = losses & -losses
        component = 0
        while frontier:
            component |= frontier
            losses &= ~frontier
            neighbors = 0
            for s in members(frontier):
                neighbors |= contacts[s]
            frontier = losses & neighbors
        yield component


def connected_losses(contacts, budget):
    """Enumerate nonempty connected losses once, using their least seed as root."""
    def grow(chosen, frontier, excluded, available):
        yield chosen
        if chosen.bit_count() == budget:
            return
        for s in members(frontier):
            bit = 1 << s
            frontier ^= bit
            expanded = (frontier | contacts[s]) & available & ~(chosen | bit | excluded)
            yield from grow(chosen | bit, expanded, excluded, available)
            excluded |= bit

    if budget < 1:
        return
    seeds = mask(contacts)
    for root, row in contacts.items():
        available = seeds & ~((2 << root) - 1)
        yield from grow(1 << root, row & available, 0, available)


def check_case(graph, seeds, losses_to_check, enumeration_budget=None):
    intact, supports, cones = nominal_cones(graph, seeds)
    contacts = seed_contacts(graph, supports, cones)
    count = separated = 0
    for losses in losses_to_check:
        components = tuple(loss_components(contacts, losses))
        predicted = list(intact)
        for component in components:
            region = 0
            for s in members(component):
                region |= cones[s]
            _, arrival = trace(graph, seeds ^ component)
            for v in members(region):
                predicted[v] = arrival[v]
        if tuple(predicted) != trace(graph, seeds ^ losses)[1]:
            raise AssertionError(('independent loss trace', len(graph), seeds, losses))
        count += 1
        separated += len(components) > 1

    if enumeration_budget is not None:
        candidates = [mask(group) for size in range(1, enumeration_budget + 1)
                      for group in combinations(tuple(members(seeds)), size)]
        expected = {losses for losses in candidates
                    if next(loss_components(contacts, losses)) == losses}
        found = list(connected_losses(contacts, enumeration_budget))
        if len(found) != len(expected) or set(found) != expected:
            raise AssertionError(('connected loss enumeration', len(graph), seeds))
    return count, separated


def check_examples():
    checked = separated = 0
    possible = tuple(combinations(range(4), 2))
    for edge_mask in range(1 << len(possible)):
        graph = adjacency(4, (possible[i] for i in members(edge_mask)))
        for seeds in range(1, 1 << len(graph)):
            if None in trace(graph, seeds)[1]:
                continue
            subsets = [v for v in range(1 << len(graph)) if not v & ~seeds]
            count, independent = check_case(graph, seeds, subsets, seeds.bit_count())
            checked += count
            separated += independent

    graph = adjacency(19, pairwise(range(19)))
    seeds = mask(range(0, 19, 2))
    subsets = [mask(group) for size in range(4) for group in combinations(tuple(members(seeds)), size)]
    count, independent = check_case(graph, seeds, subsets, 3)
    checked += count
    separated += independent

    base = MODEL['cubic_two_round_chain_certificate'](3)
    graph, seeds, _, _ = MODEL['cyclic_cubic_chain_lift'](base, 7, reversed_edge=(0, 1))
    rng = Random(319)
    pool = tuple(members(seeds))
    subsets = [mask(rng.sample(pool, size)) for size in range(1, 9) for _ in range(25)]
    count, independent = check_case(graph, seeds, subsets)
    checked += count
    separated += independent
    if not separated:
        raise AssertionError('The examples never split into distinct components')
    return checked, separated


if __name__ == '__main__':
    checked, separated = check_examples()
    print(f'{checked} loss traces checked, including {separated} with separate components')
