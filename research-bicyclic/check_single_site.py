"""Check rooted-tree attachments to the four positive leafless bicyclic cores."""

from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
THETA = runpy.run_path(str(HERE / 'check_theta.py'))
TWO_CYCLES = runpy.run_path(str(HERE / 'check_two_cycles.py'))
SITES = {
    'bowtie': (0, 1),
    'theta122': (0, 2),
    'theta222': (0, 2),
    'theta223': (0, 2, 4),
}
STAR_SUPPORTS = {'bowtie': (1, 2), 'theta122': (2, 3)}
# Entries give the base blue set, killing pair and slow loss with one new leaf.
LEAF_BASES = {
    ('bowtie', 1): ((0, 1, 3, 4, 5), (3, 4), 0),
    ('theta122', 2): ((0, 1, 3, 4), (0, 1), 3),
    ('theta222', 0): ((0, 2, 3, 4, 5), (2, 3), 0),
    ('theta222', 2): ((0, 1, 3, 4, 5), (0, 1), 3),
    ('theta223', 0): ((0, 2, 3, 4, 6), (2, 3), 0),
    ('theta223', 2): ((0, 1, 2, 4, 5, 6), (4, 5), 2),
    ('theta223', 4): ((1, 2, 3, 5, 6), (2, 3), 1),
}


def cores():
    result = {'bowtie': TWO_CYCLES['graph'](3, 3, True)[0]}
    for lengths in sorted(THETA['POSITIVE_CORES']):
        name = 'theta' + ''.join(map(str, lengths))
        result[name] = THETA['theta'](lengths)[0]
    return result


def root_shape(adj, vertex, parent):
    children = THETA['TOOLS']['neighbors'](adj[vertex])
    return tuple(sorted(root_shape(adj, child, vertex) for child in children if child != parent))


def parent_list(shape):
    parents = []

    def visit(root, children):
        for child in children:
            label = len(parents) + 1
            parents.append(root)
            visit(label, child)

    visit(0, shape)
    return tuple(parents)


def small_rooted_trees():
    trees = THETA['SIMULATOR']['tree_families'](6)
    for size, family in trees:
        if size == 1:
            continue
        shapes = {root_shape(adj, v, None) for adj in family for v in range(size)}
        yield from sorted(parent_list(shape) for shape in shapes)


def attach(core, site, parents):
    adj = list(core)
    labels = [site]
    for parent in parents:
        labels.extend(THETA['append_leaves'](adj, labels[parent], 1))
    return adj, labels


def expected_positive(name, site, parents):
    return site == 0 and name in STAR_SUPPORTS and not any(parents)


def replay_negative(name, site, parents, adj, labels):
    if (name, site) in LEAF_BASES:
        seed, support, slow = LEAF_BASES[name, site]
        blue = set(seed).union(labels[1:])
    else:
        depths = [0]
        for parent in parents:
            depths.append(depths[parent] + 1)
        leaf = max(range(1, len(labels)), key=depths.__getitem__)
        slow = labels[leaf]
        white = labels[parents[leaf - 1]]
        blue = set(range(len(adj))) - {white}
        support = STAR_SUPPORTS[name]
    mask = THETA['mask']
    THETA['certify'](adj, mask(blue), mask(support), 1 << slow, 1, 2)


def main():
    models = cores()
    rooted = list(small_rooted_trees())
    positive = negative = larger = 0
    for name, core in models.items():
        for site in SITES[name]:
            for parents in rooted:
                adj, labels = attach(core, site, parents)
                predicted = expected_positive(name, site, parents)
                actual, error, _, _ = THETA['every_minimum_support'](adj)
                if actual != predicted:
                    raise AssertionError((name, site, parents, actual, error))
                if predicted:
                    positive += 1
                else:
                    replay_negative(name, site, parents, adj, labels)
                    negative += 1

            for size in (8, 32, 64):
                shapes = ((0,) * size, tuple(range(size)), tuple(i // 2 for i in range(size)))
                for parents in shapes:
                    if not expected_positive(name, site, parents):
                        adj, labels = attach(core, site, parents)
                        replay_negative(name, site, parents, adj, labels)
                        larger += 1
    print('Rooted trees with one to five attached vertices:', len(rooted))
    print('Exact placements:', positive + negative, 'positive:', positive, 'negative:', negative)
    print('Larger negative certificate replays through 64 attached vertices:', larger)


if __name__ == '__main__':
    main()
