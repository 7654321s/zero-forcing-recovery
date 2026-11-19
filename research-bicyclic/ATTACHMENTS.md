# A rooted tree at one vertex of a positive bicyclic core

**Theorem.** Take one of the [four positive leafless bicyclic graphs](NEARBY_FAMILIES.md#bicyclic-graphs-of-minimum-degree-two). Attach a nontrivial rooted tree by identifying its root with one core vertex. The resulting graph satisfies `EveryMinimumSupport` in exactly two cases. The attachment consists of direct leaves at the shared vertex of the two triangles, or it consists of direct leaves at a degree-three vertex of the diamond $\Theta(1,2,2)$. Every negative attachment admits a two-vertex minimum killing support with restricted time one and a specified singleton loss that finishes in round two.

The other two cores are $\Theta(2,2,2)$ and $\Theta(2,2,3)$. The theorem concerns one tree attachment site on these four cores. For [direct leaves at multiple sites](LEAF_MULTIPLICITIES.md), truncating each leaf multiplicity at two gives a separate classification.

## Direct leaves at the two positive sites

For the diamond this is the [one-sided leaf classification](NEARBY_FAMILIES.md#leaves-and-paths-on-a-diamond). For the two triangles sharing $x$, put all the new leaves at $x$. Each of the two nonshared triangle pairs is a fort. If a forcing set has a killing singleton, the two budget comparisons agree automatically because the minimum support has size one. Otherwise both triangle pairs must start wholly blue. When there are at least two new leaves, each pair of new leaves is also a fort, so all leaves must start blue. In this singleton-tolerant case the minimum support has size two, since removing a triangle pair kills.

If all leaves start blue and $x$ starts blue, every singleton loss takes one round. If all leaves start blue and $x$ starts white, an unaffected triangle restores $x$ in the first round. In that round the lost vertex cannot be forced because $x$ starts white. It then fills in round two. The only other possibility is one leaf that starts white. If $x$ starts blue, a lost triangle vertex or $x$ itself is restored in round one, and the leaf fills in round two. If $x$ starts white, the unaffected triangle restores $x$ in round one, the lost triangle vertex fills in round two and the leaf fills in round three. In each of these configurations the singleton times agree for every loss, which proves the property at budget one. At larger budgets a minimum support itself can be lost, and budget zero compares the intact coloring on both sides.

## A deeper vertex at either of the two positive sites

Suppose the attachment tree has a vertex at distance at least two from the root. Choose a deepest leaf $z$ and its parent $u$. The vertex $u$ is outside the core. Start with every vertex blue except $u$. Let $H$ be the pair of nonshared vertices in either triangle of the shared-vertex graph, or the pair of degree-two vertices in the diamond.

The two vertices of $H$ remain twins, so losing both kills. After either singleton from $H$, the lost vertex fills in round one from its mate on the shared-vertex graph or the leafless degree-three vertex of the diamond. In the same round the leaf $z$ restores $u$. If $z$ is lost instead, the parent of $u$ forces $u$ in round one. That parent is blue and its sole white neighbor is $u$. The lost leaf $z$ must wait until round two because its sole neighbor starts white.

After any singleton loss there are exactly two white vertices, $u$ and the lost vertex $v$. They cannot be twins. If $v\ne z$, the leaf $z$ distinguishes them by adjacency to $u$ alone. If $v=z$, the parent of $u$ distinguishes them. Hence some blue vertex sees exactly one of the two whites and can force it in round one. The last white then fills by connectivity. Thus $H$ is a minimum killing pair with the claimed time gap.

## The seven remaining site types

Up to symmetry, the shared-vertex graph has the shared vertex and one nonshared site. The diamond and $\Theta(2,2,2)$ each have two site types, distinguished by degree. The three site types in $\Theta(2,2,3)$ are a common endpoint, the internal vertex of a length-two path, and an internal vertex of the length-three path. The table gives the one-leaf certificates for all seven excluded site types.

Use the [theta numbering](NEARBY_FAMILIES.md#remaining-theta-graphs), with the two endpoints numbered $0,1$. For the shared-vertex graph the triangles are $(0,1,2)$ and $(0,3,4)$. Number the added leaf after the last core vertex. In each row the intact coloring and both restricted singleton losses finish in one round. The designated loss takes two rounds, every singleton loss finishes, and removing both support vertices kills. These finite statements can be replayed by the command below.

| Core | Attachment site | Blue vertices | Killing pair | Slow loss |
| --- | --- | --- | --- | --- |
| Shared triangles | 1 | $0,1,3,4,5$ | $3,4$ | 0 |
| $\Theta(1,2,2)$ | 2 | $0,1,3,4$ | $0,1$ | 3 |
| $\Theta(2,2,2)$ | 0 | $0,2,3,4,5$ | $2,3$ | 0 |
| $\Theta(2,2,2)$ | 2 | $0,1,3,4,5$ | $0,1$ | 3 |
| $\Theta(2,2,3)$ | 0 | $0,2,3,4,6$ | $2,3$ | 0 |
| $\Theta(2,2,3)$ | 2 | $0,1,2,4,5,6$ | $4,5$ | 2 |
| $\Theta(2,2,3)$ | 4 | $1,2,3,5,6$ | $2,3$ | 1 |

In every row the added leaf is blue and belongs to neither the support nor the slow loss. Clone this leaf to as many blue leaves as the root of the attachment tree has children. For all compared runs the original leaf is blue. Whenever its parent starts white, the original leaf already restores it in round one. The clones cannot restore it any sooner and change no other forces on the old vertices. Thus the relevant times and the double failure persist. Any original singleton loss still finishes because the new blue neighbors cannot block an old force. A loss at a clone reduces to the original leaf loss by swapping the two indistinguishable leaves.

Now turn each blue leaf into the head of its subtree in the attachment tree, coloring every descendant blue. All the heads stay blue in each compared run. The descendants have no effect on the compared runs, and their initial blue colors cannot block completion after an old singleton loss. For a singleton loss deeper in the new tree, a blue child restores a lost internal vertex in round one. A lost leaf whose parent lies below a head is restored by its parent in round one, since all the parent's other neighbors are blue. A leaf directly below a head can be restored as soon as the core attachment vertex is blue. If the attachment vertex starts white, the table provides an independent core restoration in round one. Vertex $0$ restores site $2$ of $\Theta(1,2,2)$ and $\Theta(2,2,2)$, and vertex $5$ restores site $4$ of $\Theta(2,2,3)$. In those cases the lost leaf fills in round two. After the new loss is restored all intact seeds are present, so the graph finishes. This preserves the budget-one certificate for arbitrary rooted trees at these seven sites.

## Reproduction

```sh
python -B research-bicyclic/check_single_site.py
```

The checker independently enumerates the full support property for 36 rooted trees with one to five attached vertices at each of nine sites up to symmetry. It confirms 10 positives and replays the certificates for all 314 negative placements. It also replays 75 larger certificates on stars, paths and branching trees with up to 64 attached vertices. The argument above applies to all sizes.
