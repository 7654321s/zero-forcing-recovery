# Theta cores, diamond attachments and cycle bouquets

We use the same [synchronous forcing and loss model](../README.md#模型与定理) as the two-cycle classification. A fort is a nonempty set such that every outside vertex has zero or at least two neighbors in it. An initially white fort never turns blue. In particular, any two vertices with the same neighbors outside the pair form a fort. A connected graph with just one white vertex fills it in the next round.

In each parametric exclusion the initial blue set is $B$, the killing pair is $H$, and the delayed singleton is $z\in B\setminus H$. The intact run and both singleton losses from $H$ finish by round $R$. All singleton losses finish, the double loss of $H$ fails, and the loss of $z$ takes strictly more than $R$ rounds. This gives a minimum killing support and a counterexample at budget one by [the certificate implication](../research-unicyclic/CertificateDeadline.lean).

## Theta graphs

Write $\Theta(p,q,r)$ for the union of three internally disjoint paths of edge lengths $p\leq q\leq r$ with common endpoints $x,y$. Here $p\geq 1$ and $q\geq 2$, so at most one path is the edge $xy$. The order is $p+q+r-1$. Write the internal vertices on each path as $a_i,b_i,c_i$ in order from $x$.

Through order 15 there are 109 such length triples. The three positive graphs are $\Theta(1,2,2)$, $\Theta(2,2,2)$ and $\Theta(2,2,3)$. The other 106 graphs each have an explicit two-loss certificate at budget one. The replay computes these certificates from the graph and verifies each loss condition. [ThetaSeeds.lean](ThetaSeeds.lean) checks the three positive graphs against the full quantified property.

The constructions below classify the whole shortest-path-one family and three shortest-path-two families. The other theta length triples of arbitrary order remain open here.

### Two cycles sharing an edge

The graph $\Theta(1,q,r)$ satisfies `EveryMinimumSupport` exactly when $q=r=2$. This class consists of two cycles with their common edge $xy$ and no other shared vertices. For $r\geq5$ the construction gives the exact times

$$
T=\lfloor(r-3)/2\rfloor,\qquad U=\lceil q/2\rceil,\qquad
R=\lceil(T+U+1)/2\rceil,\qquad S=T+1+\lceil U/2\rceil.
$$

Here $S-R\geq\lceil T/2\rceil\geq1$. In particular, if the shorter cycle is a triangle then $U=1$ and $S-R=\lfloor(r+1)/4\rfloor$. This shows that the unrestricted worst time can exceed the restricted one by arbitrarily many rounds even at budget one with a two-element support.

For $r\leq4$ the positive case is the diamond $\Theta(1,2,2)$ from the finite Lean checks. The table gives the other cases. The singleton times are ordered by the blue vertices in the list $x,y,b_1,\ldots,b_{q-1},c_1,\ldots,c_{r-1}$, skipping the initially white vertices. Direct synchronous steps give the displayed times. In every row the coloring after the double loss of $H$ is already fixed and has whites.

| $(q,r)$ | Initially white | $H$ | $z$ | Intact time | Singleton times |
| --- | --- | --- | --- | --- | --- |
| $(2,3)$ | $c_2$ | $\{b_1,c_1\}$ | $x$ | 1 | $(2,1,1,1)$ |
| $(2,4)$ | $b_1$ | $\{c_1,c_3\}$ | $y$ | 1 | $(2,2,1,1,1)$ |
| $(3,3)$ | $b_1,c_2$ | $\{b_2,c_1\}$ | $x$ | 1 | $(3,3,2,2)$ |
| $(3,4)$ | $b_1,c_3$ | $\{b_2,c_1\}$ | $y$ | 1 | $(1,3,2,2,1)$ |
| $(4,4)$ | $c_1,c_2,c_3$ | $\{b_1,b_3\}$ | $x$ | 2 | $(3,3,2,2,2)$ |

For $r\geq5$, color $x,y,c_1,c_3$ blue. Also color each even-indexed $b_i$ with $2\leq i\leq q-2$ and each even-indexed $c_i$ with $2\leq i\leq r-2$ blue. Put $H=\{c_1,c_3\}$ and $z=y$. The $b$-path has $U$ white vertices, and the tail of the $c$-path has $T$ white vertices. Both neighbors of $y$ on these paths start white. In the double loss all blue internal path vertices are isolated between two white vertices, and each endpoint has two white neighbors. Thus the double loss stalls.

Within either of these two white intervals, successive whites are adjacent or separated by one blue vertex. Every blue vertex in the interior of such an interval has two white neighbors at the start. Consequently, all forces into the interval advance from its ends. Each activated end fills one white per round until the intervals meet, since a blue separator can force the next white as soon as its other neighbor turns blue. The two advances cover distinct whites until possibly meeting on the last round.

For loss of $c_1$, $c_2$ restores $c_1$ in round one. The advance from the intact $c$-run starts in round one, and $x$ begins the $b$-path in round two. For loss of $c_3$, $x$ starts the $b$-path and $c_2$ restores $c_3$ in round one. The $c$-tail begins to fill in round two. The two left advances therefore begin at rounds one and two in either order. As long as both path neighbors of $y$ are white, $y$ cannot help. The first path finishes in the round when its left advance alone would finish. If the two left-only completion times are $F_1,F_2$, they sum to $T+U+1$. After round $\min(F_1,F_2)$ the remaining path needs $|F_1-F_2|$ more forces, which now proceed from both ends. Thus both restricted singleton runs finish in round $\lceil(F_1+F_2)/2\rceil=R$. The intact run is at least as fast by monotonicity.

When $y$ is lost, $x$ sees both $y$ and $b_1$ white, and the $b$-path cannot advance. The only advance is from the $c$-run, which reaches $c_{r-1}$ in round $T$. That vertex can then force $y$ in round $T+1$. The two endpoints now fill the $b$-path from both ends in $\lceil U/2\rceil$ more rounds, giving $S$. Subtracting $R$ gives $\lceil T/2\rceil$, plus one when $T$ is even and $U$ is odd.

If $x$ is lost, $c_1$ restores it using $c_2$ in round one and the intact blue set is available. Any remaining single loss outside $H\cup\{x,y\}$ keeps $x,y,c_1$ blue, so $x$ can force $b_1$ in round one. This advance along a degree-two path eventually fills the entire $b$-path even if it has one additional white vertex. The endpoint $y$ can then advance through the remaining $c$-path. Thus every singleton loss finishes.

### Two paths of length two

For $\Theta(2,2,r)$ with $r\geq4$, color all vertices except $y,c_{r-1}$ blue. Take $H=\{a_1,b_1\}$ and $z=x$. The pair $H$ is a fort. If one member of $H$ is lost, $x$ restores it, the other member forces $y$, and $c_{r-2}$ forces $c_{r-1}$ in round one. The last force uses the blue $c_{r-3}$.

If $x$ is lost instead, both $a_1$ and $b_1$ initially see two white neighbors, and $c_{r-1}$ is white. Thus $y$ stays white in round one. In the same round $c_1$ restores $x$ and $c_{r-2}$ forces $c_{r-1}$. The remaining white vertex $y$ fills in round two. For any other singleton loss, the intact $a_1,b_1$ and blue $x$ give $y$ in round one. Then $y$ can force $c_{r-1}$ if needed because both short-path vertices are blue. This leaves at most the lost vertex white. Thus $R=1$ and the delayed loss takes two rounds. With the three positive seeds this in particular classifies $\Theta(2,2,r)$ for $r\geq2$.

### A path of length two and a path of length three or four

For $\Theta(2,q,r)$ with $q\in\{3,4\}$ and $r\geq5$, color every vertex except $b_{q-1},c_{r-2}$ blue. Take $H=\{a_1,b_1\}$ and $z=c_{r-1}$. After the double loss $\{a_1,b_1,b_{q-1}\}$ is a fort. Each endpoint sees exactly two of these vertices, and the interior $b_2$ when $q=4$ sees both white vertices of its own path.

When $a_1$ is lost, $x$ restores it, and the pair $b_{q-3},b_{q-2}$ supplies the force into $b_{q-1}$, with $b_0=x$. When $b_1$ is lost, $x$ restores it and $y$ forces $b_{q-1}$. The other white vertex $c_{r-2}$ is filled by its predecessor with a blue predecessor of its own. These moves all occur in round one.

When $z=c_{r-1}$ is lost, its only initially blue neighbor is $y$, which sees both $b_{q-1}$ and $z$ white. The predecessor pairs on the two longer paths fill $b_{q-1},c_{r-2}$ in round one, so $z$ fills in round two. The other singleton losses have the following recovery moves.

- A lost endpoint is restored by $a_1$. If $y$ is lost, the predecessor pairs fill both initially white vertices. If $x$ is lost, $y$ can fill $b_{q-1}$ and the predecessor pair on the longest path fills $c_{r-2}$.
- If $q=4$ and $b_2$ is lost, $b_1$ restores it and $y$ fills $b_3$. The longest path is unaffected.
- For any other singleton loss on the longest path, the force into $b_{q-1}$ remains available. The disjoint pairs $\{c_{r-4},c_{r-3}\}$ and $\{c_{r-1},y\}$ can each supply a force into $c_{r-2}$. One survives, leaving at most the lost vertex white after round one.

This gives $R=1$ in both families.

## Leaves and paths on a diamond

Let the diamond $\Theta(1,2,2)$ have adjacent degree-three vertices $x,y$ and two degree-two vertices $a,b$ adjacent to both. Attach $s$ leaves at $x$ and $t$ leaves at $y$ with no other attachments. The graph satisfies `EveryMinimumSupport` exactly when one count is zero or both counts are at least two.

Suppose that one root, say $x$, has exactly one leaf $z$, and the other has at least one. Color all nonroots blue. The pair $H=\{a,b\}$ is a fort. The intact coloring fills both roots in round one. Loss of one twin restores both roots in round one from their leaves and restores the twin in round two. Loss of $z$ leaves $x$ white until round two, because $a,b$ start with both neighbors white. In round two either twin forces $x$ after $y$ has recovered, and $z$ fills in round three. Loss of a leaf at $y$ has the symmetric argument if it is the only leaf there, and otherwise $y$ still recovers in round one. This is a certificate with $R=2$.

For the positive cases take a forcing set $B$. If some singleton loss kills, the minimum killing size is one. At budget zero the tests agree, and at every higher budget both tests allow the whole killing support to be lost. It therefore suffices to consider $B$ for which every singleton loss finishes. Such $B$ contains both twins $a,b$, and every leaf in every group with at least two leaves. Indeed, if a twin pair contains only one initially blue vertex, loss of that vertex makes the entire fort white. Every such $B$ has minimum killing size two because $\{a,b\}$ is a killing pair. It remains to compare singleton times.

- **At least two leaves on both sides.** If both roots are blue, every singleton loss completes in one round. If both roots are white, after any loss each still has a blue leaf and fills in round one. The lost nonroot fills in round two. If exactly one root is blue, loss of that root is repaired along with the other one in one round. Any nonroot loss takes exactly two rounds. The missing root fills in round one, but either the lost vertex depends on that root or its blue root sees both white vertices. Each minimum killing pair contains a nonroot in this case because only one root was initially blue.
- **Leaves on just one side, all included in $B$.** With both roots blue, all singleton losses take one round. With one root blue they all take two rounds. Loss of the blue root makes both roots white, so a leaf first forces its root and a twin then forces the leafless root. A nonroot loss leaves that vertex and the missing root white. The root is forced first, while the lost vertex either needs it or its blue neighbor sees both whites. If both roots are initially white, at least two leaves are needed for singleton recovery. One of them restores the leafy root in round one. A twin restores the leafless root in round two, and the last white vertex fills in round three. The leafy root cannot fill that last vertex in round two because the leafless root was still white at the start of the round.
- **One leaf, omitted from $B$.** When both roots are white the two twins each see two white neighbors and the coloring stalls. For singleton recovery this stall must be impossible even after one loss, so both roots must be blue initially. If a twin is lost, the leafless root restores it in round one. If a root is lost, it is restored from its blue neighbors in that round. In all cases the leaf fills in round two, since its root either was white or had two white neighbors at the start of round one.
- **No leaves.** To survive all singleton losses both roots must be blue as well as the twins. All singleton losses then take one round.

In every positive case each minimum killing pair contains a singleton whose time is the unrestricted maximum. The intact run is at least as fast by monotonicity. Budget one therefore gives the same deadlines on both sides of the property, and all other budgets follow from the minimum killing size.

Two further attachment families have uniform certificates.

- **A path of length $d\geq2$ attached at $x$.** Let $B$ contain all four core vertices and the first path vertex $z$. Put $H=\{a,b\}$. One lost twin is restored by $y$ in round one and the blue head sends a force along the tail every round. The restricted time is $d-1$. If the head is lost, $x$ must first restore it and the time is $d$. Loss of $x$ or $y$ is repaired by the core in round one and the intact head then finishes the tail. The twin pair is still a fort after the double loss. A path of length one is the positive one-leaf case above.
- **Any positive number of leaves attached at $a$.** Color every vertex except $a$ blue and take $H=\{x,y\}$, $z=b$. The roots are still twins, so their double loss kills. After one root loss, $b$ restores the lost root and a leaf restores $a$ in round one. If $b$ is lost, each root sees both $a,b$ white, so $b$ must wait until round two. Any loss of a leaf leaves a blue leaf to restore $a$ or, when it is the only leaf, leaves both roots able to force $a$. The remaining white vertex then fills. Thus the two times are one and two.

## A bouquet of any number of cycles

Let at least two cycles meet in a single common vertex $x$, with otherwise disjoint vertex sets and no other edges. The graph satisfies `EveryMinimumSupport` exactly when every cycle is a triangle.

In a bouquet of triangles, the two vertices outside $x$ in each petal form a fort. If a forcing $B$ does not contain both vertices of each petal, one singleton loss kills. Otherwise every peripheral vertex is blue. If $x$ is blue, all singleton losses take one round. If $x$ is white, an unaffected petal restores $x$ in round one and the lost peripheral vertex fills in round two. Thus all singleton times agree in each case, and a minimum killing pair is one of the petal pairs. The budgets other than one agree by the same argument as for the diamond.

If some cycle is longer than a triangle, choose that petal and any other petal. On their union use the [shared-vertex certificate](RESEARCH.md) for their two cycle lengths. In that certificate $x$ is blue initially or is forced in round one in each of the intact, restricted singleton, delayed singleton and double-loss runs. Color every new petal vertex blue. All new vertices can affect the core only by forcing $x$. In the listed runs this cannot make $x$ blue earlier because a white $x$ already fills in the first round. The remaining core moves are unchanged, since the extra neighbors at $x$ stay blue. The exact time gap and the double failure thus persist. Any other single loss on the chosen two petals still finishes since the added blue neighbors can only help its core propagation.

When an added peripheral vertex $v$ is lost, the intact old seeds remain. If $x$ starts white, its original first-round restoration uses an old vertex whose neighbors are unchanged, so the added loss cannot block it. Once $x$ is blue, $v$ is the only white vertex in its new petal and fills in the next round. The remaining old coloring contains the intact seeds, with all new vertices blue, so it completes. This yields a two-vertex certificate for any number of added petals.

## Reproduction

```sh
python -B research-bicyclic/check_theta.py
lake env lean -DwarningAsError=true research-bicyclic/ThetaSeeds.lean
```

The Python command checks the 109 theta graphs through order 15. It checks 979 shared-edge cases, including every length pair through 40 and five choices of the shorter path for each longer length through 80. It also replays 229 other theta certificates and 239 diamond certificates for parameters through 80. It exhaustively checks 21 small leaf-count pairs on the diamond and four triangle bouquets. The bouquet checker additionally replays 451 negative cases with two to five petals of lengths three through eight. The Lean command assumes the pinned core modules were built first. It checks the three finite theta examples. The parameterized results above have mathematical proofs for the indicated families.
