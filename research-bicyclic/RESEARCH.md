# Minimum killing supports in two families of bicyclic graphs

**Theorem.** Let two simple cycles of lengths $p,q\geq 3$ share exactly one vertex, or let them be disjoint and joined by a path of any positive length. The internal vertices of the path lie outside both cycles. Assume the graph has no other vertices or edges. It satisfies `EveryMinimumSupport` exactly when the two cycles are triangles sharing a vertex. In every other case there is a two-element minimum killing support whose worst singleton loss is exactly one round faster than a specified singleton loss outside that support. Every singleton loss in these certificates completes.

Use [synchronous zero forcing and minimum killing supports](../README.md#模型与定理). Write the first cycle in the order $x,a_1,\ldots,a_{p-1}$ and the second in the order $y,b_1,\ldots,b_{q-1}$. For a shared vertex $x=y$. For disjoint cycles write the connecting path as $x=t_0,t_1,\ldots,t_\ell=y$ with $\ell\geq 1$. The exterior of the first cycle consists of the vertices outside that cycle. It contains the second-cycle vertices other than a possible shared vertex, and all internal path vertices. If the exterior is blue and $x$ is white, it forces $x$ in round one. In the shared case either second-cycle neighbor of $x$ can force it. In the disjoint case $t_1$ can force it, including when $t_1=y$.

Interchange the cycles if necessary so that $p\leq q$. Every vertex outside an explicitly specified initial blue set $B$ is white. A set of white vertices stays white if every vertex outside it has zero or at least two neighbors inside it. We use this fort criterion on the double loss. A cycle with an adjacent pair of blue vertices eventually fills when all neighbors outside the cycle stay blue. This follows by advancing from the ends of blue runs. A connected graph with exactly one white vertex fills it in the next round.

For each negative case write $H$ for the killing pair and $z$ for the delayed singleton loss. If the intact coloring and both losses from $H$ finish by round $R$, the double loss stops, and all singleton losses finish including $z$ at round $R+1$, then $H$ is minimum and the property fails with budget one and deadline $R$. This implication also has a [Lean proof](../research-unicyclic/CertificateDeadline.lean).

## Two triangles sharing a vertex

Each pair of nonshared vertices in a triangle is a fort, so a forcing $B$ meets both pairs. If either pair contains exactly one blue vertex, a minimum killing support has size one. At budget zero the two tests coincide. At any higher budget and finite deadline both tests fail because both allow the loss of the entire support.

Otherwise all four nonshared vertices are blue. If $x$ is blue, every singleton loss finishes in one round. If $x$ is white, loss of any nonshared vertex leaves the other triangle's two nonshared vertices able to force $x$ in round one. The lost vertex then fills in round two and cannot fill in round one because its mate sees two white neighbors. In either coloring every singleton loss finishes, and removing both members of a triangle's nonshared pair kills. Thus the minimum killing size is two. The worst singleton time is independent of the vertex lost, so budget one gives the same answer for every minimum support. Budgets zero and at least two are settled as above.

## Shorter cycle of length at least six

In either graph, color the exterior blue. On the first cycle color $a_1,a_2,a_3$ blue, and also color $a_5$ blue when $p$ is odd. Take $H=\{a_1,a_3\}$ and $z=a_2$.

After the double loss, the initially white nonroot vertices of the first cycle form a fort. The blue $a_2$, and $a_5$ if present, each has two neighbors in the fort. Both first-cycle neighbors of $x$ are in the fort. The second cycle has no neighbors in the fort other than through $x$.

For each of the three compared singleton losses, the exterior restores $x$ in round one. Loss of $a_3$ restores $a_3$ in round one via $a_2$. Loss of $a_1$ restores $a_1$ and colors $a_4$ in round one, so the blue set at that time contains the blue set for loss of $a_3$. The intact coloring finishes at least as fast by monotonicity. It suffices to compare the loss of $a_3$ with the loss of $a_2$.

If $p$ is even, the white interval $a_4,\ldots,a_{p-1}$ has even length $L=p-4$. After losing $a_3$, both ends begin advancing in round two, so the interval fills in round $R=1+L/2$. After losing $a_2$, the interval starts filling from $x$ in round two. In that round $a_1$ restores $a_2$, and the other end starts filling in round three if the interval still has any white vertices. At round $R$ the two advances have covered $L-1$ vertices. The interval finishes one round later.

If $p$ is odd, the terminal white interval $a_6,\ldots,a_{p-1}$ has odd length $M=p-6$. After losing $a_3$, $a_3$ restores $a_4$ in round two, so $a_5$ can start advancing into this interval in round three. The other end starts advancing from $x$ in round two. Completion is in round $R=(M+3)/2$. After losing $a_2$, it is restored in round two, $a_4$ is restored in round three, and the advance from $a_5$ starts in round four if the interval is still unfinished. The advance from $x$ still begins in round two. If $M\geq 3$, there is one white vertex in that interval after round $R$, and completion is in round $R+1$. For $M=1$ the interval itself fills in round two in both runs, while $a_4$ waits until round three after losing $a_2$.

Any other singleton loss retains $a_1,a_2,a_3$. The first vertex forces $x$ and the run advances from $a_3$ through the first cycle, regardless of progress in the exterior. After the first cycle is full, there is at most one white vertex in the exterior, which fills by connectivity.

## Shorter cycle of length four

In either graph let $B$ consist of the exterior together with $x,a_1,a_3$. Take $H=\{a_1,a_3\}$ and $z=x$. The three nonroot vertices of the square form a fort after the double loss. After either loss in $H$, the remaining nonroot blue vertex forces $a_2$ and $x$ restores the lost vertex, both in round one. If $x$ is lost, the exterior restores it in round one, and $a_2$ must wait until round two. For a singleton loss in the exterior, one of $a_1,a_3$ fills $a_2$ in round one and the sole remaining white vertex then fills.

## Shorter cycle of length five

For a shared vertex take $B$ to be all vertices except $a_4,b_{q-2}$. Let $H=\{a_1,a_2\}$ and $z=b_{q-1}$. After the double loss, $\{a_1,a_2,a_4\}$ is a fort. A loss of $a_1$ is repaired by $a_2$ as $a_3$ forces $a_4$. A loss of $a_2$ is repaired by $a_1$ as $x$ forces $a_4$. The second cycle can fill $b_{q-2}$ in round one in both cases. After losing $z$, $x$ sees two white neighbors, $z$ and $a_4$. Neither neighbor of $z$ can force it in round one. The retained predecessor pair $b_{q-4},b_{q-3}$ supplies the force into $b_{q-2}$, and $a_3$ fills $a_4$. The only remaining white vertex is $z$, which fills in round two.

After loss of $x$, $a_1$ restores it and $a_3$ fills $a_4$ in round one. After loss of $a_3$, $a_2$ restores it and $x$ fills $a_4$ in round one. For any loss on the second cycle other than $x$, the disjoint blue pairs $\{b_{q-4},b_{q-3}\}$ and $\{b_{q-1},x\}$ can each independently supply a force into $b_{q-2}$, so at least one force remains. Loss of $x$ leaves the first of these forces available. In the second-cycle loss cases $a_3$ fills $a_4$ and the sole remaining white vertex is restored in round two.

For a bridge take $B=\{a_1,a_2,a_3\}\cup\{y,b_1,\ldots,b_{q-2}\}$, $H=\{a_1,a_3\}$, and $z=a_2$. The double loss leaves $\{a_1,a_3,a_4\}$ as a fort. In the compared singletons $b_{q-2}$ fills $b_{q-1}$ in round one. After loss of $a_1$, $a_2$ restores $a_1$ and $a_3$ fills $a_4$ in round one, so $x$ fills in round two. After loss of $a_3$, $a_2$ restores $a_3$ while $a_1$ fills $x$, and $a_4$ fills in round two. After loss of $a_2$, no first-cycle vertex fills in round one because $a_1,a_3,y$ each see two white neighbors. In round two $y$ fills $x$, and in round three $a_1$ and $x$ fill $a_2,a_4$. In any other singleton loss the first cycle fills in round one. The originally blue run $b_0=y,b_1,\ldots,b_{q-2}$ contains at least four vertices, so one loss leaves a blue edge and the second cycle eventually fills with $x$ blue.

For a path of length $\ell\geq 2$, color every vertex blue except $a_4$ and $t_2$. Take $H=\{a_1,a_2\}$ and $z=t_1$. After the double loss $\{a_1,a_2,a_4\}$ is a fort. If $a_1$ is lost, $a_2$ restores it and $a_3$ fills $a_4$. If $a_2$ is lost, $a_1$ restores it and $x$ fills $a_4$. In each case $t_1$ fills $t_2$ in round one because $x$ is blue. After loss of $t_1$, $x$ sees both $a_4$ and $t_1$ white, and the other neighbor $t_2$ of $t_1$ is white. Thus $t_1$ cannot be restored in round one. In that round $a_3$ fills $a_4$, and $t_2$ fills from $t_3$ if $\ell\geq 3$, or from a cycle neighbor of $y=t_2$ if $\ell=2$. The blue $t_3$ has every neighbor except $t_2$ blue, including when $t_3=y$. The sole remaining white vertex $t_1$ fills in round two.

After loss of $a_3$, $a_2$ restores it, $x$ fills $a_4$, and $t_1$ fills $t_2$, all in round one. After loss of $x$, $a_1$ restores $x$, $a_3$ fills $a_4$, and $t_2$ fills independently from the side away from $x$. Any remaining singleton loss retains $a_2,a_3,x,t_1$. These vertices fill $a_4,t_2$ by round one. The lost vertex is then the only possible white vertex and fills by connectivity.

## Shorter cycle a triangle

In each case $H=\{a_1,a_2\}$ is a fort. Both its vertices and $x$ are initially blue, so either singleton loss from $H$ is restored in round one by its mate. For each construction below the second cycle also fills in round one after either such loss. The delayed singleton finishes in round two.

For disjoint cycles, color all internal path vertices blue in addition to the specified cycle vertices. In the delayed cases that require $y$ to be filled from the path, $t_{\ell-1}$ can force it. At $\ell=1$ this is $x$, whose triangle is all blue under those losses. For larger $\ell$, the other neighbor $t_{\ell-2}$ is blue. If an internal path vertex is itself the singleton loss, both cycles finish in round one using only cycle edges. The sole remaining white vertex then fills by connectivity.

- **Shared vertex and $q=4$.** Color all vertices except $b_2$ blue. After either loss from $H$, $b_1$ and $b_3$ fill $b_2$ using the blue shared vertex $x$. If $z=x$ is lost, the triangle restores it in round one but both neighbors of $b_2$ are blocked in that round. A loss at $b_1$ or $b_3$ leaves the other force into $b_2$ available.
- **Shared vertex and $q\geq5$.** Color all vertices except $b_2,b_3$ blue. After either loss from $H$, the forces from $b_1,b_4$ fill $b_2,b_3$ in round one. If $z=b_1$ is lost, neither neighbor of $b_2$ can fill it in round one. In that round $x$ restores $b_1$ and $b_4$ fills $b_3$. If $x$ is lost, the triangle restores it in round one and both boundary forces are available in round two. For every other loss on the second cycle, at least one adjacent blue pair survives. The two candidate pairs are $\{x,b_1\}$ and the edge from $b_4$ to its neighbor other than $b_3$. Their only possible common vertex is $x$. With both $a_1,a_2$ blue, that adjacent pair suffices to fill the second cycle.
- **Disjoint cycles and $q=3$.** Color every vertex except $y$ blue. The pair $b_1,b_2$ restores $y$ independently of either loss from $H$. If $z=b_1$ is lost, the path fills $y$ in round one, then $b_1$ is restored in round two. Loss of $b_2$ is symmetric. If $x$ is lost, both triangles recover their roots from their nonroot blue pairs in round one.
- **Disjoint cycles and $q=4$.** Color every vertex except $b_2$ blue. The blue $y$ lets $b_1,b_3$ fill $b_2$ in round one after either loss from $H$. If $z=y$ is lost, the path restores it in round one and $b_2$ must wait until round two. Loss of $x$ is restored by its triangle and leaves the force into $b_2$ available. Loss of $b_1$ or $b_3$ leaves the other force into $b_2$ available.
- **Disjoint cycles and $q\geq5$.** Color all of the first cycle and $b_1,\ldots,b_{q-2}$ blue. After either loss from $H$, the ends of the blue run fill $y,b_{q-1}$ in round one. If $z=b_{q-2}$ is lost, both neighbors of $b_{q-1}$ start white. In round one the path or $b_1$ fills $y$ and $b_{q-3}$ restores $z$. Then $b_{q-1}$ is the only white vertex and fills in round two. If $x$ is lost, its triangle restores it in round one while the second cycle fills from the ends of its blue run. For any other loss in the second cycle, the path fills $y$ in round one. The second cycle then has the blue edge $yb_1$ unless $b_1$ was lost, in which case $b_2b_3$ is blue. Either edge suffices because $t_{\ell-1}$ stays blue.

## Reproduction

```sh
python -B research-bicyclic/check_two_cycles.py --max-cycle 40 --max-path 12
```

The command checks 9,633 graphs with cycle lengths between 3 and 40, including path lengths from 1 to 12. It exhausts the 14 forcing sets and 36 minimum supports of the two triangles sharing a vertex. For each other graph it verifies all singleton losses, the failing double loss, and the exact restricted and delayed times. The arguments above apply to all cycle and path lengths. For related work on minimum-cardinality fault-tolerant sets, see [Fault Tolerant Zero Forcing](https://arxiv.org/abs/2509.07854).

[Bowtie.lean](Bowtie.lean) proves `bowtie_every_minimum_support` by kernel reduction against the existing finite decision theorem. The Lean proof covers the positive graph. The parametric exclusions are proved above. Run the following command from a checkout with the pinned Lean dependencies and core modules built.

```sh
lake env lean -DwarningAsError=true research-bicyclic/Bowtie.lean
```
