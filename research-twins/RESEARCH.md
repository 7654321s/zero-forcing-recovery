# Truncating twin classes in synchronous zero forcing

Let $G$ be a finite nonempty simple graph. Two vertices are twins if they have the same neighbors outside their pair. This includes adjacent twins and nonadjacent twins. The relation, with equality included, partitions the vertex set. Indeed, for three distinct vertices on two successive twin pairs, their three mutual adjacency bits are equal. Their adjacency agrees at all other vertices as well. Each class is therefore a clique or an independent set, with a uniform neighborhood outside the class. A pair of twins is a fort, since any outside vertex has zero or two neighbors in the pair. We use the [initial-color loss model](../README.md#模型与定理) and the [fort criterion](https://arxiv.org/html/2509.07854v4#S2).

## Twin truncation theorem

**Theorem.** Keep one vertex of every singleton twin class and any two vertices of each larger class. The induced graph on the retained vertices satisfies `EveryMinimumSupport` exactly when $G$ does. A budget-one counterexample with a two-element minimum killing support and finite recovery under every singleton loss transfers in both directions, preserving its restricted and delayed times.

If every class is a singleton, there is nothing to reduce. Otherwise consider an initial forcing set. If a singleton loss kills, a minimum killing support has size one. The budget-zero comparisons agree, and at any higher budget both comparison domains contain a killing loss. Thus only forcing sets that survive every singleton loss matter. They include every vertex of each repeated twin class. Two initially white members already form a white fort. With just one missing member, losing any other member creates a white fort. In a singleton-tolerant set a pair from a repeated class kills, so the minimum killing size is two. Budget one is the only budget left to compare.

Corresponding initial sets on the two graphs have the same colors at singleton classes and have all repeated-class vertices blue. After deleting at most one retained vertex per repeated class, all discarded vertices and at least one retained representative of each discarded vertex's class are still blue. For any white target, a discarded blue source has the same white neighborhood as that retained blue representative. This remains true when they are adjacent, since both are blue. Every white vertex is retained, so removing edges incident to discarded vertices leaves the old sources' white-neighbor counts unchanged. Exactly the same white vertices fill in the next round. The blue representatives remain blue throughout, so induction gives equality in every round. In particular the exact completion time, including noncompletion, is unchanged. [TwinProjection.lean](TwinProjection.lean) verifies this round projection by isolating the discarded blue vertices in the ambient graph. The same file checks that an initially white twin pair stays white in every round.

Permuting any twin class is a graph automorphism. A singleton loss at a discarded vertex can therefore be moved to a retained vertex of the same class. This proves correspondence of singleton tolerance and of all distinct singleton completion times. For double losses that use at most one vertex per class, the same permutation puts the loss in the retained graph and the projection applies. A double loss within one class kills on both sides by the fort criterion. Thus every minimum killing pair in either graph corresponds to one in the other, with matching restricted singleton times. The unrestricted worst singleton time and the intact time also match. This proves the deadline equivalence and the claimed preservation of counterexamples.

In particular, truncating only a chosen collection of repeated classes gives the same result. The proof applies verbatim with all other vertices kept. The [pendant-leaf reduction](../research-bicyclic/LEAF_MULTIPLICITIES.md) is the case of sibling leaves.

## Checking graphs with few singleton classes

Suppose at least one twin class is repeated, and let $s$ be the number of singleton classes. After truncation there are at most $2^s$ relevant initial sets. For each one, check the intact run and every singleton loss. When these all finish, test pairs for failure and compare the two restricted singleton times with the unrestricted maximum. No larger support or budget is needed. Since there are at most $s+1$ whites after a singleton loss, a finite singleton run takes at most $s+1$ rounds. Every minimum pair admits a singleton loss with time at least one. Thus any strict difference between the worst singleton times is at most $s$ rounds.

An isolated vertex makes the full property automatic. Every forcing set contains that vertex, and its singleton loss kills. If there are no singleton twin classes, every singleton-tolerant set is the full vertex set. In the absence of isolated vertices all its singleton losses take one round, so the property holds.

The gap can still grow without bound in graphs that contain twins. In the [shared-edge family $\Theta(1,2,r)$](../research-bicyclic/NEARBY_FAMILIES.md#two-cycles-sharing-an-edge), the endpoint $x$ is blue and belongs to neither the killing pair nor the slow loss for $r\geq5$. Add a nonadjacent twin of $x$ and color it blue. All compared runs, including the double loss, keep $x$ as a blue representative, so their times are unchanged by the projection. Old singleton losses still finish by monotonicity, and losing the new twin is equivalent to losing $x$ in the enlarged graph. The same certificate therefore exhibits a gap of $\lfloor(r+1)/4\rfloor$ on graphs with a twin pair.

[Sharp single-loss time bounds](ONE_LOSS_TIMING.md) give five rounds when the intact time is one, and nine rounds for subcubic graphs when the intact time is at most two. For intact time at most two, the sharp worst-case recovery times are 15 at maximum degree four, 19 at degree five, and $\lfloor d^2/2\rfloor+6$ for every $d\geq6$. Without a degree bound, intact time two allows arbitrarily large finite recovery times.

[Longer intact runs](ONE_LOSS_TIMING.md#more-than-two-intact-rounds) have sharp exponential base $d-1$ for fixed maximum degree $d\geq3$. Their worst finite recovery time divided by $d(d-1)^{t-1}$ approaches $1/2$ as $d$ grows, uniformly over intact deadlines $t\geq3$. At maximum degree two the exact time is $3t+1$. [The two-term expansion](ONE_LOSS_TIMING.md#the-first-two-asymptotic-terms) gives $d^t/2-(t-2)d^{t-1}/2+O_t(d^{t-2})$ for each fixed $t\geq3$.

[Several lost seeds](MULTIPLE_LOSS_TIMING.md) have exact worst-case time $t+k(2t+1)$ in degree two. [One intact round](MULTIPLE_LOSS_TIMING.md#exact-values-for-one-intact-round) has exact worst-case values for every positive maximum degree cap and loss budget. The [two-round finite bounds](MULTIPLE_LOSS_TIMING.md#finite-bounds-for-two-intact-rounds) give the exact value $2+13k$ at degree four and differ by at most $2k$ rounds for higher degrees. For $t\geq2$, the first two asymptotic terms scale with $k$, even for connected graphs that recover from every loss of at most $k$ seeds.

## Exactly one vertex without a twin

Suppose $G$ has no isolated vertex and exactly one vertex $x$ without a twin. For each $v\ne x$, compare the neighborhoods of $x$ and $v$ after excluding both $x$ and $v$. Then `EveryMinimumSupport` holds exactly when all these pairs are comparable by inclusion, or all are incomparable.

The singleton-tolerant initial sets can only be the full set and the full set except $x$. The full set has singleton time one for every loss. Starting from all vertices except $x$, a singleton loss at $v$ leaves precisely $x,v$ white. Their exterior neighborhoods differ because they are not twins. At least one fills in the first round, and the other then fills because it has a neighbor. Both fill in the first round exactly when each has an outside neighbor not adjacent to the other. That is exactly incomparability. Hence every singleton loss takes either one or two rounds according to the stated comparison. If some losses are fast and others slow, choose a fast vertex and one of its twins. They give a minimum killing pair with restricted time one, because the two fast singleton times agree by the twin swap. The unrestricted time is two. Conversely, when the singleton times all agree, every minimum pair sees the same worst time.

For an explicit negative example, take vertices $x,a_1,a_2,b_1,b_2$. Put in all edges from $\{a_1,a_2\}$ to $\{x,b_1,b_2\}$, and the edge $b_1b_2$. Start with $x$ white and every other vertex blue. Loss of either $a_i$ finishes in one round. Loss of $b_1$ takes two because $b_2$ restores $b_1$ first and the two $a_i$ can then restore $x$. The minimum killing pair is $\{a_1,a_2\}$.

## Complete multipartite graphs

**Corollary.** Every finite nonempty complete multipartite graph satisfies `EveryMinimumSupport`.

There is nothing to check beyond killing singletons for an edgeless graph. Otherwise each part of size at least two consists of nonadjacent twins, and vertices in singleton parts are universal. If there are at least two universal vertices they are all twins, so there is no vertex without a twin. If there is exactly one universal vertex, its exterior neighborhood contains every other exterior neighborhood, so the preceding criterion applies. If there are no singleton parts the full set is the only singleton-tolerant set.

## Reproduction

```sh
python -B research-twins/check_twin_truncation.py
lake env lean -DwarningAsError=true research-twins/TwinProjection.lean
```

The Python script compares the exact property on 1,258 generated blowups and their twin-truncated graphs, using both cliques and independent sets as replacement classes. It compares exact completion on 22,068 projected loss states and replays all 72 lifted counterexamples. It independently compares the one-singleton criterion on 226 generated instances and checks 52 complete multipartite instances. The Lean command uses the pinned, built core modules and prints the axiom audit of the projection.
