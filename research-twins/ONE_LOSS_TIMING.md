# Sharp single-loss recovery bounds for one-round colorings

Use synchronous zero forcing, with a loss turning an initially blue vertex back to white. Write $T(B)$ for the number of rounds to completion from $B$, with infinity for a stalled run. See the [model and deadline property](../README.md#模型与定理).

**Theorem.** If $T(B)\leq1$ and $T(B\setminus\{z\})$ is finite, then $T(B\setminus\{z\})\leq5$. If some other initially blue vertex has the same initially white neighbors as $z$, then the upper bound is four. This includes loss of one member of an initially blue twin pair. Both bounds are attained by graphs that recover from every singleton loss and have a two-vertex minimum killing support whose restricted worst time is one.

In contrast, even with recovery from every singleton loss and a two-vertex minimum killing support, restricted time two allows an arbitrarily large finite unrestricted time. The examples below have intact time exactly two as well. The lost vertex can have a retained blue twin, either adjacent or nonadjacent.

## Upper bounds

Let $W=V\setminus B$ be the intact white set. For each $w\in W$, an original source is an initially blue vertex whose only neighbor in $W$ is $w$. There is at least one original source for every $w$ because the intact coloring finishes within one round. A vertex can be an original source for at most one $w$.

Run the process with $z$ lost. Suppose $w$ is still white after the first round and it has an original source $v\ne z$. The vertex $v$ must be adjacent to $z$, since otherwise it would still have forced $w$ in round one. If $w$ later turns blue before $z$, the source $v$ then sees only $z$ white. All its neighbors other than $w,z$ were already blue at the start. Thus $v$ restores $z$ in the next round. The sole possible exception among the initially white vertices is the one that had $z$ as its only original source.

If $z$ is still white after round four, the successful run must have added some vertex in each of rounds two and three. A round that changes nothing is a fixed point. These two new vertices are distinct, and neither is $z$, so at least one has an original source other than $z$. Its restoration then restores $z$ by round four, a contradiction. Once $z$ is blue the color set contains $B$, so at most one additional round is needed. This gives five.

If a different blue vertex has the same neighbors in $W$ as $z$, every $w$ has an original source other than $z$. If $z$ is still white after round three, a new vertex in round two forces it to return in round three by the same argument. This gives four. Both bounds are verified in [SingleLossBound.lean](SingleLossBound.lean).

## Sharp examples with restricted time one

Each capital label in these constructions denotes an independent pair of vertices. An edge between two labels denotes all edges between their vertices. Lowercase labels denote single vertices. The listed edges are exhaustive. In each construction the two vertices of $A$ are twins, so their double loss is a fort. The pair $P$ repairs a singleton loss from $A$ in round one, and the retained member of $A$ fills its initially white neighbor in that same round.

**Five rounds.** Use white vertices $x_0,x_1,x_2,x_3$, a blue vertex $z$, and blue pairs $A,P,U,D_2,D_3$. Put in the edges

$$
x_0x_1,\ x_1x_2,\ zx_1,\ Ax_0,\ AP,\ Ux_1,\ Ux_2,\ D_2x_2,\ D_2z,\ D_3x_3,\ D_3z.
$$

The four white vertices fill in one round from $A,z,D_2,D_3$, respectively, also after either loss in $H=A$. Losing $z$ gives the five successive new blue vertices $x_0,x_1,x_2,z,x_3$. The advance from $x_0$ fills $x_1$, and $U$ then fills $x_2$. The pair $D_2$ can only restore $z$ after $x_2$ is blue. The vertex $x_1$ also cannot restore $z$ any sooner because $x_2$ remains white until round three. The restoration of $z$ frees $D_3$ to finish the run in round five.

Loss in $U$ leaves all four original forces available, after which the sole missing vertex fills. If one member of $D_2$ or $D_3$ is lost, its mate keeps the corresponding original force. The pair $U$ then fills the still-white $x_1$ in round two, and $z$ repairs the lost vertex in round three. If a member of $P$ is lost, $x_1,x_2,x_3$ still fill in round one. The vertex $x_1$ fills $x_0$ next, and $A$ repairs $P$. Thus all singleton losses recover.

**Four rounds with a retained twin.** Use white vertices $x_1,x_2,x_3$ and blue pairs $A,P,Z,D_2,D_3$. Put in the edges

$$
x_1x_2,\ Ax_1,\ AP,\ D_2x_2,\ D_2Z,\ D_3x_3,\ D_3Z.
$$

The intact and $A$-restricted runs finish in round one from $A,D_2,D_3$. Loss of either member of $Z$ gives the successive new blue vertices $x_1,x_2$, the lost member of $Z$, and $x_3$. The pair $D_2$ forces the lost member of $Z$ after $x_2$ is blue, freeing $D_3$. A singleton loss in $D_2$ or $D_3$ retains the three sources for the original whites and leaves just one white after round one. Loss in $P$ leaves $x_1$ until $x_2$ can force it in round two, after which $A$ can repair $P$. All singleton losses recover, and the usual pair $A$ is minimum.

## Restricted time two and unbounded recovery

Fix an integer $n\geq2$. Start with a white path $w_1,\ldots,w_n,g$ and a blue vertex $z$ adjacent to $g$. Add blue independent pairs $A,P$ with edges $Aw_1$ and $AP$. For each $i=2,\ldots,n$, add blue independent pairs $D_i,E_i$ with edges $D_iw_i$, $D_ig$, $D_iz$ and $D_iE_i$. All edges are exactly those specified, including the path edges. Set $H=A$.

In the intact run and after either singleton loss from $A$, the pairs $A,P$ handle $w_1$ and any lost member of $A$ in round one. The vertex $z$ fills $g$ in that round. Each $D_i$ then fills $w_i$ in round two. There is a white $w_i$ after round one, since the path and its sources cannot fill it that early, so the restricted time is exactly two. The pair $A$ still kills on a double loss.

When $z$ is lost, all the $D_i$ see both $z$ and $g$ white. They cannot force any vertex before $g$ is restored. The path therefore fills one vertex at a time from $w_1$. In round $n+1$ the path reaches $g$. Only then can $z$ be forced, in round $n+2$. This yields the unbounded difference $n$.

The remaining singleton losses all recover. A loss from $D_i$ is repaired by $E_i$ in the first round, restoring every intact seed. A loss from $E_i$ leaves $w_i$ white after round two, while the other path vertices and $g$ have filled by then. The preceding vertex on the path fills $w_i$ in round three, then $D_i$ repairs $E_i$. A loss in $P$ keeps $w_1$ white in round one. The vertex $w_2$ fills in round two and then fills $w_1$, allowing $A$ to repair $P$. Hence $A$ is a minimum killing support in every member of the family.

For an adjacent blue twin, add $z'$ adjacent to $z$ and its other neighbors. It leaves the intact and $A$-restricted times unchanged because its white neighbors agree with those of $z$. After loss of $z$, the retained $z'$ sees both $z$ and $g$ white until the path reaches $g$. Thus the delayed time is still $n+2$. Loss of $z'$ is symmetric, and any other singleton loss still completes because an additional blue vertex does not obstruct existing forces.

For a nonadjacent blue twin, replace $z$ by a blue independent pair $Z$. Remove the edge to $g$ and put in a blue independent pair $C$ joined precisely to $Z$ and $g$. The pair $C$ now restores $g$ in round one in the intact and restricted runs. When a vertex of $Z$ is lost, $C$ and each $D_i$ see both that lost vertex and $g$ white. The other vertex of $Z$ has no white neighbor. The path therefore still fills one vertex per round, then $C$ restores the lost vertex in round $n+2$. Loss of a member of $C$ leaves its mate to restore $g$. The blue $Z$ can restore the missing $C$ in round one. All other singleton losses recover by the preceding arguments with $C$ supplying the force into $g$.

## A bound from the neighborhood of the lost vertex

For arbitrary finite intact time $t$ and finite recovery, let $N_{\leq 2t}(z)$ be the vertices at distance at most $2t$ from the lost vertex, including $z$. Then

$$
T(B\setminus\{z\})\leq t+|N_{\leq 2t}(z)|.
$$

The next-round color of a vertex depends only on the current colors within distance two. Each possible source is a neighbor, and its eligibility depends on the colors of its neighbors. The two runs differ only at $z$ at round zero. Therefore by induction they agree outside the radius-$2i$ neighborhood of $z$ after round $i$. At round $t$ the intact run is full, so every remaining white in the delayed run lies in the stated neighborhood. The delayed run eventually finishes, hence every unfinished round colors at least one of these remaining vertices.

For maximum degree $\Delta\geq2$, the number of vertices in the radius-$2t$ neighborhood is at most $1+\Delta\sum_{j=0}^{2t-1}(\Delta-1)^j$. Thus at fixed intact time an unbounded delay requires unbounded neighborhoods of the lost vertices. For example, maximum degree three and intact time at most two imply recovery by round 48 whenever it occurs.

## A sharper maximum-degree bound

Let $D_i$ consist of the vertices blue in the intact run and white in the delayed run after round $i$. Monotonicity gives inclusion of the delayed coloring in the intact one. For every round,

$$
|D_{i+1}|\leq\sum_{w\in D_i}\deg(w)+\mathbf{1}_{z\in D_i}.
$$

To see this, take a new discrepancy at $u\in D_{i+1}\setminus D_i$. It had to be white in the intact run at round $i$, since otherwise it was already blue in both. Choose one intact source $v$ that forces $u$. Attribute this new discrepancy to $v$ itself if $v\in D_i$. Otherwise $v$ is blue in both runs, and the force is blocked in the delayed run by an additional white neighbor $w\in D_i$. Attribute it to one such $w$. A source forces at most one target, so each vertex $w\in D_i$ receives at most one attribution from itself and one from each of its neighbors. If $w$ itself forces, one of its neighbors is the intact white target and cannot be a source, so at most $\deg(w)$ new discrepancies are attributed to $w$.

When $w\ne z$, it was originally white and had to be forced in the intact run in an earlier round. The earlier source is a neighbor of $w$ with no white neighbors left in the intact run. It remains blue without any white neighbors and cannot generate a new discrepancy. This removes one more potential attribution, even if $w$ itself is a source, because that earlier source and $w$'s intact white target are distinct. Hence at most $\deg(w)-1$ new discrepancies are attributed to such a $w$. Adding at most $|D_i|$ retained discrepancies gives the inequality.

Since $D_0=\{z\}$, the bound implies $|D_t|\leq\sum_{j=0}^{t}\Delta^j$. At the intact completion time all whites of the delayed run are in $D_t$, so finite recovery obeys

$$
T(B\setminus\{z\})\leq t+\sum_{j=0}^{t}\Delta^j.
$$

For maximum degree three and intact time at most two, this gives 15 rounds. The next argument lowers this bound by counting which round-one sources can still act in round two.

## Two-round colorings at bounded degree

**Theorem.** Let the maximum degree be $\Delta\geq1$ and let the intact coloring finish by round two. If the delayed run finishes, it does so within $\Delta^2+3$ rounds. For maximum degree at most three the sharp bound is **nine rounds**. The subcubic proof uses a finite enumeration when eight, nine or ten vertices remain white at the end of round two.

Write $m=|D_1\setminus\{z\}|$. For each of these $m$ missed targets, choose an intact round-one source. If $z$ forced a missed target, choose $z$ as its source and call that target $w_0$. Every other chosen source is an initially blue neighbor of $z$. The chosen sources are distinct and have no white neighbors in the intact run after round one. Counting these neighbors of $z$, together with $w_0$ if present, gives $m\leq\Delta$.

If $z\notin D_1$, the delayed coloring after round one contains the entire intact initial blue set. By monotonicity, the delayed coloring after round two contains the intact coloring after round one, so every discrepancy in $D_2$ is new. Each of the $m$ vertices of $D_1$ accounts for at most $\Delta-1$ new discrepancies by the preceding attribution argument. Thus $|D_2|\leq m(\Delta-1)$.

If $z\in D_1$, at most $\Delta-m$ new discrepancies can be attributed to $z$. When $z$ was not chosen as a round-one source, the $m$ chosen neighbors are unavailable in round two. If $z$ itself acts in round two, its still-white target is an additional neighbor unavailable as a source, accounting for $z$'s own attribution. When $z$ was chosen in round one, it can no longer act, and the $m-1$ chosen neighbors are again unavailable. The neighbor $w_0$ is in $D_1$, so any force from $w_0$ is attributed to $w_0$ itself. In either case, counting retained and new discrepancies gives

$$
|D_2|\leq 1+m+(\Delta-m)+m(\Delta-1)
       =1+\Delta+m(\Delta-1)
       \leq 1+\Delta^2.
$$

At round two the intact coloring is full. Every subsequent round of a finite delayed run colors at least one of the remaining whites, so it finishes by round $\Delta^2+3$.

### A finite reduction for eight to ten whites

Let $k=|D_2|$. If $k\leq7$, a successful run finishes by round nine by adding at least one vertex per unfinished round. For $k\geq8$ in a subcubic graph, the preceding count gives $z\in D_1$ and $m\in\{2,3\}$. Use the same round-one sources and round-two attributions as above. Call the vertices of $D_1$ old, and the vertices of $D_2\setminus D_1$ new. All old and new vertices are white in the delayed run at time one.

The replay builds a small graph on the old and new vertices and records each relevant outside blue vertex by its set of neighbors in that graph. In later rounds, an outside vertex forces the sole remaining white in its set if one exists. An old or new vertex can act once it is blue, using its edges inside the small graph. This preserves the evolution after round two because every outside vertex is blue from then on.

**Required edges and sources.** Each missed round-one target uses one edge to its chosen predecessor. If that predecessor is $z$, the edge is internal. Otherwise the predecessor is permanently blue and contributes the set $\{z,w\}$, where $w$ is its target. Its other neighbors were already blue initially. These choices use $m$ edges at $z$ and one at each other old vertex.

For each new target, use the distinct intact round-two source chosen in the attribution. Each old vertex other than $z$ has at most two new targets associated with it, and at most one can be forced directly by that vertex. The others are forced by outside sources blue after round one in both runs. Such a source is adjacent to its new target and the old vertex that blocks it. It can also be adjacent to one other old vertex, as long as there is an unused edge there. No second new vertex can be its neighbor because its own target was its unique white neighbor at intact time one. A direct force gives a direct edge between the old and new vertices. Either type of source spends one edge at the old vertex and one at the new target.

The lost vertex can receive at most $3-m$ new attributions. For $m=3$ it receives none. For $m=2$, a new attribution to $z$ must use an outside source. If $z$ acted in round one it is already inactive. Otherwise the two chosen predecessors are initially blue neighbors of $z$, and if its third neighbor were an intact round-two white target then $z$ would already have forced it in round one.

**Vertices restored in round two.** If an old vertex returns by round two, it must have been forced from outside the small graph. The prescribed round-one and round-two outside sources are blocked at time one by at least two white neighbors. The restoring source therefore uses another edge at the restored vertex. It sees no other old or new vertex, since they were all still white at time one. The replay reserves one such edge and starts that old vertex blue. Other edges to it can contribute to the later runs.

**Remaining edges.** The replay fills the available degree slots with optional edges within the small graph and optional outside blue sources with one to three white neighbors at time two. It allows an extra old neighbor for each chosen outside round-two source as described above. Neighbors already blue at time two can be dropped from outside source sets. Edges between blue vertices and duplicate outside source sets have no effect on future forces. The allowed configurations include every actual residual process and can also include configurations without a realizing intact run.

Up to permutation of the missed round-one targets that share the same type of predecessor, the replay considers the following configurations. It skips runs that cannot start, and for eight or nine whites it stops evaluating a run once the elapsed rounds plus the remaining white count is below seven.

| Whites after round two | Templates | Configurations evaluated | Finishing runs with at least seven further rounds | Maximum further rounds |
| ---: | ---: | ---: | ---: | ---: |
| 10 | 10 | 6,176,870 | 0 | 6 |
| 9 | 20 | 5,390,980 | 0 | At most 6 |
| 8 | 57 | 3,470,951 | 1,168 | 7 |

Thus the global subcubic upper bound is nine rounds. When nine or ten vertices are still white after round two, the bound is eight. A 24-vertex witness in the [example replay](check_single_loss_bounds.py) attains eight rounds with ten whites, while recovering from every singleton loss and having restricted time two.

### Sharp nine-round witness

A connected 19-vertex graph in the [example replay](check_single_loss_bounds.py) attains the global bound. The initial blue set is $\{0,8,9,10,11,13,15,16,17,18\}$. Its intact time is two and its minimum killing support $\{17,18\}$ has restricted time two. Without initial blue vertex $0$, the successive additions are $\{14\},\{12\},\{5\},\{7\},\{4\},\{1\},\{0,2\},\{3\},\{6\}$. The replay checks that every singleton loss recovers and the two-vertex support loss stalls.

## Reproduction

```sh
python -B research-twins/check_single_loss_bounds.py
python -B research-twins/check_saturated_subcubic.py
lake env lean -DwarningAsError=true research-twins/SingleLossBound.lean
```

The replay verifies both sharp examples and 147 instances of the unbounded family, using 49 path lengths and three variants of the lost vertex. The largest path has 100 vertices before $g$. It also checks 25,392 recoverable singleton cases with intact time at most one across all labeled simple graphs through order five. In 7,914 of those cases a blue twin of the lost vertex remains. On the same small graph range, the replay checks the degree-weighted inequality on 78,122 transitions and the refined round-two count on 51,658 singleton losses, including stalled runs. Separate subcubic certificates attain eight rounds with ten white vertices and nine rounds with eight white vertices after round two. The Lean proof establishes the one-round upper bounds without a graph-order restriction.
