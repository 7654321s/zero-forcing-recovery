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

**Theorem.** Let the maximum degree be $\Delta\geq1$ and let the intact coloring finish by round two. If the delayed run finishes, it does so within $\Delta^2+3$ rounds. For maximum degree at most three the sharp bound is **nine rounds**. Every nine-round run in this class has exactly eight white vertices after its second round. The subcubic proof uses a finite enumeration for seven to ten remaining whites.

Write $m=|D_1\setminus\{z\}|$. For each of these $m$ missed targets, choose an intact round-one source. If $z$ forced a missed target, choose $z$ as its source and call that target $w_0$. Every other chosen source is an initially blue neighbor of $z$. The chosen sources are distinct and have no white neighbors in the intact run after round one. Counting these neighbors of $z$, together with $w_0$ if present, gives $m\leq\Delta$.

If $z\notin D_1$, the delayed coloring after round one contains the entire intact initial blue set. By monotonicity, the delayed coloring after round two contains the intact coloring after round one, so every discrepancy in $D_2$ is new. Each of the $m$ vertices of $D_1$ accounts for at most $\Delta-1$ new discrepancies by the preceding attribution argument. Thus $|D_2|\leq m(\Delta-1)$.

If $z\in D_1$, at most $\Delta-m$ new discrepancies can be attributed to $z$. When $z$ was not chosen as a round-one source, the $m$ chosen neighbors are unavailable in round two. If $z$ itself acts in round two, its still-white target is an additional neighbor unavailable as a source, accounting for $z$'s own attribution. When $z$ was chosen in round one, it can no longer act, and the $m-1$ chosen neighbors are again unavailable. The neighbor $w_0$ is in $D_1$, so any force from $w_0$ is attributed to $w_0$ itself. In either case, counting retained and new discrepancies gives

$$
|D_2|\leq 1+m+(\Delta-m)+m(\Delta-1)
       =1+\Delta+m(\Delta-1)
       \leq 1+\Delta^2.
$$

At round two the intact coloring is full. Every subsequent round of a finite delayed run colors at least one of the remaining whites, so it finishes by round $\Delta^2+3$.

### A finite reduction for seven to ten whites

Let $k=|D_2|$. If $k\leq6$, a successful run finishes by round eight by adding at least one vertex per unfinished round. For $k\geq7$ in a subcubic graph, the preceding count gives $z\in D_1$ and $m\in\{2,3\}$. Use the same round-one sources and round-two attributions as above. Call the vertices of $D_1$ old, and the vertices of $D_2\setminus D_1$ new. All old and new vertices are white in the delayed run at time one.

The replay builds a small graph on the old and new vertices and records each relevant outside blue vertex by its set of neighbors in that graph. In later rounds, an outside vertex forces the sole remaining white in its set if one exists. An old or new vertex can act once it is blue, using its edges inside the small graph. This preserves the evolution after round two because every outside vertex is blue from then on.

**Required edges and sources.** Each missed round-one target uses one edge to its chosen predecessor. If that predecessor is $z$, the edge is internal. Otherwise the predecessor is permanently blue and contributes the set $\{z,w\}$, where $w$ is its target. Its other neighbors were already blue initially. These choices use $m$ edges at $z$ and one at each other old vertex.

For each new target, use the distinct intact round-two source chosen in the attribution. Each old vertex other than $z$ has at most two new targets associated with it, and at most one can be forced directly by that vertex. The others are forced by outside sources blue after round one in both runs. Such a source is adjacent to its new target and the old vertex that blocks it. It can also be adjacent to one other old vertex, as long as there is an unused edge there. No second new vertex can be its neighbor because its own target was its unique white neighbor at intact time one. A direct force gives a direct edge between the old and new vertices. Either type of source spends one edge at the old vertex and one at the new target.

The lost vertex can receive at most $3-m$ new attributions. For $m=3$ it receives none. For $m=2$, a new attribution to $z$ must use an outside source. If $z$ acted in round one it is already inactive. Otherwise the two chosen predecessors are initially blue neighbors of $z$, and if its third neighbor were an intact round-two white target then $z$ would already have forced it in round one.

**Vertices restored in round two.** If an old vertex returns by round two, it must have been forced from outside the small graph. The prescribed round-one and round-two outside sources are blocked at time one by at least two white neighbors. The restoring source therefore uses another edge at the restored vertex. It sees no other old or new vertex, since they were all still white at time one. The replay reserves one such edge and starts that old vertex blue. Other edges to it can contribute to the later runs.

**Remaining edges.** The replay fills the available degree slots with optional edges within the small graph and optional outside blue sources with one to three white neighbors at time two. It allows an extra old neighbor for each chosen outside round-two source as described above. Neighbors already blue at time two can be dropped from outside source sets. Edges between blue vertices and duplicate outside source sets have no effect on future forces. The allowed configurations include every actual residual process and can also include configurations without a realizing intact run.

Up to permutation of the missed round-one targets that share the same type of predecessor, the replay considers the following configurations. It skips configurations without a potential initial force. For seven, eight or nine whites it stops evaluating a run once the elapsed rounds plus the remaining white count is below seven.

| Whites after round two | Templates | Configurations evaluated | Finishing runs with at least seven further rounds | Maximum further rounds |
| ---: | ---: | ---: | ---: | ---: |
| 10 | 10 | 6,176,870 | 0 | 6 |
| 9 | 20 | 5,390,980 | 0 | At most 6 |
| 8 | 57 | 3,470,951 | 1,168 | 7 |
| 7 | 95 | 1,535,427 | 0 | At most 6 |

Thus nine rounds require exactly eight remaining whites at time two. Rounds three through nine then have one two-vertex addition and six single additions. A 24-vertex witness in the [example replay](check_single_loss_bounds.py) attains eight rounds with ten whites, while recovering from every singleton loss and having restricted time two.

### Sharp nine-round witness

A connected 17-vertex graph in the [example replay](check_single_loss_bounds.py) attains the global bound. The initial blue set is $\{0,8,9,10,11,13,15,16\}$. Its intact time is two and its minimum killing support $\{15,16\}$ has restricted time two. The two support vertices are leaves at vertex $14$. Either leaf forces $14$ in round one, and $14$ restores a missing leaf in round two. With both leaves white, $14$ cannot force either of them. Without initial blue vertex $0$, the successive additions are $\{14\},\{12\},\{5\},\{7\},\{4\},\{1\},\{0,2\},\{3\},\{6\}$. The replay checks that every singleton loss recovers and the two-vertex support loss stalls.

## Quadratic growth with the maximum degree

Let $M_d$ be the largest finite recovery time after one initial blue vertex is lost, over graphs of maximum degree at most $d$ whose intact coloring takes at most two rounds. For every $d\geq4$,

$$
\left\lfloor\frac{d^2}{2}\right\rfloor+5
\ \leq\ M_d\ \leq\
\left\lfloor\frac{d^2}{2}\right\rfloor+8.
$$

In particular the leading coefficient is $1/2$, with an additive gap of three rounds. The lower bound holds for connected graphs of maximum degree exactly $d$ that recover after every singleton loss and have a two-vertex minimum killing support of restricted time two.

### Upper bound

Write $Z$ for the round in which the lost vertex $z$ returns and $S$ for the delayed completion time. At time $Z$ the delayed coloring contains the initial blue set $B$, so $S\leq Z+2$. We may take $Z\geq6$, since otherwise $S\leq7$.

Use the same chosen sources and attributions as in the round-two bound. There are $m$ missed round-one targets, comprising $D_1\setminus\{z\}$. If $z$ is a chosen round-one source, denote its target by $w_0$. Every other missed target has a permanently blue predecessor $p$ whose only possible white neighbors in the delayed run are that target and $z$. If a target were blue by round $Z-2$, its predecessor would force $z$ by round $Z-1$. Thus these targets stay white through round $Z-2$.

Consider the $Z-5$ rounds from $3$ through $Z-3$. Every addition belongs to $D_2$, since the intact process is full by time two. The only old discrepancy that may be added in these rounds is $w_0$. Each other addition $x$ has a chosen intact round-two source. This is either an old discrepancy acting directly, or a vertex $q$ blue in both runs at time one. The only possible white neighbors of such a $q$ after time one are $x$ and vertices of $D_1$.

Suppose $x$ is added in round $j$ in this interval, and $q$ has just one neighbor in $D_1$. If this neighbor is $z$ or a missed target with a permanently blue predecessor, then $q$ forces it by round $j+1$ and $z$ is blue by $j+2<Z$. Thus every such outside source has at least two neighbors in $D_1$, apart from sources whose sole neighbor there is $w_0$. In that exception, $q$ makes $x$ and $w_0$ restore one another within a round once either is blue. If $w_0$ arrives in round $a$, all these targets arrive in rounds $a-1,a,a+1$. Together with $w_0$ they therefore occupy at most three rounds of the interval.

Let $N$ be the number of additions in the interval after excluding $w_0$ and the targets of those exceptional sources. Each outside source among the remaining additions uses at least two incidences at vertices of $D_1$. A direct force uses one incidence. These incidences are distinct across additions because the chosen sources are distinct, and none are the edges spent on the round-one predecessors. Those edges use $m$ incidences at $z$ and one at each of the $m$ other old discrepancies. At most

$$
(d-m)+m(d-1) = d+m(d-2)\leq d(d-1)
$$

incidences remain. There are at most $d$ direct forces. If $m<d$, there are at most $m+1$ old discrepancies that can act directly. If $m=d$, the round-one links already use all edges incident to $z$, leaving only the $d$ other old discrepancies as possible direct sources. Thus $2N\leq d(d-1)+d=d^2$.

Let $r$ be the number of rounds in the interval with at least one of the excluded additions. Every unfinished round adds a vertex, so $Z-5\leq N+r$. If $r\leq1$, this and $S\leq Z+2$ give the desired bound. If $r$ is two or three, $w_0$ must be blue by round $Z-3$ because all exceptional arrivals are within one round of its arrival. At least $r-1$ excluded targets use distinct incidences at $w_0$, because only one of the occupied rounds can be explained by $w_0$ itself. None of these incidences is counted for $N$.

At time $Z-2$, the blue vertex $w_0$ must still have another white neighbor $y$ besides $z$. Otherwise it would force $z$ in round $Z-1$. The edge $w_0y$ uses a further incidence outside the count for $N$. If $y$ is old, the incidence at $y$ is also unused. If $y$ is new, its own attribution uses a separate unused old incidence unless it is a direct force from $w_0$. In that last case the early count loses one possible direct force, since the direct force from $w_0$ was assigned to the late vertex $y$. Thus in each case the constraint from $y$ saves two units in the bound for $2N$, in addition to the $r-1$ incidences from the excluded targets. Consequently

$$
S\leq 7+r+N
 \leq 7+r+\left\lfloor\frac{d^2-r-1}{2}\right\rfloor
 \leq \left\lfloor\frac{d^2}{2}\right\rfloor+8
 \qquad(r=2,3).
$$

### Construction attaining the lower bound

Use blue vertices $z,p_1,\ldots,p_d$ and white vertices $w_1,\ldots,w_d$, with edges $zp_i,p_iw_i$. Set $k=d-2$. Make a multiset of pairs of old white vertices as follows. Use $k$ copies of the pair $\{w_2,w_3\}$. On the ordered list $w_1,w_4,\ldots,w_d$, take $\lfloor k/2\rfloor$ copies of the consecutive pairs around the cycle, including the closing pair. For $k=2$ a traversal counts the same pair twice. If $k$ is odd, also take $\lfloor k/2\rfloor$ disjoint consecutive pairs from that list. Each vertex occurs at most $k$ times. The number of pairs, including multiplicities, is $k+\lfloor k^2/2\rfloor=\lfloor d(d-2)/2\rfloor$.

For each pair occurrence $e$, add a distinct blue vertex $q_e$ adjacent to both endpoints and to its own white vertex $y_e$. Add white vertices $x_i$ for $i\ne2$ with edges $w_ix_i$, and join each $x_i$ for $i\geq4$ to $x_1$. Add a white vertex $u$ adjacent to $x_3$ and to a blue vertex $q_*$, with $q_*$ also joined to $w_2$. Use two more white vertices $a,b$. In the list consisting of $b$, all $y_e$ in any fixed order, and then $x_3,x_4,\ldots,x_d,x_1$, add one distinct blue relay vertex per consecutive pair, adjacent to both entries of that pair. Add a blue seed $s$ with edges $sa,ab$, and a blue helper $h$ joined to $s$ and to two blue leaves forming the support $H$. These are all the edges. The graph is connected and simple because each pair occurrence uses a different $q_e$. The $w_i$ have at most $k+2=d$ neighbors, the relay vertices and $x_i$ for $i\ne1$ have at most four, and $x_1$ has $d-1$ neighbors. The degree of $z$ is $d$.

In the intact run the $w_i$ and $a$ fill in round one. All $y_e$ fill from the $q_e$, all $x_i$ from the $w_i$, $u$ from $q_*$ and $b$ from $a$ in round two. After losing one leaf from $H$, the helper restores it in round one and both rounds proceed as before. A double loss in $H$ stalls because their common neighbor cannot force either leaf while both are white.

After losing $z$, no $p_i$ or $q_e$ can act while the $w_i$ are white. Once a $y_e$ is blue all its neighbors are already blue. A blue $x_3$ sees both $u,w_3$ white, and $q_*$ sees both $u,w_2$ white. A blue $x_i$ for $i\geq4$ sees both $w_i,x_1$ white until $x_1$ fills. Hence the run traverses $a,b$, then the $L=\lfloor d^2/2\rfloor-1$ vertices $y_e,x_i$ in list order, one per round. When $x_1$ fills, the next round restores $w_1,w_4,\ldots,w_d$. The $q_e$ incident to $w_2$ or $w_3$ are adjacent to both, so they remain blocked, as do $x_3$ and $q_*$. The next three rounds restore $z$, then $w_2,w_3$, then $u$. Thus recovery ends in round $L+6=\lfloor d^2/2\rfloor+5$.

Every other singleton loss recovers. Losing $p_i$, $s$, $h$ or a support leaf is repaired in round one by $z$, $h$, a leaf, or $h$, respectively. The delayed coloring then contains $B$. On loss of a $q_e$, the path from $s$ through the relays still colors every $y_e$ and $x_i$, and all $w_i$ fill in round one. An endpoint of its pair then restores the missing $q_e$. If $q_*$ is lost, $w_2$ restores it after round one, and $q_*$ can then restore $u$. On loss of a relay, both intact rounds can still fill all originally white vertices, and an adjacent vertex then restores that relay. The pair $H$ is therefore a minimum killing support.

## Reproduction

```sh
python -B research-twins/check_single_loss_bounds.py
python -B research-twins/check_saturated_subcubic.py
lake env lean -DwarningAsError=true research-twins/SingleLossBound.lean
```

The replay verifies both sharp examples and 147 instances of the unbounded family, using 49 path lengths and three variants of the lost vertex. The largest path has 100 vertices before $g$. It also checks 25,392 recoverable singleton cases with intact time at most one across all labeled simple graphs through order five. In 7,914 of those cases a blue twin of the lost vertex remains. On the same small graph range, the replay checks the degree-weighted inequality on 78,122 transitions and the refined round-two count on 51,658 singleton losses, including stalled runs. Separate subcubic certificates attain eight rounds with ten white vertices and nine rounds with eight white vertices after round two. The replay also verifies the degree-dependent lower bound for every maximum degree from 4 through 22, including all singleton losses and the minimum killing support. The Lean proof establishes the one-round upper bounds without a graph-order restriction.
