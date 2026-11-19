# Single-loss recovery times for synchronous zero forcing

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

Let $M_d$ be the largest finite recovery time after one initial blue vertex is lost, over graphs of maximum degree at most $d$ whose intact coloring takes at most two rounds. Put $F=\lfloor d^2/2\rfloor$. Then
$$
M_1=1,\qquad M_2=7,\qquad M_3=9,\qquad M_4=15,\qquad M_5=19,\qquad
M_d=\left\lfloor\frac{d^2}{2}\right\rfloor+6\quad(d\geq6).
$$
For $d\geq3$, the lower bounds hold for connected graphs of maximum degree exactly $d$ that recover after every singleton loss and have a two-vertex minimum killing support of restricted time two.

At degree one, a component is an isolated vertex or an edge. A recoverable loss can occur only on an edge with both endpoints initially blue, and it is repaired in one round. At degree two, the earlier bound $d^2+3$ gives seven. On the path $0,1,\ldots,8$ take initial blue set $\{0,5,6\}$. The intact time is two. Losing $5$ gives the successive additions $1,2,3,4,5,7,8$. The singleton times for $0,5,6$ are $5,7,7$. A separate edge with both endpoints initially blue gives a minimum killing support of restricted time two while preserving these times in the path component. The subcubic value was established in the preceding section.

### Upper bound

Write $Z$ for the round in which the lost vertex $z$ returns and $S$ for the delayed completion time. The coloring at time $Z$ contains the initial blue set, so $S\leq Z+2$. We may take $Z\geq6$, since otherwise $S\leq7$.

Use the chosen round-one predecessors and round-two attributions from the preceding bound. The old discrepancies are $D_1$, consisting of $z$ and $m$ missed targets. If $z$ was chosen to force one of those targets, call that target $w_0$. Each other missed target has a permanently blue predecessor $p$ whose only possible white neighbors in the delayed run are that target and $z$. Hence each of these targets is white through round $Z-2$. It will be blue by round $Z+1$, since $z$ is blue at time $Z$.

Consider the $Z-5$ rounds from $3$ through $Z-3$, inclusive. Every addition belongs to $D_2$ because the intact process is full by time two. The only old discrepancy that may be added in this interval is $w_0$. Every new discrepancy $x\in D_2\setminus D_1$ has a distinct chosen source in intact round two. The source either lies in $D_1$ and acts directly, or is an outside vertex $q$ blue in both runs at time one. The only possible white neighbors of $q$ after time one are $x$ and vertices of $D_1$.

Suppose $x$ is added in round $j$ of the interval. If $q$ has just one neighbor in $D_1$ and that neighbor is $z$ or a missed target with predecessor $p$, it restores that neighbor by $j+1$ and $z$ by $j+2<Z$. The exception is an outside source whose sole old neighbor is $w_0$. Through such a source, $x$ and $w_0$ each restore the other within a round. Thus those exceptional targets can arrive only in rounds $a-1,a,a+1$, where $a$ is the arrival time of $w_0$.

Let $r$ count the rounds in the interval that include at least one exceptional target or $w_0$ itself. Let $N$ be the number of other additions in the interval. Then $0\leq r\leq3$ and $Z-5\leq N+r$. Every outside source counted for $N$ uses at least two incidences at vertices of $D_1$, and a direct source uses one. The incidences are distinct across targets and avoid the round-one predecessors. The latter use $m$ edges at $z$ and one at each other old discrepancy, leaving at most $C=(d-m)+m(d-1)\leq d(d-1)$ incidences. There are at most $d$ direct sources. For $m<d$ there are only $m+1$ old discrepancies, and for $m=d$ the round-one links use all edges at $z$. Thus $2N\leq C+d\leq d^2$.

We will use the following savings in this count. Any specified late new target uses at least one unused old incidence. A round with an exceptional target likewise uses a distinct unused incidence at $w_0$. If $w_0$ is blue at time $Z-2$, it must still see a white neighbor $y\ne z$. The edge $w_0y$ is unused in the early count. If $y$ is old, the incidence at $y$ is also unused. If $y$ is new, its attribution uses another old incidence unless it is a direct force from $w_0$. In that case it reduces the number of possible early direct forces by one. Thus the edge to $y$ accounts for two units in the bound for $2N$. When $S=Z+2$, a vertex $u$ added in the last round is new whenever $w_0$ is already blue. We can choose $y\ne u$. Indeed, if $u$ neighbors $w_0$, then $w_0$ must see another white neighbor at time $Z$ to avoid forcing $u$ by $Z+1$. That neighbor was already white at time $Z-2$.

**The bound $F+7$.** If $r=0$, use $S\leq7+N$. If $r=1$, $w_0$ is blue by time $Z-2$, so the savings from $y$ give $2N\leq d^2-2$ and $S\leq8+N$. If $r=2$ or $3$, $w_0$ is blue by time $Z-3$. At least $r-1$ of the exceptional rounds include a target of an exceptional source, since at most one round can be covered by $w_0$ alone. Together with $y$ this saves at least $r+1$ units. For $S\leq Z+1$, this gives $S\leq6+r+\lfloor(d^2-r-1)/2\rfloor\leq F+7$. If $S=Z+2$, also charge a vertex $g$ added at round $Z-2$ and a vertex $u$ added at $Z+2$. Both are new, and $g$ differs from $y$, which is still white at time $Z-2$. Choose $y\ne u$ as above. These two attributions consume additional distinct old incidences. Hence $S\leq7+r+\lfloor(d^2-r-3)/2\rfloor\leq F+7$.

**The bound $F+6$ for $d\geq6$.** First take $r=0$. If $S\leq Z+1$, use $S\leq6+N$. Otherwise it suffices to save two units. If $m<d$, then $C\leq d(d-1)-(d-2)$ already supplies the savings. If $m=d$, all old discrepancies are blue by time $Z+1$. This includes $w_0$ when it exists, because all other neighbors of $z$ are the blue predecessors. Thus a final addition $u$ is new. If $w_0$ is blue at time $Z-2$, use the savings from $y$. Otherwise a vertex $g$ added in round $Z-2$ is new, and the attributions of $g,u$ supply the two incidences.

Next let $r=1$ and $w_0$ first return at $Z-2$. The exceptional target in round $Z-3$ contributes one saved incidence, and $y$ supplies two more units. If $S\leq Z+1$ this gives $S\leq7+\lfloor(d^2-3)/2\rfloor\leq F+6$. If $S=Z+2$, also charge the final new vertex $u$ with $y\ne u$, giving $S\leq8+\lfloor(d^2-4)/2\rfloor=F+6$.

In the remaining cases, $r\geq1$ and $w_0$ is blue by time $Z-3$. Count old incidences away from $w_0$. Every outside source for an early addition counted in $N$ has at least two old neighbors away from $w_0$. Otherwise, if it has just one such neighbor, that neighbor would be its sole white neighbor by time $Z-3$, forcing $z$ by time $Z-1$. Sources with no such neighbor were already excluded. The resources away from $w_0$ total at most $C-(d-1)$, and at most $d-1$ vertices away from $w_0$ can act directly. If $\delta$ is one when $w_0$ itself accounts for an early direct target and zero otherwise, this gives
$$
2(N-\delta)\leq d^2-d,
\qquad
N\leq F-\lfloor d/2\rfloor+\delta.
$$

For $r=1$ this suffices since $S\leq8+N$ and $\lfloor d/2\rfloor\geq3$. For $r=2$ it suffices if $\delta=0$. If $\delta=1$, the guard $y$ contributes an unused incidence away from $w_0$. For old $y$ use the incidence of $w_0y$ at $y$. A new $y$ cannot be the direct target of $w_0$, which already has an early target, and cannot be assigned to an outside source with only $w_0$ as old neighbor, since that source would have forced it by $Z-2$. Its attribution therefore uses an unused incidence away from $w_0$. Subtracting this unit from the even budget $d^2-d$ gives $N\leq F-\lfloor d/2\rfloor$, and $S\leq9+N\leq F+6$.

Finally take $r=3$. Then $w_0$ was blue by $Z-4$, because all three possible exceptional rounds occur in the interval. An outside source with sole old neighbor $w_0$ would have acted by $Z-3$. Thus the late vertices $y,g$ from above, and $u$ when $S=Z+2$, each use a distinct incidence away from $w_0$, apart from at most one direct target of $w_0$. As before, if $y$ is old we use the incidence of $w_0y$ at $y$. If $S\leq Z+1$ and $\delta=0$, use $S\leq9+N$. If $\delta=1$, both $y$ and $g$ save units away from $w_0$, again yielding $N\leq F-\lfloor d/2\rfloor$. If $S=Z+2$, the three vertices save at least $2+\delta$ units because $\delta=1$ excludes a late direct target of $w_0$. Now $N\leq F-\lfloor d/2\rfloor-1$, so $S\leq10+N\leq F+6$.

### Common relay and support

A relay between consecutive white vertices is a blue vertex adjacent to those two vertices. The prefix consists of a blue seed $s$ joined to a white $a$, with $a$ joined to a white $b$. The prefix advances in two rounds. Join $s$ to a blue helper $h$ with two blue leaf neighbors forming $H$. Losing $s$, $h$, or one leaf is repaired in round one by $h$, a leaf, or $h$, respectively. A singleton loss in $H$ leaves the other round-one forces available. Losing both leaves stalls because their only neighbor sees two whites until one is restored.

### Construction for maximum degrees four and five

Use old whites $w_0,\ldots,w_{d-1}$. The blue $z$ is adjacent to $w_0$ and to the blue predecessors of $w_1,\ldots,w_{d-1}$, each predecessor joined to its own target. Use consecutive pairs on the path $w_1,\ldots,w_{d-1}$, with multiplicities $(1,1)$ for $d=4$ or $(2,1,2)$ for $d=5$. Each pair occurrence has a distinct blue $q_e$ joined to both endpoints and its own white $y_e$.

Give each $w_i$ with $i\geq1$ a direct white neighbor $x_i$. Add a white $G$ adjacent to $w_0,x_1,\ldots,x_{d-2}$. Use four more white vertices $E,R,g,u$ with distinct blue sources, each joined to its own white target and to one old white vertex. The old neighbors of these four sources are $w_0,w_0,w_1,w_{d-1}$, respectively. Join $u$ to $x_{d-1}$. Use the common prefix and support. Add a relay from $b$ to $E$, and relays between consecutive entries in the list $R$, all $y_e$, all $x_i$, then $g$. These are all the edges. The graph is connected with maximum degree $d$. In particular $w_0$ has degree four, each $x_i$ has at most four neighbors, and the path multiplicities account for the available slots at the other $w_i$.

Intact round one restores the $w_i$ and $a$. Round two restores every other white vertex, directly from an old vertex, from a blue source, or from $a$. The same deadlines hold for losses in $H$. On loss of $z$, rounds one and two restore $a,b$. The next three rounds restore $E,w_0,R$ in that order. While the other $w_i$ are white, each blue $x_i$ remains blocked by $G$ or $u$. The relays then fill all $y_e$, all $x_i$, and $g$, one at a time. The number of vertices $y_e,x_i$ is five for $d=4$ and nine for $d=5$, namely $F-3$. The next round after $g$ restores $w_1$, and the following round restores $z$. The endpoint $w_{d-1}$ is still white when $z$ returns, since it is at least two steps from $w_1$ in the pair path. It fills one round after $z$, followed by $u$ in the last round. The total time is $2+3+(F-3)+1+4=F+7$.

For a lost predecessor, the prefix and the source at $E$ still restore $w_0$, freeing $z$ to restore the predecessor. If a pair source or the source of $g$ or $u$ is lost, the relay run still colors its list, and an old neighbor restores the missing source once that neighbor's direct child is blue. If the source of $E$ is lost, the prefix still colors $E$, which then restores its source. If the source of $R$ is lost, the first pair target still fills in round two from its intact source. The relay next to $R$ then restores $R$, which can restore its source. If a relay is lost, the intact forces fill all originally white vertices by round two, and the relay returns next. All singleton losses therefore recover, so $H$ is a minimum killing support.

### Construction for odd maximum degree

Use white vertices $w_1,\ldots,w_d$ and blue vertices $z,p_1,\ldots,p_d$, with edges $zp_i,p_iw_i$. Use the common prefix and support. Here $k=d-2$ is odd. Use $k-1$ copies of $\{w_2,w_3\}$. On the cyclic list $w_1,w_4,\ldots,w_d$ use $\lfloor k/2\rfloor$ copies of all consecutive pairs, then add disjoint consecutive pairs on the list with $w_1$ removed. This uses at most $k-1$ occurrences at $w_1,w_2,w_3$ and at most $k$ at the other $w_i$. Give each pair its own blue $q_e$ and white $y_e$ as before. The pair count is $\lfloor d(d-2)/2\rfloor-1$.

Give every old vertex $w_i$ its direct white neighbor $x_i$. Instead of using $x_1$ as the end of the relay list, add a new white end $G$ and a blue vertex adjacent to exactly $G,w_1$. Join $G$ to all $x_i$ other than $x_2,x_3$. The relay list is now $b$, all $y_e$, all $x_i$, then $G$. The last white vertex $u$ remains adjacent to the blue $q_*$, which is joined to $w_2$. Join $u$ to both $x_2$ and $x_3$. The degree cap holds: $G$ has $d$ neighbors, each $x_i$ has four, and the extra blue sources observing $w_1,w_2$ use the slots available there.

In the intact run both $G$ and $u$ fill from their blue sources in round two, after $w_1,w_2$ became blue. In round one the $p_i$ fill the $w_i$. In round two the $q_e$ fill the $y_e$ and the $w_i$ fill their $x_i$. Both prefix rounds and the support times are as above. On loss of $z$, the relay list advances one vertex per round. While $G,u$ are white, the $x_i$ that are already blue cannot act because they also see their own old white neighbor. There are
$$
\left(\left\lfloor d(d-2)/2\right\rfloor-1\right)+d+1=F
$$
entries after $b$. Once $G$ fills, the next round restores all $w_i$ except $w_2,w_3$. Then $z$ fills, then $w_2,w_3$, then $u$. Thus the number of delayed rounds is $2+F+4=F+6$.

Every singleton loss still recovers. If a predecessor is lost, $z$ restores it in round one because all neighbors of $z$ are predecessors. The seed, helper and leaves recover as above. If a pair source is lost, the relays can color the entire list and the endpoints of the pair are blue, allowing its recovery. If a relay is lost, the intact sources still color the entire list within two rounds and the missing relay then returns. If the blue source observing $G$ or $u$ is lost, its old neighbor can restore it once the corresponding direct target is blue. In the first case the relays can color that target, and in the second case the same relay list also colors $x_2$. Both leaves must be lost for $H$ itself to stall.

### Construction for even maximum degree at least six

Use white vertices $w_0,\ldots,w_{d-1}$. The blue vertex $z$ is adjacent to $w_0$ and to the blue predecessors $p_i$ of $w_i$ for $1\leq i<d$. As before each $p_i$ is adjacent to $z,w_i$. On the cyclic list of the $w_i$, take $(d-2)/2$ copies of all consecutive pairs. Remove one copy each of $\{w_0,w_1\}$ and $\{w_3,w_4\}$ and insert one copy of $\{w_1,w_4\}$. The resulting multiset has $d(d-2)/2-1$ pairs. Each old vertex occurs $d-2$ times, except $w_0,w_3$, which occur $d-3$ times. The pair graph has a neighbor of $w_0$ and no path of length at most two from $w_0$ to $w_3$, since they are nonadjacent and their neighbor sets are disjoint.

For each pair use a blue $q_e$ joined to its endpoints and a distinct white child $y_e$. For $1\leq i<d$ use a white $x_i$ adjacent to $w_i$ and two further white vertices $G,u$. Join $G$ to $w_0$. Give $u$ a blue source adjacent to $u,w_3$, and add a white vertex $L$ with a blue source adjacent to $L,w_0$. The relay list is $b$, all $y_e$, all $x_i$, then $L$. Use the same prefix $s,a,b$ with the helper and its two leaves, and the same blue relay between each consecutive pair. Each $x_i$ has at most five neighbors. The vertices $G,u$ have degree $d$, and $w_0,w_3$ use their spare pair slots for their remaining edges. The graph is connected and has maximum degree $d$.

In the intact run $z$ fills $w_0$ in round one and the $p_i$ fill the other $w_i$. In round two the pair sources fill the $y_e$, the $w_i$ fill the $x_i$ or $G$, and their own blue sources fill $L,u$. The prefix fills in two rounds, and the support leaves behave as before.

After losing $z$, the run traverses the prefix and then the relay list one vertex per round. A blue $x_i$ remains blocked by $G,u$, and all old vertices are white. The list has $F-1$ entries after $b$. After $L$ fills, the next round restores $w_0$. Then the pair sources restore its neighbors, and one of their predecessors restores $z$ in the following round. The vertex $w_3$ is still white when $z$ returns because it is at distance at least three from $w_0$ in the pair graph. The remaining old vertices and $G$ fill one round after $z$, and $u$ then fills from its source. Thus the full delayed run has $2+(F-1)+5=F+6$ rounds.

All singleton losses recover. The relays and prefix can color their entire list on loss of any predecessor or any blue source for a pair, $L$, or $u$. If a predecessor is lost, $L$ then enables $w_0$ to return, after which $z$ restores the missing predecessor. For a lost pair source or the source of $u$, an old endpoint other than $w_0$ restores it once that endpoint and its direct target are blue. If the source of $L$ is lost, $L$ can restore it after the relay traversal. On loss of a relay, the intact two rounds fill all originally white vertices and the missing relay then returns. Loss of the prefix seed, helper or a support leaf still recovers as in the other constructions. This gives the same two-vertex minimum killing support with restricted time two.

## More than two intact rounds

Write $M_{d,t}$ for the largest finite single-loss recovery time over graphs of maximum degree at most $d$ whose intact coloring completes by round $t$. Thus $M_d=M_{d,2}$ above. For $d\geq3$ and $t\geq3$, put $P=d(d-1)^{t-1}$. The bounds below give

$$
M_{d,t}=\Theta(P),
\qquad
\frac{M_{d,t}}{P}=\frac12+O(1/d),
$$

with constants independent of $t$. In particular, for fixed $d\geq3$ the growth rate in $t$ has base $d-1$, and for each fixed $t\geq3$ the leading term in $d$ is $d^t/2$.

### A tree of all discrepancies

Let $A_i=\bigcup_{j=0}^i D_j$ be the vertices that have ever disagreed by round $i$. For $d\geq2$,

$$
|A_i|\leq 1+d\sum_{j=0}^{i-1}(d-1)^j .
$$

For each new discrepancy $x$, choose one intact source $v$ at the round when $x$ becomes blue in the intact run. If $v$ has ever been a discrepancy, make it the parent of $x$ in a tree, even if $v$ has already turned blue in the delayed run. Otherwise $v$ is blue in both runs, and it sees another white neighbor $w$ in the delayed run that is blue in the intact run. Make one such $w$ the parent of $x$. Each parent appears strictly earlier than its child, and $z$ is the only first discrepancy, so these links make a rooted tree.

Each child of a vertex $w$ uses a distinct selected source from among $w$ itself and its neighbors. A selected source can force only one target in the intact process, since after making a force all its neighbors are blue. If $w$ is chosen as the source of one of its own children $x$, the neighbor $x$ cannot be counted as an outside source for another child of $w$. Before that force $x$ is white, and after it $x$ is a historical discrepancy, so a later choice of $x$ as a source would put its target below $x$ itself. If $w\ne z$, its own intact predecessor is also unavailable as an outside source because it has already used its force. Thus $z$ has at most $d$ children and every other discrepancy has at most $d-1$. By round $i$ the tree has depth at most $i$, giving the bound.

At intact completion all whites of the delayed run belong to $D_t\subseteq A_t$. If it recovers, it adds at least one vertex per unfinished round. In particular,

$$
M_{d,t}\leq t+1+d\sum_{j=0}^{t-1}(d-1)^j.
$$

For $d=2$ this upper bound is attained for every $t\geq1$. On the path $0,\ldots,3t+2$, start with $0,2t+1,2t+2$ blue. The first two blue blocks fill the gap of $2t$ whites from both ends in $t$ rounds. The last block also fills the $t$ whites to its right. On loss of either of its two seeds only the left endpoint can start a force. The path advances one white per round, passing the remaining seed once its left neighbor turns blue. This takes $3t+1$ rounds. Loss of $0$ leaves the consecutive blue pair and also recovers. A separate blue edge gives restricted time $t$ with a two-vertex minimum killing support.

### Counting the final round of discrepancies

For fixed $d\geq2$ and $t\geq1$ consider a recoverable instance, and let $D=|D_{t-1}|$. We claim the more precise bound

$$
T(B\setminus\{z\})\leq t+\left\lfloor\frac{(d+4)D+1}{2}\right\rfloor.
$$

Choose an intact round-$t$ source for each $x\in D_t\setminus D_{t-1}$. A source in $D_{t-1}$ is direct and uses one incidence at that old vertex. A source outside $D_{t-1}$ is blue in both runs at $t-1$, and its only possible white neighbors from then on are $x$ and its neighbors in $D_{t-1}$. It must have at least one old neighbor. If it has two or more, count at least two old incidences for $x$. If it has just one, say $w$, call $x$ exceptional. Because the source sees only $x,w$ as possible whites, their arrival times differ by at most one. Thus the old vertices and the exceptional targets occupy at most $3D$ rounds after $t$.

Let $E$ be the number of exceptional targets and $N$ the number of other new targets. The old vertices and exceptional targets can also occupy at most $D+E$ rounds. The chosen sources for distinct new targets are distinct. The old incidences counted at the sources avoid the intact predecessor of each non-$z$ old vertex, since it already used its force. The total capacity is at most $(d-1)D+1$. With at most $D$ direct sources, it follows that $2N+E\leq dD+1$. Each round after $t$ adds a vertex, so the number of further rounds is at most
$$
N+\min(3D,D+E)
\leq \frac{dD+1}{2}+\min(3D-E/2,D+E/2)
\leq \frac{(d+4)D+1}{2}.
$$

Taking the integer part proves the bound. By the tree estimate, for $d\geq3$ and $t\geq3$ we can use $D\leq(P-2)/(d-2)$.

### Layered constructions

Take $d\geq3$ and $t\geq3$. Use a blue $z$ and $d$ blue predecessors $p_i$, each adjacent to $z$ and to a white root $w_i$. These roots form layer one. For each vertex in layers one through $t-2$, introduce $d-1$ white children in the next layer. Each child has a distinct blue source adjacent to exactly that child and its parent. Give $w_1$ only $d-2$ children to leave one spare edge there.

The vertices in layer $t-1$ are partitioned by their root. In a branch of size $L\geq2$, take all consecutive pairs in cyclic order, including the closing pair, $\lfloor(d-1)/2\rfloor$ times. If $d-1$ is odd, also take $\lfloor L/2\rfloor$ disjoint consecutive pairs. Each pair occurrence gives a distinct terminal white vertex and a blue source adjacent to it and to the two vertices of the pair. For $L=2$ the cycle counts the pair twice, using distinct sources. A branch of size one contributes no pairs. This happens only for the branch at $w_1$ when $(d,t)=(3,3)$.

Join all $n$ terminal vertices into a white path in any order, with a blue seed $s$ adjacent to the first and with the last adjacent to $w_1$. Attach the same blue helper and its two blue leaf neighbors to $s$, forming the support $H$. All edges are specified by this construction. The graph is connected and simple, and its maximum degree is $d$. Every nonterminal white has one incoming source and at most $d-1$ outgoing incidences. At $w_1$ one of those incidences is used for the terminal path. The count of terminal vertices is
$$
n=
\left\lfloor\frac{(d-2)(d-1)^{t-2}}{2}\right\rfloor
+(d-1)\left\lfloor\frac{(d-1)^{t-1}}{2}\right\rfloor
-\mathbf 1_{(d,t)=(3,3)}.
$$

In the intact run each nonterminal layer $j$ fills in round $j$. Before then, a source for a next-layer child sees two white vertices while both parent and child are white. A terminal source also sees its two white parents, so it cannot start coloring the deepest nonterminal layer. The terminal path can progress from $s$ starting in round one and from $w_1$ starting in round two. By time $t-1$ these two fronts can have filled at most $2t-3$ vertices. Since $n\geq2^{t-1}>2t-3$, some terminal white remains. The terminal sources fill the remainder in round $t$. The same timing holds after a singleton loss in $H$.

After losing $z$, all nonterminal layers stay white while the terminal path advances one vertex per round from $s$. The single-parent sources see two white neighbors and every terminal source still sees two white parents. At round $n+1$ the last path vertex restores $w_1$. Then $p_1$ restores $z$ and the other roots fill in round $n+3$. Until their own roots fill, none of the other branches can start, since each terminal source is confined to one branch. Within each such branch, the nonterminal layers then fill one per round. The last nonterminal layer fills at $n+t+1$, giving that delayed time.

All singleton losses recover. If a predecessor is lost, $z$ restores it in round one. The seed, helper and support leaves also recover in round one. If a blue source is lost, its parent layer still fills, since each parent can be forced from the preceding layer. A parent then sees only the missing source white. If that parent is $w_1$, the terminal path also fills independently from the seed, since this missing single-parent source is outside the terminal path. This allows $w_1$ to restore the source. For a terminal source the two parents are in layer $t-1$, where neither has an additional path neighbor. These cases give finite recovery for every singleton. The two leaves cannot recover if both are lost, so $H$ is a minimum killing support with restricted time $t$.

This gives $n+t+1\leq M_{d,t}$. The terminal count is at least $P/2-(d-1)^{t-2}/2-d/2-1$. Dividing by $P$ and using the upper bound from the final-round count gives $M_{d,t}/P=1/2+O(1/d)$ uniformly for $t\geq3$. The same estimates give the stated growth in $t$ at each fixed $d\geq3$.

### The first two asymptotic terms

The error term can be sharpened uniformly in the intact deadline. With $P=d(d-1)^{t-1}$, for $d\geq6$ and $t\geq3$,
$$
M_{d,t}=\frac P2+\frac{P}{2(d-1)}+O\!\left(\frac{P}{d^2}\right),
$$
with an absolute constant. Equivalently, for fixed $t\geq3$,
$$
M_{d,t}=\frac{d^t}{2}-\frac{t-2}{2}d^{t-1}+O_t(d^{t-2}).
$$

#### Upper bound

Let $\alpha_j=1+d\sum_{\ell=0}^{j-1}(d-1)^\ell$ be the capacity of the discrepancy tree through round $j$. At any cutoff $j$ put $A=|A_j|$, $D=|D_j|$ and $h=A-D$. Each link of the tree with both endpoints still discrepant reserves an incidence at its parent. If the link used an outside source, that source already made its intact force and cannot be selected again. If it used the parent itself as a historical direct source, its child is still discrepant. The edge to that child cannot be used for a direct force into a new discrepancy or for an outside source blue in both runs. These incidences are distinct by the tree argument. They also avoid the earlier intact predecessor at every non-root vertex, which is already excluded.

At most $(d-1)h+\mathbf{1}_{z\notin D_j}$ links have a restored parent, and exactly $h-\mathbf{1}_{z\notin D_j}$ have a restored child. Hence the number $Q_j$ of links with both endpoints still discrepant satisfies
$$
Q_j\geq A-1-dh.
$$
The capacity for incidences used in new forces at round $j+1$ is therefore at most $(d-1)D+1-Q_j$.

Set $i=t-1$, $X=\alpha_i$ and $Y=\alpha_{i-1}$. For each new discrepancy born in round $i$, select one intact source. Let $B$ count those for which the selected source is outside $D_{i-1}$ and has at least two neighbors in $D_{i-1}$. A direct source or an outside source with one old neighbor uses one incidence, while an outside source counted for $B$ uses at least two. Thus the number born plus $B$ is at most $(d-1)|D_{i-1}|+1-Q_{i-1}$. Adding the number retained and using the bound for $Q_{i-1}$ gives
$$
|D_i|+B\leq (d-1)|A_{i-1}|+2\leq (d-1)Y+2=X.
$$

Consider the additions after the intact deadline $t$. Use the final-round classification above, with $N$ counting the nonexceptional new targets and $E$ the exceptional targets. Let $R$ count the rounds after $t$ that add an old vertex or an exceptional target. Among the old vertices in $D_i$, those already present in $D_{i-1}$ and those born from a direct source in round $i$ number at most $2Y$ in total. At most $B$ further old vertices were born from outside sources with multiple old neighbors. These vertices and their own exceptional targets occupy at most $3(2Y+B)$ rounds.

Every other old vertex $v$ is a round-$i$ birth with a selected outside source that had exactly one neighbor $w$ in $D_{i-1}$. From time $i-1$ onward, this source has only $w,v$ as possible whites. Their delayed arrival times differ by at most one. Each final-round exceptional target associated with $v$ also arrives within one round of $v$. All these arrivals are within two rounds of the arrival of some $w\in D_{i-1}$, and therefore occupy at most $5Y$ rounds. We conclude that $R\leq11Y+3B$.

For the final-round incidence count, use $Q_i$ to get
$$
2N+E\leq d|D_i|+1-Q_i.
$$
The right-hand side is at most $(d-1)X+2$ by the bound on $Q_i$. It is also at most $d(X-B)+1$ by the penultimate count. The run finishes by $t+N+R$. In bounding $N$ by half the smaller of these two upper bounds, use their weighted average with weight $6/d$ on the second. This cancels the $3B$ in the bound for $R$ and gives
$$
M_{d,t}\leq t+11Y+\frac{(d-1)X+2}{2}+\frac{3(X-1)}{d}.
$$
Here $X=(P-2)/(d-2)$ and $Y=(X-2)/(d-1)$. The terms $t$, $Y$ and $X/d$ are all $O(P/d^2)$ uniformly in $t\geq3$. The middle term is $P/2+P/(2(d-2))+O(1)$, which gives the claimed upper bound.

#### Lower bound

Use the nonterminal layers of the previous construction with $d-1$ children at every vertex, including $w_1$. There is no edge from the terminal path back to $w_1$. The deepest nonterminal layer has $L=d(d-1)^{t-2}=P/(d-1)$ white vertices. Give every one of these vertices a direct terminal white child. On the same $L$ parents use the cyclic pair construction with at most $d-2$ incidences per parent, by repeating the cycle $\lfloor(d-2)/2\rfloor$ times and adding one matching of disjoint consecutive pairs when $d-2$ is odd. Each pair occurrence has a distinct outside blue source and a terminal white target, for $\lfloor(d-2)L/2\rfloor$ such targets.

Partition the $L$ direct children into $\lceil L/(d-2)\rceil$ groups of size at most $d-2$. In each group choose one child and join it to the other children of that group. Call the chosen child its guard. Use the prefix $s,a,b$ and the same helper and two support leaves. Add a blue relay between consecutive vertices in the list consisting of $b$, the pair targets, all direct children other than the guards, then all guards. Each guard has its old parent, at most $d-3$ guarded neighbors and at most two blue relay neighbors. Each other direct child has at most four neighbors, and every old parent has at most $d$ neighbors. The graph is connected and has maximum degree $d$.

In the intact run all nonterminal layers fill on their assigned rounds. Before the deepest nonterminal layer fills, the pair sources are blocked. The relay list starts from $b$ in round two, and the guards are beyond all the nonguard targets, too far to arrive by the relay before the intact deadline. Thus a direct child reached early by the relay cannot restore its old parent while its guard is white. In round $t$ the old parents fill their direct children and the pair sources fill their targets. There are more nonguard targets than the $t-2$ that the relay could supply by then, so intact and support-restricted completion take exactly $t$ rounds.

When $z$ is lost, all nonterminal layers stay white until the first guard is reached. The pair sources see two white parents, and each blue nonguard direct child sees both its parent and its guard white. Thus the two prefix vertices, all nonguard terminal targets, and the first guard fill one at a time. This gives a lower bound of
$$
\left\lfloor\frac{dL}{2}\right\rfloor-\left\lceil\frac{L}{d-2}\right\rceil+3
$$
rounds. The relays eventually fill all terminal vertices. Then the direct children can force their old parents, the single-parent sources let this repair reach the roots, and a predecessor restores $z$.

The other singleton losses also recover. A lost predecessor, prefix seed, helper or leaf is restored in round one. A lost single-parent source is restored by its old parent, because the parent's earlier layer still fills. A lost pair source is repaired by one of its parents after the relay list is blue. A lost relay can return after the intact sources color all originally white vertices. The leaf pair remains a minimum killing support.

Since $dL=P+P/(d-1)$, the lower bound is $P/2+P/(2(d-1))-O(P/d^2)$ with an absolute constant, as required.

## Reproduction

```sh
python -B research-twins/check_single_loss_bounds.py
python -B research-twins/check_saturated_subcubic.py
lake env lean -DwarningAsError=true research-twins/SingleLossBound.lean
```

The replay verifies both sharp examples and 147 instances of the unbounded family, using 49 path lengths and three variants of the lost vertex. The largest path has 100 vertices before $g$. It also checks 25,392 recoverable singleton cases with intact time at most one across all labeled simple graphs through order five. In 7,914 of those cases a blue twin of the lost vertex remains. On the same small graph range, the replay checks the degree-weighted inequality on 78,122 transitions and the refined round-two count on 51,658 singleton losses, including stalled runs. Separate subcubic certificates attain eight rounds with ten white vertices and nine rounds with eight white vertices after round two. The replay also verifies the degree-dependent lower bounds for every maximum degree from 4 through 22, including all singleton losses and the minimum killing support. The same script checks the cumulative discrepancy and final-round bounds on the small graphs, the degree-two extremal paths for intact times 1 through 25, 12 layered certificates with intact times three through six, and six guarded layered certificates. It also checks the penultimate-round incidence bound on the small graphs. The Lean proof establishes the one-round upper bounds without a graph-order restriction.
