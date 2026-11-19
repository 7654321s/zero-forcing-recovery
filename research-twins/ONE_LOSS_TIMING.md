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

**Theorem.** Let the maximum degree be $\Delta\geq1$ and let the intact coloring finish by round two. If the delayed run finishes, it does so within $\Delta^2+3$ rounds. For maximum degree at most three it finishes within **10 rounds**. If exactly ten vertices remain white after delayed round two, the bound improves to **eight rounds** and is attained. The subcubic result uses a finite enumeration for the ten-white case.

Write $m=|D_1\setminus\{z\}|$. For each of these $m$ missed targets, choose an intact round-one source. If $z$ forced a missed target, choose $z$ as its source and call that target $w_0$. Every other chosen source is an initially blue neighbor of $z$. The chosen sources are distinct and have no white neighbors in the intact run after round one. Counting these neighbors of $z$, together with $w_0$ if present, gives $m\leq\Delta$.

If $z\notin D_1$, the delayed coloring after round one contains the entire intact initial blue set. By monotonicity, the delayed coloring after round two contains the intact coloring after round one, so every discrepancy in $D_2$ is new. Each of the $m$ vertices of $D_1$ accounts for at most $\Delta-1$ new discrepancies by the preceding attribution argument. Thus $|D_2|\leq m(\Delta-1)$.

If $z\in D_1$, at most $\Delta-m$ new discrepancies can be attributed to $z$. When $z$ was not chosen as a round-one source, the $m$ chosen neighbors are unavailable in round two. If $z$ itself acts in round two, its still-white target is an additional neighbor unavailable as a source, accounting for $z$'s own attribution. When $z$ was chosen in round one, it can no longer act, and the $m-1$ chosen neighbors are again unavailable. The neighbor $w_0$ is in $D_1$, so any force from $w_0$ is attributed to $w_0$ itself. In either case, counting retained and new discrepancies gives

$$
|D_2|\leq 1+m+(\Delta-m)+m(\Delta-1)
       =1+\Delta+m(\Delta-1)
       \leq 1+\Delta^2.
$$

At round two the intact coloring is full. Every subsequent round of a finite delayed run colors at least one of the remaining whites, so it finishes by round $\Delta^2+3$.

### Nine whites after round two

For $\Delta=3$, $|D_2|=9$ requires $m=3$ and $z\in D_1$. The chosen round-one sources occupy all three neighbors of $z$, counting $z$'s own target as a neighbor when it was chosen to act. No new discrepancy is attributed to $z$. Each of the three other vertices of $D_1$ receives at most two attributions.

The six-attribution case cannot leave nine whites. If all three missed targets receive two attributions, each has degree three. Besides its round-one source, its two neighbors are either two chosen outside blue sources, or one such source and a white target it forces in intact round two. Every such outside source sees both the missed target and the new discrepancy white in delayed round one. Each blue round-one source also sees $z$ and its target white. All blue neighbors of $D_1$ are among these blocked sources, so no vertex of $D_1$ is restored in round two. Hence $|D_2|=9$ requires exactly five attributions and all four vertices of $D_1$ retained. The attribution counts for the three missed targets are two, two and one.

Suppose every delayed round after round two adds exactly one vertex. If $z$ had three blue round-one neighbors $p_i$ with missed targets $w_i$, then each $p_i$ sees only $z,w_i$ as possible whites. If $z$ fills first among the four vertices, the next round fills all three $w_i$. If some $w_i$ fills first, then $z$ fills next and both remaining $w_i$ fill in the following round. Neither permits a single addition in every round.

If $z$ was chosen to act in round one, its neighbors are two blue sources $p_1,p_2$ and its own target $w_0$. Under the one-addition assumption, $z$ cannot fill before both of the targets $w_1,w_2$ of $p_1,p_2$. Renaming them if necessary, let $w_1$ fill in round $r$, then $z$ in round $r+1$ and $w_2$ in round $r+2$. The vertex $w_0$ must fill before round $r$, since otherwise $z$ would force it alongside $w_2$.

At time $r-1$, the blue vertex $w_0$ can have at most one white neighbor other than $z$, and that neighbor cannot be $w_1$ or $w_2$. If $w_0$ receives two attributions, this follows from the saturated degree-three description above. If it receives one, both $w_1,w_2$ are saturated and their incident edges leave no room for an edge to $w_0$. In this case the attribution to $w_0$ either comes from a permanently blue neighbor, or is a force from $w_0$ itself, whose only white neighbor in intact round one is its new target. In each case at most one neighbor besides $z$ can still be white at time $r-1$.

If no such neighbor remains white, $w_0$ would restore $z$ by round $r$. If such a white neighbor $x$ remains, it cannot fill in rounds $r$ and $r+1$, which add only $w_1$ and $z$. Then $w_0$ forces $x$ alongside the force into $w_2$ in round $r+2$. This contradicts the one-addition assumption. Thus a successful run with nine whites after round two finishes within ten rounds.

### Ten whites after round two

For $|D_2|=10$, all the inequalities in the round-two count are equalities. In particular $\Delta=m=3$, all four members of $D_1$ remain white, and each missed round-one target has exactly two new discrepancies attributed to it. The [finite replay](check_saturated_subcubic.py) proves that any successful delayed run in this case finishes within six more rounds. The following reduction explains why the replay covers arbitrary graph order.

After round two every vertex outside $D_2$ is blue forever. Its contribution is fully described by its set of neighbors in $D_2$. In each round it forces the sole white member of that set if one exists. A vertex in $D_2$ uses its neighbors within $D_2$ once it becomes blue.

Label the four old discrepancies by $z,w_1,w_2,w_3$. Each $w_i$ has two distinct new discrepancies associated with it, one of which is the target of an outside source. The other is the target of a second outside source or of $w_i$ itself. If $z$ acted in round one, relabel its target as $w_1$. The required edges and permanently blue sources are as follows.

- For each $w_i$ whose round-one source is not $z$, that source has exactly $\{z,w_i\}$ as its neighbor set in $D_2$. Its other neighbors were blue initially. For a target of $z$, use the direct edge $zw_1$.
- For each new discrepancy forced by an outside source in round two, that source contributes the two-element set consisting of $w_i$ and the new target. The source cannot neighbor another new discrepancy because only its chosen target is white in intact round one. It cannot neighbor another old discrepancy either. All the $z$ edges are occupied by the round-one choices, and every other $w_j$ uses its slots for its own predecessor and its own two attributions. The chosen sources for different new targets are distinct.
- A new discrepancy forced by $w_i$ itself uses a direct edge to $w_i$. All incident edges of $z,w_1,w_2,w_3$ have now been accounted for. Each of the six new discrepancies has used one incident edge, leaving at most two additional edges.

There are ten templates up to relabeling the three branches. When $z$ did not act there are four possible numbers of branches with a direct second edge. When it did act the branch $zw_1$ has two choices, and the other two branches have three possible counts. For each template the program enumerates direct edges among the six new discrepancies and extra neighbor sets of size one through three for permanently blue sources. Each extra incidence spends one of the two remaining slots at its endpoint. The program may drop duplicate blue neighbor sets because they give the same force in every round. A configuration without a singleton blue neighbor set stalls immediately, since all ten residual vertices start white.

The program checks 6,176,870 configurations with at least one singleton source. Of these, 5,921,708 finish, and the largest number of additional rounds is six. The largest total time in the ten-white case is therefore eight. The global subcubic bound is ten, using this enumeration for ten whites, the argument above for nine, and the white count itself for eight or fewer.

### Eight-round witness with all singleton losses recoverable

A connected 24-vertex subcubic graph in [the replay](check_single_loss_bounds.py) attains eight rounds with ten white vertices left after round two. Its initial blue set is $\{0,10,11,12,13,14,15,16,18,20,21,22,23\}$. Its intact time is two, and its minimum killing support $\{22,23\}$ has restricted time two. Without initial blue vertex $0$, the new blue sets in order are $\{19\},\{17\},\{4\},\{1,6\},\{2,5\},\{0,7,9\},\{3\},\{8\}$. The replay checks that every singleton loss recovers and that loss of both support vertices stalls. Together the lower and upper bounds put the overall maximum between eight and ten rounds.

## Reproduction

```sh
python -B research-twins/check_single_loss_bounds.py
python -B research-twins/check_saturated_subcubic.py
lake env lean -DwarningAsError=true research-twins/SingleLossBound.lean
```

The replay verifies both sharp examples and 147 instances of the unbounded family, using 49 path lengths and three variants of the lost vertex. The largest path has 100 vertices before $g$. It also checks 25,392 recoverable singleton cases with intact time at most one across all labeled simple graphs through order five. In 7,914 of those cases a blue twin of the lost vertex remains. On the same small graph range, the replay checks the degree-weighted inequality on 78,122 transitions and the refined round-two count on 51,658 singleton losses, including stalled runs. Three subcubic examples attain ten white vertices after round two, one of them at the sharp eight-round deadline. The Lean proof establishes the one-round upper bounds without a graph-order restriction.
