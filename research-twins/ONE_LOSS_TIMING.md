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

For maximum degree three and intact time at most two, this gives **15 rounds**. The [17-vertex certificate in the replay](check_single_loss_bounds.py) has maximum degree three, restricted time two, and delayed time seven. Its initial blue set is $\{0,1,2,6,7,9,11,12,14\}$, its killing pair is $\{0,11\}$, and its slow loss is $9$. The two bounds leave the best possible maximum-degree-three time open.

## Reproduction

```sh
python -B research-twins/check_single_loss_bounds.py
lake env lean -DwarningAsError=true research-twins/SingleLossBound.lean
```

The replay verifies both sharp examples and 147 instances of the unbounded family, using 49 path lengths and three variants of the lost vertex. The largest path has 100 vertices before $g$. It also checks 25,392 recoverable singleton cases with intact time at most one across all labeled simple graphs through order five. In 7,914 of those cases a blue twin of the lost vertex remains. The replay checks the degree-weighted inequality on 78,122 round transitions through intact completion on the same small graph range, including stalled delayed runs. The Lean proof establishes the one-round upper bounds without a graph-order restriction.
