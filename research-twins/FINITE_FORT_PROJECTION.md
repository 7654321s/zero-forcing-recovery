# Which base supports lift to finite forts?

Let $G$ be a finite simple graph. Give each oriented edge $uv$ an integer shift $\delta_{uv}$ with $\delta_{vu}=-\delta_{uv}$. In the integer-sheet lift, the neighbor of $(u,s)$ above $v$ is $(v,s+\delta_{uv})$. A fort is a nonempty vertex set such that no outside vertex has exactly one neighbor in it. A fort in the base can be the projection of a finite fort in this lift exactly when two systems of endpoint inequalities are feasible. In that case, a finite fort can be constructed with one interval of occupied sheets per selected base vertex.

## Earliest and latest sheets

Fix a nonempty projected support $U\subseteq V(G)$. Give each $v\in U$ an integer $a_v$. For every edge $uv$ with $v\in U$, require
$$
a_v-\delta_{uv}\;\geq\;
\min\bigl(
\{a_u:\ u\in U\}\ \cup\
\{a_w-\delta_{uw}:w\in U\cap N(u),\ w\ne v\}
\bigr).
$$
The minimum of the empty set is $+\infty$. The first term in the minimum represents the source label $u$, when it is selected. The other terms represent the alternative neighbors of the source.

If a finite fort projects to $U$, choose $a_v$ as the earliest occupied sheet above $v$. At sheet $a_v-\delta_{uv}$ over $u$, the copy above $v$ is a fort neighbor. Either the copy of $u$ itself belongs to the fort, or it has a second fort neighbor. In the first case $a_u$ is at most this sheet. In the second case the left endpoint from that other neighbor is at most this sheet. This proves the inequality. Reflection of the sheets negates the shifts and gives a second feasible system, using the negatives of the latest occupied sheets.

## Constructing a finite fort from the endpoints

Let $a$ solve the first system and let $b$ solve the system with negated shifts. Write $R=\max_{uv}|\delta_{uv}|$, with $R=0$ for a graph without edges. Set $T=\max_v a_v+R$ and $C=\max_v a_v+\max_v b_v+2R$. Put all copies of each $v\in U$ in the interval $[a_v,C-b_v]$ into the new fort. Seen from any adjacent source, each such shifted interval contains $T$.

Consider an outside vertex $(u,s)$ at $s\leq T$. Any selected neighbor has its shifted left endpoint at most $s$, and an unselected neighbor either has its left endpoint above $s$ or has no interval. If $u$ has an interval then its own left endpoint is above $s$. The inequality at a selected neighbor therefore forces a second selected neighbor. For $s\geq T$, the same argument applies after the reflection $s\mapsto C-s$, using $b$ and the negated shifts. This verifies the fort condition everywhere. Its seed cost for a lifted seed set is the sum of the interval lengths at the selected seed labels.

## A finite test

At a feasible assignment, choose one term witnessing each inequality. Rearranging gives difference inequalities of the form $a_v\geq a_w+c$ with $|c|\leq2R$. A directed cycle of positive total weight would contradict feasibility. Longest walk values from a new source joined to every selected label with weight zero therefore give a feasible assignment with values from zero through $2R(|U|-1)$. Walks can delete their repeated-vertex cycles without lowering weight, so the bound follows from the length of a simple path.

To decide feasibility, start all values at zero and repeatedly increase them to satisfy each violated lower inequality. Every right side is monotone in the current values, so these updates stay below any feasible nonnegative assignment. If a value exceeds $2R(|U|-1)$ the system is infeasible. If a pass makes no change, the current values give a solution. There are at most $2R|U|(|U|-1)$ strict updates before one of these outcomes. Apply this test in both directions. A successful construction occupies a span of at most $4R(|U|-1)+2R+1$ sheets.

For example, take a four-cycle with shifts zero on three consecutive edges and shift one on the last edge around the cycle. The pair of opposite labels forms a base fort. One outside label makes the two earliest sheets equal. The other makes them differ by one. The two conditions together exclude this projection for finite forts.

## The greatest attainable support

Suppose the search is run on an allowed label set $U$ and a test fails at a particular label $v$. No attainable subset of $U$ contains $v$. To see this, compare every intermediate update on $U$ to a feasible nonnegative assignment on any subset $W\subseteq U$. At an updated label in $W$, the minimum used by the update can only increase when its witness labels are restricted to $W$. By induction, the updates on $U$ remain below the feasible values at every label of $W$. A missing witness for $v$ on $U$ would also be missing on $W$. An update exceeding $2R(|U|-1)$ would exceed the bound for $W$ as well.

Remove the failing label and repeat the two directional tests. No attainable support is lost. If both tests succeed, the remaining set is attainable and contains all attainable subsets of the original allowed set. If the set becomes empty, there is no finite fort supported there. This takes at most $|U|$ removals. In particular, a finite fort anywhere in an integer-sheet lift can be detected in polynomial time for bounded shifts by using all base labels initially.

## Blocking numbers of the cyclic reductions

Fix a base seed set $S$ with intact time $t$. Its pullback forces each cyclic reduction and the integer-sheet lift in the same number of rounds. Suppose $R\geq1$ and put $D=(4t+2)R$. For a cyclic fort of seed cost $b$, each occupied sheet lies within $2tR$ of some selected seed sheet. This follows because the radius-$2t$ neighborhood of a vertex determines its color at round $t$. The corresponding $b$ sheet intervals cover at most $b(4tR+1)$ sheets and have at most $b$ complementary runs. If there is no run of $2R$ consecutive empty sheets, then $m\leq b(4tR+1)+b(2R-1)=Db$.

When $m>Db$, cut the cycle in the middle of $2R$ empty sheets. The resulting strip has $R$ empty sheets at each end. Edges span at most $R$ sheets, so all neighbors of selected vertices are represented in that strip and the fort becomes a finite fort of the same cost. Conversely the image of a finite fort is a fort under cyclic projection at no larger cost.

If finite forts exist and their minimum seed cost is $c$, the cyclic blocking number is exactly $c$ for $m>D(c-1)$. If no finite fort exists, the cyclic blocking number is at least $\lceil m/D\rceil$ and at most $m|S|$, so it grows linearly. The greatest-support algorithm decides which case holds without enumerating moduli. For zero shifts the sheets are disjoint copies of the base and the blocking number is constant.

For the four-cycle example above, the integer lift has no finite fort. In the cyclic reduction to $m$ sheets, lift two adjacent base seeds to obtain $m$ disjoint adjacent seed pairs, each separated from the next pair by two initially white vertices. An adjacent blue pair forces the entire cycle. To block recovery therefore requires deleting one seed from each pair, giving blocking number exactly $m$.

## Application to shorter prism chains

In the [signed unpadded prism chain](BLOCK_STABILIZATION.md), the finite blocking number is 24 for every fixed chain with at least 11 blocks. Its cyclic blocking number is also 24 at every sheet count of at least 34. The guarantee starts at 28 sheets for every chain with at least 24 blocks.

The finite result for at least 24 blocks follows from [block and sheet stabilization](BLOCK_STABILIZATION.md). To descend from $k+1$ blocks to $k$, consider a hypothetical finite fort of cost at most 23. If the fort has two successive empty appended stages, insert a new empty stage between them to preserve the cost. If the fort avoids all opening seeds, the opening fills from its own seeds in two rounds. The fort then avoids the opening and the old stage ports adjacent to it, so the opening insertion preserves its cost. Each insertion would produce a finite fort at the excluded budget on $k+1$ blocks.

In the remaining case the projection meets the opening seeds and every adjacent pair of appended stages. Its base seed count is at most 23 because every selected seed label costs at least one lifted seed. It also satisfies both endpoint systems. The verifier rules out these conditions together for each $k$ from 23 down through 11. It gives every base label two binary endpoint variables, each with enough bits to represent $2(|V(G)|-1)$, since the edge shifts have magnitude one. For each projected neighbor it requires a selected witness label and the corresponding shifted comparison in each direction. An extra bit handles the shift differences without overflow. The 24-seed witness inherited from the four-block chain supplies the upper bound throughout this range.

## A lower cyclic threshold for shorter chains

For each of the thirteen lengths from 11 through 23 blocks, the verifier checks the sheet bands of widths 10 through 13. The ten-sheet test permits five lost seeds and forces a consecutive pair of sheets in the core. The larger widths use the two overlapping shorter bands exactly as in the [26-block proof](BLOCK_STABILIZATION.md#a-smaller-sheet-threshold-for-long-chains), including the two-sheet margins. Thus each thirteen-sheet band of a wrapped fort contains at least nine seeds. Counting cyclic translates gives $9m\leq13b$ for a wrapped fort of cost $b$. At $m\geq34$ and $b\leq23$ this is impossible. The two empty sheets then give a finite fort of the same cost, excluded by the projected-support argument above.

The same checks extend through width 16 for the 11- and 15-block chains. There the inequality $12m\leq16b$ excludes a wrapped fort below cost 24 from 31 sheets onward. The inherited cost-24 fort supplies the matching upper bound at all these moduli.

## Reproduction

```sh
python -B research-twins/check_finite_fort_projection.py
```

The verifier tests all 61,440 nonempty supports in the weighted four-vertex cases with shifts in $\{-1,0,1\}$. It checks all intervals it constructs and independently brute-forces the endpoint inequalities on supports of size at most two. For each graph it compares the greatest support with the union of all accepted supports. It checks that the shifted four-cycle has no finite fort, and realizes the projection of the published prism fort.

The optional PySAT verifier checks the binary comparisons and replays the thirteen shorter-chain exclusions.

```sh
python -B research-twins/check_prism_projected_support.py
```

The sheet-band checks for the shorter chains can be replayed with the same verifier as at 26 blocks.

```sh
python -B research-twins/check_block_stabilization.py --band-blocks 11 12 13 14 15 16 17 18 19 20 21 22 23
python -B research-twins/check_block_stabilization.py --band-through 16 --band-blocks 11 15
```
