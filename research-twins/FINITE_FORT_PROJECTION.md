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

For the [signed unpadded prism chain](BLOCK_STABILIZATION.md), the finite blocking numbers at two and three blocks are 16 and 21. Every chain with at least four blocks has finite blocking number 24. The cyclic blocking numbers equal their finite values from eight sheets at two blocks, 22 sheets at three blocks, and 23 sheets at every length of at least four blocks.

The finite result for at least 24 blocks follows from [block and sheet stabilization](BLOCK_STABILIZATION.md). To descend from $k+1$ blocks to $k$, consider a hypothetical finite fort of cost at most 23. If the fort has two successive empty appended stages, insert a new empty stage between them to preserve the cost. If the fort avoids all opening seeds, the opening fills from its own seeds in two rounds. The fort then avoids the opening and the old stage ports adjacent to it, so the opening insertion preserves its cost. Each insertion would produce a finite fort at the excluded budget on $k+1$ blocks.

In the remaining case the projection meets the opening seeds and every adjacent pair of appended stages. Its base seed count is at most 23 because every selected seed label costs at least one lifted seed. It also satisfies both endpoint systems. The verifier rules out these conditions together for each $k$ from 23 down through 11. It gives every base label two binary endpoint variables, each with enough bits to represent $2(|V(G)|-1)$, since the edge shifts have magnitude one. For each projected neighbor it requires a selected witness label and the corresponding shifted comparison in each direction. An extra bit handles the shift differences without overflow. The 24-seed witness inherited from the four-block chain supplies the upper bound throughout this range.

## Four through ten blocks

The [two-, three- and four-block checks](MULTIPLE_LOSS_TIMING.md#saturation-of-the-blocking-number-in-cyclic-covers) establish the first three finite values. For each of five through ten blocks, the width-16 band test shows that a fort meeting every consecutive sheet pair within such a band must place at least 12 lost seeds in it. Take an inclusion-minimal finite fort of cost at most 23 if one exists. Two consecutive empty sheets inside its span would separate it into smaller forts, since an outside vertex cannot see across both empty sheets. Its span has at most 31 sheets, because a longer span would contain two disjoint width-16 bands and require at least 24 lost seeds.

Translate this fort to start on sheet one of the 33-sheet guarded strip. The [strip verifier](check_finite_fort_strip.py) uses the fort clauses, the two empty guards, an occupied first interior sheet, and no consecutive empty pair before the last occupied sheet. It also uses the local minimality and seed ancestry constraints. The six instances at budget 23 are unsatisfiable. The inherited 24-seed witness gives equality.

The same width-16 band check passes at four blocks. Counting cyclic translates in a wrapped fort gives $12m\leq16b$ for seed cost $b$. For $m\geq31$ and $b\leq23$, this inequality is impossible. An empty pair would turn the cyclic fort into the already excluded finite fort, so the common cyclic value is 24 at these sheet counts for four through ten blocks.

## A lower cyclic threshold for shorter chains

At every length from four through 23 blocks, the sheet-band verifier checks widths 10 through 28. The ten-sheet test permits five lost seeds and forces a consecutive pair of sheets in the core. The larger widths use the overlapping shorter bands and their complement bounds. A wrapped fort of cost $b$ must place at least 24 seeds in every 28-sheet band of its periodic lift. Counting over one period gives $24m\leq28b$, which excludes $b\leq23$ for $m\geq27$.

At 26 sheets and every length from four through 23 blocks, a 27-sheet band counts the full budget plus the seeds on one extra sheet. At $b\leq22$ each sheet would need a seed, contradicting $b\leq22<26$. At $b=23$, a 25-sheet band contains at least 21 seeds, so any single sheet contains at most two. The wrapped verifier excludes this remaining budget using the periodic band inequalities, the exact total of 23 seeds and the requirement that every adjacent pair of sheets meets the fort. For every window spanning more than half a period it encodes the equivalent upper bound on the complementary window. These checks cover all forts at that budget. A fort with two consecutive empty sheets unrolls, where the finite lower bound applies. The inherited 24-seed witness supplies the matching upper bound.

At 25 sheets, the width-26 band requires at least 22 seeds. Below budget 22 each sheet would again need a seed, which is impossible. At budgets 22 and 23 the width-24 band leaves respective caps of two and three seeds on each sheet. The same wrapped verifier excludes both budgets at every length from four through 23 blocks. Together with the finite lower bound, the common witness and the [long-chain result](BLOCK_STABILIZATION.md#the-25-sheet-case), this proves $\kappa_{k,m}=24$ for every $k\geq4$ and $m\geq25$.

At 24 sheets, the width-25 band requires at least 21 seeds. Below budget 21 this would force at least one seed on each sheet. At budgets 21, 22 and 23 the width-23 band leaves respective caps of two, three and four on a single sheet. The wrapped verifier excludes all three budgets at every length from four through 23 blocks. The [long-chain result at 24 sheets](BLOCK_STABILIZATION.md#the-24-sheet-case) then gives $\kappa_{k,m}=24$ for every $k\geq4$ and $m\geq24$.

At 23 sheets and four through 23 blocks, the width-24 band requires at least 20 seeds. Below budget 20, every sheet would again need a seed. At budgets from 20 through 23, the width-22 band caps the omitted sheet at two through five seeds. The wrapped verifier excludes all four budgets at each of these lengths. The [long-chain check at 23 sheets](BLOCK_STABILIZATION.md#the-23-sheet-case) gives the same value for every $k\geq24$, proving $\kappa_{k,m}=24$ for all $k\geq4$ and $m\geq23$.

At four and five blocks and 21 sheets, the width-22 band requires at least 18 seeds. Below budget 18 each sheet would need a seed. At budgets 18 through 23 the width-20 band leaves caps of two through seven on the omitted sheet. The wrapped verifier excludes all six budgets at each length, giving $\kappa_{4,21}=\kappa_{5,21}=24$.

At four through thirteen blocks and at 26 blocks, the width-23 band requires at least 19 seeds on a 22-sheet cover. Below budget 19, every sheet would need a seed. At budgets from 19 through 23 the width-21 band gives caps of two through six on the omitted sheet. The wrapped verifier excludes each budget at these lengths. The finite lower bound and the common witness give the value 24, and the budget-23 contraction and opening insertion extend it from 26 blocks to all $k\geq24$.

## Cyclic thresholds at two and three blocks

The width-25 band test passes at both lengths, yielding $21m\leq25b$ for a wrapped fort of cost $b$ on $m$ cyclic sheets. At two blocks it excludes all wrapped costs below 16 from 18 sheets. At three blocks it excludes all wrapped costs below 21 from 24 sheets. A fort with two consecutive empty sheets unrolls, and the respective finite lower bounds apply. The finite forts give cyclic upper bounds at every modulus by projection.

The [small-cover verifier](check_short_prism_covers.py) treats the two remaining sheet counts immediately below each range. At two blocks the wrapped budgets are 14 and 15 at 16 sheets, and 15 at 17 sheets. At three blocks they are 19 and 20 at 22 sheets, and 20 at 23 sheets. For every verified band width $w$, write $w=qm+r$ with $0\leq r<m$. Each such band counts the full seed cost $q$ times plus the seeds of an $r$-sheet window. The verifier therefore imposes a lower bound of $w-4-qb$ on that window. This keeps the periodic constraint useful even when the band width exceeds the period. It also bounds each sheet using the strongest window of length $m-1$ and rotates a sheet of maximum seed count to zero. The six wrapped formulas are unsatisfiable. The resulting cyclic values are 16 from 16 sheets at two blocks and 21 from 22 sheets at three blocks.

At two blocks the verifier also treats every period from one through 15. It starts at the integer lower bound from $21m\leq25b$ and checks all wrapped budgets below the exhibited upper bound. A full pair of seed fibers gives upper cost $2m$, and the projected finite witness gives upper cost 16. The verifier checks these witnesses and excludes all smaller costs. Together with the range from 16 sheets, this gives the exact value $\kappa_{2,m}=\min(2m,16)$ for every positive sheet count.

## Exact minimum spans in signed prism chains

The span of a finite fort is its largest occupied sheet minus its smallest occupied sheet plus one. A fort of span at most $w$ can be translated into the middle $w$ sheets of a cyclic cover with $w+2R$ sheets, where $R\geq1$ bounds the absolute edge shifts. Keep $R$ empty guard sheets on each side. An edge meeting the fort stays inside this strip, and all outside neighbor counts next to the fort agree with those in the integer lift. A fort within the proposed span exists exactly when the guards, colored blue initially, fail to force the whole cyclic cover. In that case the vertices left white are the largest fort in the interior strip.

For the signed prism chain, $R=1$. The two guards force the six interior sheets at each chain length from 6 through 11. At lengths of at least 12, a 51-round timetable works uniformly. At 12 blocks, the timetable consists of the opening and first appended stage, five copies of one ordinary stage timetable, and a suffix of five fixed stages. For a longer chain, insert more copies of the repeated timetable.

Every edge joins vertices within one stage or in consecutive stages in the cyclic order from the opening through the last appended stage and back to the opening. The [normalized stage description](BLOCK_STABILIZATION.md#the-prism-stage-labels) preserves the edges and shifts when an ordinary interior stage is repeated. A proposed force and all its prerequisites lie within the five consecutive stages centered at the target stage. The opening, first stage and terminal stage retain their types. Every five-stage window of types and timetables in the longer chain already occurs at length 12, where five repeated copies suffice for the window consisting solely of repetitions. The verifier checks that each noninitial vertex in the timetable has a source and other prerequisites with strictly earlier times. Induction on the assigned time therefore forces all six interior sheets in every longer chain.

The common cost-24 witness occupies seven sheets. Consequently the minimum span is seven for every chain with at least six blocks, and that witness attains both the minimum seed cost and the minimum span throughout this range. Each numerical entry below is the minimum seed cost among forts of span at most the column value.

| Blocks | Minimum span | 4 sheets | 5 sheets | 6 sheets | 7 sheets | 8 sheets |
| --- | --- | --- | --- | --- | --- | --- |
| 2 | 4 | 22 | 18 | 16 | — | — |
| 3 | 5 | no fort | 27 | 23 | 22 | 21 |
| 4 | 5 | no fort | 41 | 34 | 24 | — |
| 5 | 6 | no fort | no fort | 42 | 24 | — |

For each displayed numerical cost, the guarded fort formula is satisfiable at that cost and unsatisfiable one seed below it. Dashes mark spans omitted from the table. The least span among minimum-cost forts is six sheets at two blocks, eight at three blocks, and seven at every length from four blocks onward.

## The two shortest minimum-cost forts

For every chain with at least four blocks, up to translation of the sheet coordinate there are exactly two finite forts with seed cost 24 and span seven. The 46-vertex fort is the common four-block witness. Removing vertices $(43,4)$ and $(44,4)$ gives the 44-vertex fort. Both removed vertices are nonseeds, so the two forts give the same blocking set of 24 seeds. Both shapes use the opening and the first two appended stages.

For four through 27 blocks, put the two blue guard sheets around the seven interior sheets. Every fort in the strip avoids the vertices forced from the guards. The verifier imposes the fort clauses on the remaining candidates and a seed budget of 24. It forbids the exact membership assignments of the two displayed forts. The formulas are unsatisfiable at all 24 lengths, and the verifier checks both displayed witnesses at each length.

The 26-stage band extends this classification to every longer chain. With at most 24 seed-label losses, the restricted base forcing process still fills a pair of consecutive stages in the first 26 appended stages. The verifier checks the terminal and nonterminal band types at 27 and 28 blocks. Project a cost-24 fort's lost seeds onto base labels, retaining all lifted seeds outside those labels. The restricted base process lifts to the integer sheets, filling two consecutive appended stages disjoint from the fort. [Contract that pair](BLOCK_STABILIZATION.md#insertion-and-contraction). This preserves the seed cost and the sheet span. By induction, the contracted fort is one of the two displayed shapes. It meets both of the first two appended stages, so the retained empty stage has index at least three and the deleted stage was beyond the support. Expanding the chain preserves the same shape and seed labels.

## The eight-sheet minimum-cost forts

For every chain with at least four blocks, up to sheet translation there are exactly 40 finite forts of seed cost 24 and span eight. They occupy the last two appended stages and realize exactly two distinct 24-seed blocking sets. Their vertex counts range from 42 through 47. The two forts of span seven have 44 and 46 vertices and share one seed set near the opening.

The [verifier](check_finite_fort_span.py) lists 40 vertices common to the terminal shapes and nine optional vertices, all in coordinates relative to the start of the penultimate stage. It checks all subsets of the optional vertices at four blocks. In the guarded strip for each length from four through 27 blocks, the verifier requires the first and last interior sheets to be occupied. It then excludes every one of the 40 full membership assignments. The remaining formula at cost at most 24 is unsatisfiable at each length. The 40 displayed shapes are checked individually and yield the same two seed patterns in terminal coordinates.

At a longer length, contract an empty pair from the 26-stage band as above. The resulting fort meets both of the last two appended stages, so the deleted empty stage must precede them. This preserves the fort's terminal coordinates. Conversely, move any of the 40 patterns to the last two stages of a longer chain. The signed internal edges and the splice into the preceding stage have the same normalized description. The opening hub keeps its two links to the terminal stage. Thus every vertex next to the pattern has the same count of fort neighbors. All other outside vertices have count zero, and the seed labels on the pattern are unchanged. This gives the same 40 shapes and two seed sets at every length.

## The nine-sheet minimum-cost forts

For every chain with at least four blocks, up to sheet translation there are exactly 12 finite forts of seed cost 24 and span nine. They lie in the opening and the first two appended stages, have 50 through 54 vertices, and realize exactly two 24-seed blocking sets.

The verifier starts with 48 common vertices and tests the subsets of seven optional vertices. It checks the resulting 12 shapes and excludes every other membership assignment in the nine-sheet guarded strips at lengths from four through 27 blocks. Each displayed shape meets both of the first two appended stages and uses the same opening labels. Contraction of an empty pair in the first 26 appended stages therefore extends the exhaustive classification. The appended-stage edits beyond these shapes preserve their neighbors and seed labels.

Taken together, the spans of seven, eight and nine give 54 minimum-cost fort shapes and five distinct 24-seed blocking sets among the finite forts of span at most nine. Each seed set occupies both extreme sheets of its fort, so the sets counted at the three spans stay distinct under sheet translation.

## The forts supported by each of the five seed sets

Fix one of the five seed sets above and delete it from the original blue set. Every fort with that seed set remains white. The complement of the resulting forcing closure is itself a fort and is the unique largest one with that seed set.

After the intact two rounds, any vertex whose radius-four neighborhood misses the deleted seeds follows the intact process. The deleted seeds lie in at most nine sheets. Translate them to start on sheet five in a 19-sheet cover. The white set at round two lies within sheets one through seventeen, since edge shifts have magnitude at most one. After round two both guards are blue and the remaining dynamics agree with the integer lift inside the strip. The verifier computes these closures for each of the five seed sets at every length from four through 27. Each largest fort is one of the shapes already listed at the original span.

The 26-stage band extends this statement to every greater length. A finite fort on one of these seed sets has cost 24, so an empty pair may be contracted. Each seed set meets both stages of its occupied end of the chain. The contraction preserves their coordinates relative to that end, as well as the sheet coordinates. Hence any fort with one of the five seed sets retains its known span and belongs to its listed family. The family counts and their inclusion-minimal and maximal fort sizes are as follows.

| Span | Forts with that seed set | Vertices in its unique inclusion-minimal fort | Vertices in its largest fort | Sizes of independent optional groups |
| --- | --- | --- | --- | --- |
| 7 | 2 | 44 | 46 | 2 |
| 8 | 8 | 44 | 47 | 1, 1, 1 |
| 8 | 32 | 42 | 47 | 1, 1, 1, 1, 1 |
| 9 | 4 | 51 | 53 | 1, 1 |
| 9 | 8 | 50 | 54 | 1, 1, 2 |

In each row, start with the inclusion-minimal fort and add any subset of the listed groups. Within a group, all vertices are included together. The verifier groups optional vertices by the list of forts in which they occur. Each group has a binary choice. Since a family with $r$ groups has exactly $2^r$ distinct forts, every combination of choices occurs. The inclusion order within each family is therefore the Boolean lattice on its groups. Its fort-size polynomial is $x^a\prod_i(1+x^{d_i})$, where $a$ is the size of the least fort and $d_i$ are the group sizes. Summing over the five seed families gives

$$
P(x)=x^{44}(1+x^2)+x^{44}(1+x)^3+x^{42}(1+x)^5+x^{51}(1+x)^2+x^{50}(1+x)^2(1+x^2).
$$

## Recovery after restoring one seed

Delete one of the five listed seed sets and restore one of its 24 seeds at time zero. The synchronous recovery time is between six and 17 rounds. The distribution depends on the seed family and is the same at every chain length of at least four blocks. This holds in the integer lift and in every cyclic cover with at least 19 sheets.

| Fort span | Forts with that seed set | Pairs of (rounds, number of restoration choices) |
| --- | --- | --- |
| 7 | 2 | (6, 2), (7, 3), (8, 4), (9, 3), (10, 1), (11, 1), (12, 2), (13, 5), (14, 3) |
| 8 | 8 | (7, 3), (8, 4), (9, 2), (10, 5), (11, 2), (12, 1), (13, 4), (14, 2), (17, 1) |
| 8 | 32 | (7, 3), (8, 4), (9, 2), (10, 4), (11, 5), (12, 1), (13, 3), (14, 2) |
| 9 | 4 | (7, 2), (8, 1), (9, 1), (10, 1), (11, 4), (12, 2), (13, 3), (14, 5), (15, 3), (16, 1), (17, 1) |
| 9 | 8 | (8, 3), (9, 1), (10, 1), (11, 4), (12, 1), (13, 4), (14, 4), (15, 4), (16, 1), (17, 1) |

The radius-four neighborhood of the original deleted seed set contains all white vertices after round two. The colors on this neighborhood at that time depend on the induced radius-eight neighborhood and its initial blue vertices. Thereafter a force on any remaining white vertex uses vertices at distance at most six from the deleted seed set. Vertices outside the radius-four neighborhood are already blue, so the radius-eight data determine all subsequent forces on the remaining whites.

The seed sets are supported on an arc of at most three consecutive stages. A path of length eight can visit only this arc and its eight adjacent stages on either side. At $k\geq20$ these at most 19 consecutive stages have the same opening, terminal and ordinary stage types in the same order, with the same signed edges and seed labels. The radius-eight data therefore agree with the 20-block case under relative stage coordinates.

For the sheet comparison place the deleted seeds within sheets five through thirteen. The radius-four neighborhood is contained in sheets one through seventeen. In a cyclic cover with $m\geq19$ the first two rounds for vertices there depend only on sheets $-3$ through $21$. These sheets contain no period translate of the deleted seeds other than the original set. After two rounds, the two guard sheets zero and eighteen are blue, so all forces onto the remaining whites have the same sources and prerequisites as in the integer lift. The verifier checks the table on the 19-sheet cover for every length from four through 20 blocks.

## An inclusion-minimal loss of 25 seeds

The [restoration verifier](check_finite_fort_span.py) also lists a 25-seed loss supported on the opening and its first two appended stages. Its final white fort has 59 vertices and spans nine sheets. Restoring any one of the 25 seeds gives full recovery in ten to seventeen rounds. By monotonicity, every proper subset of the loss leaves a forcing set. This gives an inclusion-minimal blocker of size 25 that contains none of the cost-24 patterns.

The verifier checks the 25 restorations at each length from four through 20 blocks. The same stage and sheet locality argument extends the example to every length of at least four blocks, in the integer lift and in cyclic covers with at least 19 sheets. The seed set meets both extreme sheets of its span, so it gives $m$ distinct inclusion-minimal blocking sets of size 25 in each of those cyclic covers.

## All inclusion-minimal 25-seed losses

At four blocks there are exactly 22 inclusion-minimal blockers of size 25 up to sheet translation. There are exactly 20 at every length of at least five blocks. The span of a seed set is the number of sheets from its first occupied sheet to its last, inclusive.

| Blocks | Span 7 | Span 8 | Span 9 | Span 10 | Span 11 | Total |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 4 | 1 | 7 | 8 | 4 | 2 | 22 |
| At least 5 | 1 | 7 | 8 | 4 | 0 | 20 |

Any fort of cost at most 25 has no internal pair of empty sheets, since such a gap would split it into two forts of cost at least 24 each. A span of at least 34 would contain two disjoint 17-sheet bands, requiring at least 26 seeds. There are therefore at most 33 interior sheets, with one empty guard at each end. The [enumerator](check_cost_25_blocking_sets.py) searches the resulting 35-sheet strip and excludes every translate of each of the five minimum seed sets. A remaining fort has cost 25, and its seed set is inclusion-minimal because each proper blocking subset would have to be one of the excluded 24-seed sets. Conversely, any inclusion-minimal 25-seed loss contains the seed intersection of a fort, which must equal the loss. After finding one seed set, the enumerator excludes all its translates in the strip. Unsatisfiability after the last exclusion proves the count. The output gives the seed coordinates with the first occupied sheet normalized to one.

The enumeration at five blocks supplies four patterns meeting both terminal stages and 16 meeting the opening and its first two appended stages. At six through fourteen blocks the verifier moves the four terminal patterns to the last two stages, checks all 20 patterns by forcing closure with empty sheet guards, and excludes any additional set in the 35-sheet formula.

At 15 through 27 blocks, the projected-support verifier excludes cost at most 25 when every consecutive pair of appended stages meets the projection, using the two endpoint systems. At 28 blocks and above, the first 27 appended stages force an empty pair at budget 25. The verifier checks both possibilities for the last stage of that band, terminal at 28 blocks and ordinary at 29 blocks. The ordinary band is unchanged at greater lengths.

Contract an empty pair to preserve the fort and its retained seed coordinates. Each of the five 24-seed patterns meets both of its anchored appended stages, the first two for the opening patterns or the last two for the terminal patterns. If the retained empty stage belongs to that pair, the corresponding 24-seed pattern cannot be contained in the contracted loss. If it lies outside the pair, reinserting the empty stage preserves the anchor and carries any contained 24-seed pattern back to the original loss. Thus a contracted inclusion-minimal 25-seed loss remains inclusion-minimal. Iterate the contraction to fourteen blocks. Each resulting 25-seed pattern meets every stage in its anchored interval, so reversing each contraction keeps its opening or terminal coordinates. This proves that the 20 patterns exhaust all larger lengths.

The verifier also checks the 20 patterns at 15 through 20 blocks by forcing closure and exclusion of smaller losses. At greater lengths, the radius-eight argument from the restoration-time calculation applies to each anchored interval, which occupies at most three consecutive stages. The loss support of span $s$ can be checked on $s+10$ sheets with two empty guards. Containment of a 24-seed pattern is unchanged since its anchor is fixed relative to the same end and the opening and terminal label sets are disjoint from five blocks onward.

In the cyclic cover, every fort of cost at most 25 unrolls at $m\geq30$ for every $k\geq4$. Up through 27 blocks the width-25 band gives $21m>25\cdot25$. For greater lengths the 27-stage band permits contraction to 27 blocks while preserving the occupied sheets. The direct wrapped-budget tests at 25 through 29 sheets give the same unrolling result for $4\leq k\leq14$.

In these ranges, every inclusion-minimal 25-seed loss lifts to one of the listed finite patterns. Each listed finite loss also projects to an inclusion-minimal loss. It occupies at most 11 sheets, and any contained cost-24 pattern has span at most nine, so it can be lifted into the same interval. This also gives a unique longest empty gap. The cyclic count is $22m$ at four blocks and $20m$ at every greater length within the verified sheet ranges.

## The first two terms of the independent-loss probability

The enumerator also checks the unions of pairs of distinct translated 24-seed patterns. Exactly two unions of size 25 occur up to sheet translation, each containing two minimum patterns. Only relative shifts of magnitude at most eight can give such a union, since the two patterns must share a seed and each spans at most nine sheets. From five blocks onward the two ends have disjoint seed labels, so moving the terminal patterns preserves these overlaps. For $m\geq25$, these unions have the same counts per translation in the cyclic cover. Each union occupies an interval of at most 17 sheets. Its outer gap is longer than every interior gap and determines the lift.

Write $n=10km$ for the number of lifted seeds, with $q_4=22$ and $q_k=20$ for $k\geq5$. For the ranges covered by the cyclic size-25 classification, the number of 25-element losses that block recovery is

$$
5m(n-24)+(q_k-2)m.
$$

The first summand counts single extensions of the minimum losses. The overlap subtraction removes the $2m$ double counts, and the $q_km$ inclusion-minimal losses contribute separately. For independent seed losses with probability $p$, the first two nonzero terms at fixed $k,m$ are consequently

$$
\Pr(\text{blocking})=5m p^{24}+(q_k-2)m p^{25}+O(p^{26})
$$

## Overlap correction at order 26

Let $N_{26}(k,m)$ be the number of inclusion-minimal 26-seed losses in the cyclic cover. In the same ranges of $k$ and $m$ as the two-term probability formula, the coefficient of $p^{26}$ is

$$
[p^{26}]\Pr(\text{blocking})=
\begin{cases}
N_{26}(4,m)-16m & k=4,\\
N_{26}(k,m)-15m & k\geq5.
\end{cases}
$$

The enumerator forms all unions of the known 24- and 25-seed losses through size 26, up to sheet translation. Any two events in a union of that size share a seed, so a new event only needs to be tested at shifts whose bounding sheet intervals meet the current union. For each normalized union $U$, its signed coefficient is one minus the sum of coefficients of all strict subunions in $U$, counting each contained translate. This is the inclusion–exclusion coefficient because the sum over all union monomials contained in $U$ equals one when every seed in $U$ is lost. The verifier checks the coefficient sums at each degree, including $-16$ at four blocks and $-15$ at five blocks at degree 26. The same disjointness of the opening and terminal seed labels carries the latter coefficient to every greater length.

To lift a cyclic union of size at most 26, first place one constituent loss in the integer lift. Each other constituent shares a seed with it. Two choices of shared seed give shifts differing by a multiple of $m$ and by at most 20 sheets, so the placement is unique. The reference loss and any two other constituents have at least $3\cdot24-2\cdot26=20$ common seeds in the cycle. Those seeds also agree in the lifted placements. Each pair of lifted constituents therefore lies in an interval of at most 21 sheets. Since $m\geq25$, no two distinct sites from such a pair can coincide under projection, and the entire union lifts with its size unchanged.

The enumerated unions have span at most 11, which makes the outer gap unique and gives $m$ translates of each type. Each inclusion-minimal 26-seed loss contributes one new monomial of degree 26. Its union with a different inclusion-minimal loss has size at least 27.

## The exact third term at every chain length

There are exactly 104 inclusion-minimal 26-seed losses up to sheet translation at four blocks and 97 at every length of at least five blocks. A span of 35 sheets for a fort of cost at most 26 would contain disjoint width-17 and width-18 bands requiring $13+14=27$ seeds. The search therefore uses 34 interior sheets and two guards. It excludes every translate of each known 24- and 25-seed loss and then enumerates the size-26 losses as above. At six through fourteen blocks the verifier checks the 97 patterns inherited from five blocks, keeping the opening coordinates fixed and moving the terminal patterns. All nine additional instances exclude any further seed set.

| Blocks | Span 7 | Span 8 | Span 9 | Span 10 | Span 11 | Total |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 4 | 4 | 25 | 42 | 23 | 10 | 104 |
| At least 5 | 4 | 25 | 42 | 23 | 3 | 97 |

At five blocks the catalogue has 88 opening losses meeting the first three stages and nine terminal losses meeting the last two stages. The projected-support verifier excludes a fort of cost at most 26 meeting every adjacent pair of appended stages at 15 through 28 blocks. From 29 blocks onward the first 28 appended stages force an empty pair at this budget. The band check uses a terminal last stage at 29 blocks and an ordinary last stage at 30 blocks. The latter band also applies at every greater length.

Contract an empty appended stage pair. Each loss of size 24 or 25 meets all appended stages of its anchored interval. If that interval contains the retained empty stage, the contracted loss cannot contain the smaller pattern. If the interval avoids the retained empty stage, reinsertion carries any contained smaller pattern back with the same anchor. Thus contraction preserves inclusion-minimality. Iterating to 14 blocks gives one of the 97 patterns. Each meets every stage of its anchored interval, so its coordinates relative to that end remain unchanged on reversing the contractions. The verifier checks the existence of all 97 patterns through 20 blocks. They extend to every longer chain by radius-eight locality and by the disjoint opening and terminal labels.

Wrapped forts of cost at most 26 are excluded for $m\geq30$ at every length. For $m\geq31$ the width-28 bound gives $24m>28\cdot26$ at four through 24 blocks and at 26 blocks. The width-25 bound gives $21m>25\cdot26$ at 25, 27 and 28 blocks. The 28-stage band permits every chain of at least 29 blocks to contract to 28 while preserving its occupied sheets and seed cost. The direct checks below treat 30 sheets.

In these ranges each listed loss projects injectively because its span is at most 11. Any contained smaller cyclic blocking set would have to unroll, and its finite seed pattern has span at most 11, so it lifts into the same interval. Thus $N_{26}(4,m)=104m$ and $N_{26}(k,m)=97m$ for $k\geq5$. The independent-loss probabilities are

$$
\Pr(\text{blocking})=
\begin{cases}
5mp^{24}+20mp^{25}+88mp^{26}+O(p^{27}) & k=4,\\
5mp^{24}+18mp^{25}+82mp^{26}+O(p^{27}) & k\geq 5.
\end{cases}
$$

## Overlap correction at order 27

Let $N_{27}(k,m)$ count the inclusion-minimal 27-seed losses in the cyclic cover. Wherever the cyclic size-26 catalogue above applies, the fourth coefficient satisfies

$$
[p^{27}]\Pr(\text{blocking})=
\begin{cases}
N_{27}(4,m)-127m & k=4,\\
N_{27}(k,m)-120m & k\geq5.
\end{cases}
$$

The verifier includes the size-26 catalogue and forms unions through size 27. Every constituent spans at most 11 sheets. The same lifting argument applies because the reference and any two other constituents share at least $3\cdot24-2\cdot27=18$ seeds in a union of size at most 27. The spans of the resulting unions are at most 11, so each type gives $m$ translates. At four blocks there are 131 degree-27 union types of weight $-1$, two of weight zero and four of weight $+1$. At five blocks the respective counts are 124, two and four. Disjoint opening and terminal seed labels preserve these union weights when the terminal patterns move. A new inclusion-minimal 27-seed loss contributes one degree-27 monomial, and its union with any different minimal loss has size at least 28.

## The exact fourth term at every chain length

There are 277 inclusion-minimal 27-seed losses up to sheet translation at four blocks and 258 at every length from five blocks onward.

| Blocks | Span 7 | Span 8 | Span 9 | Span 10 | Span 11 | Span 12 | Span 13 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 4 | 5 | 64 | 110 | 68 | 28 | 1 | 1 |
| At least 5 | 5 | 64 | 109 | 66 | 14 | 0 | 0 |

Of the 258 losses at five blocks, 251 meet the first three stages, five meet both terminal stages, and two meet the opening and both terminal stages. For the mixed losses, the last two stages followed by the opening form a three-stage arc. The catalogues at six through thirteen blocks have the same seed coordinates relative to the opening and terminal stages as at five blocks. A fort of cost at most 27 has no internal empty sheet pair. If its span were at least 36, two disjoint width-18 bands would require at least 28 seeds. The verifier searches the resulting guarded strip with 35 interior sheets, excluding all translates of the known losses of sizes 24 through 26. It then excludes each newly found 27-seed loss in every translation, and ends with an unsatisfiable formula.

All 258 translated losses retain their blocking property and inclusion-minimality through 20 blocks. The check places the stage coordinates from the five-block catalogue relative to their end or ends and tests the resulting closure with two blue guards and excludes the smaller patterns. Every template occupies a cyclic arc of at most three stages. Radius-eight locality extends these witnesses to all greater lengths.

For 14 through 29 blocks the projected-support verifier excludes any cost-27 finite fort meeting every consecutive pair of appended stages. From 30 blocks onward the first 29 appended stages force an empty adjacent pair, by the band checks at 30 and 31 blocks. Contract such a pair. The smaller losses of sizes 24 through 26 occupy every appended stage of their anchored support. An occurrence after contraction either avoids the retained empty stage and lifts back with the same coordinates, or would require a seed in that empty stage. Thus contraction preserves minimality. Iterating to 13 blocks gives one of the 258 patterns. The same argument preserves coordinates when reversing the contractions, including for the two patterns using both ends. This proves finite completeness at all lengths.

For all $k\geq4$ and $m\geq30$ every fort of cost at most 27 unrolls. At four through 24 blocks and at 26 blocks the width-28 band gives $24m>28\cdot27$ for $m\geq32$. At 25, 27, 28 and 29 blocks the width-25 band gives $21m>25\cdot27$ for $m\geq33$. At 31 sheets those same bands already exclude cost 26 and below. At 30 sheets they exclude cost 25 and below, since $24\cdot30>28\cdot25$ and $21\cdot30>25\cdot25$. The wrapped checks exclude costs 26 and 27 at 30 sheets at every length through 29, cost 27 at 31 sheets, and cost 27 at 32 sheets for the four lengths using the narrower band. The 30-sheet tests at 25 and 29 blocks use certified bands through width 26. For every larger $k$, the 29-stage band contracts the cyclic fort to length 29 while preserving its cost and sheet occupancy. The wrapped verifier and the width-28 bounds give the following smaller sufficient periods at the listed lengths.

| Blocks | Verified from this many sheets |
| --- | ---: |
| 4–5 | 25 |
| 6–7 | 26 |
| 8 | 27 |
| 9–10 | 28 |
| 11–12 | 29 |

The enumerated losses retain their finite blocking property and minimality after projection. At four blocks, the guarded closures of all 277 losses are checked in a 31-sheet representative. With periodic losses, after two rounds each copy of the loss lies in a band of potential white vertices extending four sheets on either side. The initial colors within distance four of each vertex in that band depend on only the original copy of the loss, since the loss span is at most 13 and the period is at least 25. Different such bands are separated by at least four blue sheets. The later forcing inside each band therefore agrees with that from a single copy in the integer lift. The smaller cyclic losses unroll and cannot be contained unless a corresponding finite loss was contained. There are $277m$ size-27 losses at four blocks and $258m$ from five blocks onward. The fourth coefficient is $(277-127)m=150m$ at four blocks and $(258-120)m=138m$ at the other lengths. The cost-26 tests also lower the third-term threshold to 25 sheets at six blocks, 26 sheets at eight blocks, 27 sheets at nine blocks, and 28 sheets at eleven blocks.

## Overlap correction at order 28

In the regions of the exact cyclic size-27 classification, let $N_{28}(k,m)$ count all inclusion-minimal 28-seed losses. Then

$$
[p^{28}]\Pr(\text{blocking})=
\begin{cases}
N_{28}(4,m)-417m & k=4,\\
N_{28}(k,m)-399m & k\geq5.
\end{cases}
$$

The enumerator forms the translated unions through size 28 from the catalogues at sizes 24 through 27. The union supports span at most 13 sheets at four blocks and at most 11 from five blocks onward. The degree-28 union weights have these counts up to translation.

| Blocks | Weight $-2$ | Weight $-1$ | Weight zero | Weight $+1$ |
| --- | ---: | ---: | ---: | ---: |
| 4 | 3 | 463 | 35 | 52 |
| At least 5 | 3 | 443 | 35 | 50 |

At five blocks and above, the opening coordinates and shifted terminal coordinates preserve all seed-label coincidences among these events, including the mixed losses.

Every pair in a cyclic union of size at most 28 shares a seed, and any three share at least $3\cdot24-2\cdot28=16$ seeds. With constituent spans at most 13, each lift relative to a shared seed is unique at periods of at least 25. The three-way intersections ensure that each pair of lifted constituents intersects, so their combined span is at most 25. No selected sites then alias modulo the period. The enumerated unions span at most 13, and the unique outer gap gives $m$ distinct translates of each finite union. A size-28 minimal loss contributes one new degree-28 monomial, since its union with any distinct minimal loss has size at least 29.

## The fifth term for chains with at least five blocks

There are exactly 741 inclusion-minimal 28-seed losses up to sheet translation at each length of at least five blocks on the integer lift. Their spans from seven through eleven have counts 13, 129, 301, 218 and 80. At five through eleven blocks, a finite fort of cost at most 28 cannot split across two empty sheets, and a span of at least 37 contains disjoint bands of widths 18 and 19 requiring at least 29 seeds. The search uses 36 interior sheets and two blue guards. It excludes every translate of the complete catalogues at sizes 24 through 27 before enumerating. At six blocks, 733 patterns transfer by holding the opening and the first two appended stages fixed and moving the last two stages. Three others use four opening stages and five use three terminal stages. Holding each of those full supports fixed relative to its own end gives exactly the eight additional patterns from the six-block search. At seven blocks the same rules transfer all 741 patterns, and the guarded search excludes any further pattern.

For eight through eleven blocks, an empty adjacent appended stage pair allows contraction to the previous length. Every known pattern of size at most 28 occupies every stage in each of its anchored opening or terminal intervals. A pattern contained in the contracted loss must avoid the retained empty stage, so reinsertion preserves that containment with the same anchors. Any further minimal loss would therefore have a fort meeting every adjacent pair. The guarded searches with this additional condition exclude further losses at each of the four lengths.

For 12 through 30 blocks the projected-support exclusions give an empty adjacent appended pair at cost at most 28. The first 30 appended stages give such a pair at every larger length by the band checks at 31 and 32 blocks. Repeated contraction and the same containment argument give completeness at every length. All patterns are verified by guarded closure and smaller-loss exclusion through 21 blocks. They occupy cyclic arcs of at most four stages, so the radius-eight neighborhood of each end-anchored pattern repeats at all longer lengths.

For every $k\geq5$ and $m\geq30$, cyclic forts of cost at most 28 unroll. For $m\geq33$ width 28 suffices at five through 24 blocks and at 26 blocks since $24m>28\cdot28$. At 25 and 27 through 30 blocks width 25 suffices for $m\geq34$ since $21m>25\cdot28$. Direct wrapped checks exclude cost 28 at 33 sheets at those five lengths, at 32 sheets through 30 blocks, and at 31 sheets through 29 blocks. The direct checks at 25 and 29 blocks use width 26. At 30 blocks and 31 sheets an empty adjacent appended pair would contract to the excluded 29-block case. The wrapped formula requiring every such pair to be occupied is also unsatisfiable. At 30 sheets the direct wrapped checks cover every length from five through 30 blocks. The 30-stage band contracts all larger lengths to 30 blocks with the same occupied sheets and cost. At five through ten blocks the direct tests also exclude wrapping at cost 28 from 28 through 30 sheets.

All smaller costs already unroll in these ranges. Every finite pattern projects with a unique outer gap and can be recovered from that gap. Thus there are $741m$ distinct minimal 28-seed losses, and the degree-28 coefficient of the blocking probability is $(741-399)m=342m$.

The catalogue through size 28 also gives the next overlap correction. The normalized unions of degree 29 have weights $-2,-1,0,1,2$ with counts 28, 1812, 124, 273 and 5. From seven blocks onward the first four and last three stages are disjoint, so keeping the opening labels fixed and shifting the terminal labels preserves all seed coincidences with their sheet offsets. This preserves the union profile. All these unions span at most 11 sheets. Any two contributors share a seed and any three have at least $3\cdot24-2\cdot29=14$ seeds in common. The same lifting argument therefore identifies the signed correction on the cycle. At each length in its verified cyclic range the degree-29 coefficient is $N_{29}(k,m)-1585m$, where $N_{29}$ counts the inclusion-minimal 29-seed losses.

## The sixth term for chains with at least five blocks

There are exactly 1,982 inclusion-minimal 29-seed losses at every length of at least five blocks on the integer lift, up to sheet translation. A finite fort of cost at most 29 cannot have an internal gap of two empty sheets. If it spanned 38 sheets, two disjoint bands of width 19 would require at least $15+15=30$ seeds. The guarded searches at five through eleven blocks thus use 37 interior sheets and exclude every translate of the complete catalogues through size 28. The numbers of patterns of spans seven through twelve are 20, 316, 750, 616, 271 and 9.

The five-block catalogue uses the same opening and terminal intervals as at size 28. All 1,982 patterns transfer to lengths six through twelve by the same rules and pass guarded closure and smaller-loss checks. If a fort at six through eleven blocks has an empty adjacent appended stage pair, contraction gives a fort at the previous length whose seed set contains a classified minimal loss. The support of that minimal loss fills each of its anchored stage intervals and avoids the retained empty stage. Its reinsertion is therefore a known loss of size at most 29. The guarded searches with every adjacent pair occupied exclude the remaining possibilities at each of these lengths.

At twelve through 31 blocks the projected-support checks force an empty adjacent pair at cost at most 29, and the 31-stage bands at 32 and 33 blocks give the same conclusion at every longer length. Contraction to eleven blocks gives completeness. To extend the verified twelve-block witnesses to every larger length, insert an empty stage into a certified empty pair of the witness fort. The new stage and its adjacent stages are still empty. Any smaller pattern contained in the extended loss would avoid these empty stages and lift back to a contained pattern before insertion, with the same anchored intervals. Iterating the insertion preserves each witness and its minimality.

For every $k\geq5$ and $m\geq33$, cyclic forts of cost at most 29 unroll. Width 28 suffices at five through 24 blocks and at 26 blocks from 34 sheets since $24m>28\cdot29$. Width 25 suffices at 25 and 27 through 30 blocks from 35 sheets, and the direct wrapped checks cover these lengths at 34 sheets. At 31 blocks width 24 suffices from 35 sheets since $20m>24\cdot29$. At 34 sheets an empty adjacent appended stage pair would contract any wrapped fort to the excluded 30-block case. The wrapped verifier with width-24 bounds and every appended stage pair occupied excludes the remaining case. At 33 sheets and 31 blocks, contraction again excludes a wrapped fort with an empty appended pair. The width-25 check excludes the remaining case in which every appended pair meets the fort. Every longer chain contracts to 31 blocks at these costs.

The 35-sheet exclusion at 31 blocks also has a certificate using the narrower width-23 band. The 35 windows of width 23 contain at least 19 seeds each, with total $23\cdot29=35\cdot19+2$. The two surplus units therefore determine each possible window profile. Consecutive window counts differ by the incoming minus the outgoing sheet count, and $\gcd(35,23)=1$ determines the sheet counts up to the constant fixed by their sum. Enumerating the surplus profiles with the other band bounds gives at most one seed per sheet. The wrapped formula with this cap and every appended pair occupied is unsatisfiable.

The wrapped verifier also packs disjoint certified subwindows inside a longer window when their summed lower bound improves on every single subwindow. This adds valid count constraints before the fort search. The 34-sheet exclusion at 31 blocks has also been checked with these constraints and the width-25 band.

Direct wrapped checks also give the smaller sufficient period 28 at five through eight blocks, and exclude wrapping at 33 sheets for nine through 30 blocks except 26. At 26 blocks the width-34 band covers a complete 33-sheet period and one additional sheet. If a wrapped fort had cost at most 29, each window would need at least 30 seeds, forcing at least one seed on every sheet. This contradicts the total budget. The smaller costs already unroll in these ranges. There are therefore $1982m$ distinct 29-seed minimal losses, and the degree-29 coefficient of the blocking probability is $(1982-1585)m=397m$.

The signed unions of size 30 from the catalogues through size 29 have weights $-2,-1,0,1,2$ with respective counts 73, 5536, 723, 1743 and 39 up to translation. The overlapping-union profile is checked directly at five, six and seven blocks, and the disjoint opening and terminal label intervals preserve it at every greater length. The same cyclic lifting argument applies since the union span is at most twelve sheets and any three constituents have at least $3\cdot24-2\cdot30=12$ shared seeds. Writing $N_{30}(k,m)$ for the number of inclusion-minimal 30-seed losses, the degree-30 coefficient at these periods is $N_{30}(k,m)-3861m$.

## The exact degree-30 term at five blocks

There are exactly 5,975 inclusion-minimal 30-seed blocking losses on the five-block integer lift, up to sheet translation.

| Seed span in sheets | 7 | 8 | 9 | 10 | 11 | 12 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Number of loss types | 47 | 679 | 2,001 | 2,136 | 998 | 114 |

A fort costing at most 30 cannot have two consecutive empty interior sheets, since the two sides would be forts of cost at least 24 each. A span of at least 39 sheets contains disjoint bands of widths 19 and 20, which together require at least 31 seeds. The exhaustive search uses the remaining 38 interior sheets and two blue guards. It excludes every translate of the 3,103 minimal losses of sizes 24 through 29. After enumerating the 5,975 size-30 types and excluding all their translates, the formula is unsatisfiable. Each reported type also passes a direct forcing-closure check and the smaller-loss containment check.

At five blocks all cyclic forts costing at most 30 unroll from 28 sheets. The direct wrapped checks exclude cost 30 on 28 through 35 sheets. The width-28 band gives $24m>28\cdot30$ for $m\geq36$, and the smaller costs already unroll from 28 sheets.

Every size-30 type and every smaller type spans at most 12 sheets. Aligning two representatives at a common seed leaves sheet differences of magnitude at most 11. At $m\geq28$, congruence of two such differences implies equality. Thus projecting a finite size-30 type cannot create a contained smaller minimal loss. Its outer gap is strictly longer than any internal gap, giving $m$ distinct translates, and any minimal cyclic loss lifts to a finite type. The overlap correction from the smaller types is $-3861m$, so for $k=5$ and $m\geq28$,

$$
M_{30}(5,m)=5975m,\qquad
[p^{30}]\Pr(\text{blocking})=2114m .
$$

The degree-30 coefficient of the logarithmic recovery probability is $-2114m$, since blocking starts in degree 24.

The [compressed JSON catalogue](five-block-loss-catalogue.json.gz) contains the 9,078 normalized types at five blocks through size 30. Each site is a pair of a base vertex label and a sheet coordinate. Base vertex labels start at zero and the first occupied sheet is normalized to one. The witness replay checks the archived sets by guarded forcing and recomputes the signed union correction and all seven coefficients per sheet. The exhaustive replay additionally excludes any unlisted minimal loss, checking each size with all translates of the archived patterns of that size and every smaller size forbidden.

## A finite representative for the degree-30 boundary term

Let $A_{30}(13)$ count the inclusion-minimal 30-seed blocking losses on the 13-block integer lift, up to sheet translation. The guarded search gives $A_{30}(13)=6055$, hence $\beta_{30}=A_{30}(13)-130=5925$. For every $k\geq13$ and $m\geq41$,

$$
M_{30}(k,m)=m(10k+5925),\qquad
[p^{30}]\Pr(\text{blocking})=m(10k+2064).
$$

The coefficient $[p^{30}]\log R_{k,m}(p)$ is the negative of the second expression because blocking starts in degree 24. The thirteen-block catalogue records 47, 679, 2,001, 2,152, 1,062 and 114 types of sheet spans 7 through 12. Two enumerations at 14 blocks agree on all 6,065 types and give the same intercept. The [compressed thirteen-block catalogue](thirteen-block-size-30-catalogue.json.gz) supports direct witness replay and an exhaustive check for an unlisted loss.

The projected-support checks give two consecutive empty appended stages in every finite fort of cost at most 30 at lengths 11 through 32. For every larger length the first 32 appended stages give an empty pair by the terminal and nonterminal band checks at 33 and 34 blocks. A fort cannot have two distinct runs of at least two empty stages in the cyclic stage order. The occupied portions between two such runs would each be nonempty finite forts, because every edge changes the stage by at most one and an outside vertex cannot see both portions. Each portion costs at least 24 seeds. Contracting an empty appended pair therefore shortens the unique run of at least two empty stages. It preserves the length of the occupied arc complementary to this run. Repeated contraction reaches 10 blocks with at least one empty stage remaining, so the original occupied arc spans at most nine stages.

Contraction preserves the sheet support. Stop at 13 blocks to apply the sheet-band checks. A finite fort has no internal pair of empty sheets by the same splitting argument. At 13 blocks a 19-sheet band meeting every consecutive pair costs at least 15 seeds, and a 20-sheet band costs at least 16. Disjoint bands of these widths exclude a span of 39 or more sheets. Thus for $k\geq13$ every finite fort of cost at most 30 fits into 38 consecutive sheets. In an inclusion-minimal loss the selected seeds are exactly the seed intersection of its final white fort. The guarded strip enumerator can therefore compute $A_{30}(13)$ with 38 interior sheets and two guards by excluding every translate of the complete catalogues through size 29 before running the cost-30 search.

The stage test uses a two-round forcing proof for each vertex with the seeds intact. For a vertex forced at a later round, take a source from an earlier round and recursively include the seeds needed to color the source and its other neighbors. The verifier checks at 13 blocks and 13 sheets that these seed ancestors always lie in the vertex's own stage or the next one. Each such proof lies within graph distance four. In the stage coordinate those windows span at most nine positions, and all ordinary placements and exceptional offsets already occur at 13 blocks. The 13-sheet period contains the whole window around the tested vertex on the integer lift. Thus the same ancestry property holds at every longer length. With losses confined to an arc of $s$ stages, any fort with seeds among these losses lies in the arc extended one stage backward.

In particular, a size-30 inclusion-minimal loss spans at most nine stages by the fort bound. At $k\geq13$ its outer stage gap has length at least four. Three consecutive seed-free stages between two lost seeds inside the support arc would leave the first two stages empty in the fort by the ancestry property. Together with the empty stages in the outer gap, this would split the fort into two of cost at least 24 each. Thus the outer gap is unique and determines the start of a normalized loss template.

For a template of span $s$, the possible fort occupies at most $s+1$ stages. Only vertices in these stages and their immediate stage neighbors can participate in a fort constraint. This uses a window of $s+3\leq12$ stages. Minimality is checked by excluding contained losses of sizes through 29. Each smaller pattern meets an exceptional stage, spans at most four stages, and has fixed labels relative to its end of the chain. Such a pattern cannot straddle the outer gap of length at least four, so the same stage window also decides containment. There are $k-(s+4)$ ordinary positions for this window and $s+4$ positions indexed by fixed offsets from the two exceptional stages. The ordinary placement weights and the weights at each offset are independent of $k$. This gives an affine count from $k=13$ by the [fixed-order placement argument](#eventual-counts-at-every-fixed-loss-order). Its slope is ten by the [ordinary classification](#blocking-losses-in-ordinary-stages).

Four consecutive sheets with all of their seeds intact separate the remaining white vertices across the middle of the four sheets by round five. Specifically, there is no pair of white vertices at graph distance at most two across the cut. The verifier starts with just the seeds in the four sheets and checks every crossing pair on 31 sheets at lengths 13 through 27. For a pair at distance at most two, the two round-five decisions and the path between the pair are determined within radius twelve of either endpoint. The sheet windows are well inside the representative's 31 sheets. In the stage coordinate, the radius-twelve window spans at most 25 positions. At 27 blocks the window realizes all ordinary placements and all offsets from the adjacent exceptional stages that can occur in any longer chain. The certificate therefore applies to the integer lift at every $k\geq13$. If four seed-free sheets lay inside the seed support of a finite fort of cost at most 30, both sides would be nonempty. The certificate prevents any outside vertex from seeing both sides, so each side is itself a finite fort of cost at least 24. Thus every internal gap in the seed support has length at most three.

To compare with cyclic covers, the same 32-stage bands contract a cyclic fort of cost at most 30 down to 32 blocks when necessary. The contraction preserves cost and the set of occupied sheets. Use the width-28 bands at 13 through 24 blocks and at 26, the width-25 band at 25, and the width-15 bands at 27 through 32. For a cyclic fort meeting every adjacent sheet pair, summing the width-$w$ window counts gives $(w-4)m\leq w\cdot30$. For each of these widths this is impossible at $m\geq41$. The weakest inequality comes from width 15, since $11\cdot41>15\cdot30$. Thus every cyclic fort at these costs unrolls. A cyclic inclusion-minimal loss has a finite lift that is also minimal, since a smaller finite blocking subset would project to a smaller cyclic blocking subset.

The thirteen-block catalogue gives sheet span at most 12. Near the exceptional stages the template transfer preserves sheet coordinates. In the ordinary interior the ten known templates also have sheet span at most 12. Thus the same bound holds throughout the affine range. At these periods any finite size-30 loss projects to a blocking loss with a unique outer gap. If its projection contained a smaller cyclic minimal loss, unroll that loss and align the two at a shared seed. Each pattern has sheet span at most 12, so each difference from the shared seed has magnitude at most 11. Congruence modulo $m\geq41$ then implies equality, which would put the smaller loss inside the original finite one. Hence the projections are minimal, and there are $m$ distinct translates of each type. The correction $-3861m$ from smaller losses gives the coefficient above.

## Independent losses on growing covers

Let $p$ be the independent loss probability of each designated seed. Define

$$
A_4(p)=5p^{24}+20p^{25}+88p^{26},\qquad
A_k(p)=5p^{24}+18p^{25}+82p^{26}\quad (k\geq5).
$$

There are constants independent of $k$ and $m$ such that for $k\geq4$, $m\geq30$ and $0\leq p\leq1$,

$$
\Pr(\text{blocking})=1-\exp(-m A_k(p))+O(km p^{27}).
$$

Put $c_4=150$ and $c_k=138$ for $k\geq5$. For all $k\geq4$ and $m\geq30$, the complete size-27 catalogue gives

$$
\Pr(\text{blocking})=1-\exp\bigl(-m(A_k(p)+c_kp^{27})\bigr)+O(kmp^{28}).
$$

For the finitely many chain lengths in the table, this holds from their listed periods with error $O(mp^{28})$. For all $k\geq4$ and $m\geq33$ the uniform error also improves to $O(mp^{28}+kmp^{30})$, by the ordinary interior threshold below. In particular, if $p\to0$, $m\to\infty$, $mp^{24}\to\lambda<\infty$ and $kp^6\to0$, the blocking probability tends to $1-e^{-5\lambda}$. If $mp^{24}\to\infty$, the probability tends to one for any sequence of chain lengths $k\geq4$. For the latter claim, take disjoint consecutive nine-sheet intervals and place one minimum blocking pattern in each. The $\lfloor m/9\rfloor$ occurrences use disjoint seed sites and each has probability $p^{24}$.

For $k\geq5$ and $m\geq30$, the size-28 catalogue gives the uniform refinement

$$
\Pr(\text{blocking})=1-\exp\bigl(-m(A_k(p)+138p^{27}+342p^{28})\bigr)+O(kmp^{29}).
$$

For $m\geq33$ the error improves to $O(mp^{29}+kmp^{30})$. The complete size-29 catalogue has $1982m$ events, so their total probability is at most $1982mp^{29}$. Larger losses give the second term of the error by the connected loss bound.

### Separate loss components

Suppose the intact seed set of any finite graph colors every vertex by round $t$. Simultaneous forcing updates a vertex using only the previous colors at distance at most two. At round $t$, all white vertices are therefore within distance $2t$ of some lost seed. Join two distinct seed sites in an auxiliary graph when their distance in the original graph is at most $4t+2$. For a specific loss, take the components induced by its lost sites in the auxiliary graph.

The radius-$2t$ neighborhoods of distinct components are at distance greater than two from each other. For a vertex in the neighborhood of one component, losing that component alone gives the same color at round $t$ as the full loss. Every seed from another component is farther than $2t$ from the vertex. Outside the union of the neighborhoods all vertices are blue by round $t$. A later update at a white vertex cannot consult a different component's neighborhood within distance two. By induction over rounds, the final white set is the union of the final white sets produced by the separate component losses.

In particular, every inclusion-minimal blocking loss is connected in the auxiliary graph. If its maximum degree is $D\geq1$, then among $n$ seed sites there are at most $n D^{2(d-1)}$ connected $d$-element sets. A rooted spanning tree of each such set admits a traversal of length $2(d-1)$ that visits precisely the set, so it suffices to count walks of that length. Any larger connected loss contains a connected $d$-element subset. Under independent losses the probability of containing any blocking set that is inclusion-minimal and has size at least $d$ is at most $nD^{2(d-1)}p^d$. For the prism cover, $t=2$, $n=10km$, and the original graph is cubic, so $D\leq3(2^{10}-1)$.

### A uniform exponential approximation

Use all translated inclusion-minimal blocking patterns of size at most $r$, with $r=26$, 27, 28 or 29 in the ranges of the corresponding exact cyclic classification. The largest catalogue has $3103m$ events, each supported within 13 consecutive sheets. Let $X_i$ indicate that every seed in the $i$th pattern is lost and order the events arbitrarily. Define $Y_i$ to be one when $X_i=1$ and all earlier events sharing a seed with event $i$ are absent, and zero otherwise. The earliest occurring event always has its $Y_i=1$, so the two families have the same union event. If $Y_i=Y_j=1$ for distinct $i,j$, their original patterns are disjoint. Thus $\mathbb E Y_i\leq p^{24}$ and $\mathbb E(Y_iY_j)\leq p^{48}$.

Each $Y_i$ depends on seed coins in an interval of at most 37 sheets. If the pattern starts at sheet $a$, any overlapping pattern starts within twelve sheets of $a$ on the cycle, and ends by sheet $a+24$ in those coordinates. Only a bounded number of the other intervals intersect this one, since the number of pattern starts per sheet is bounded. Intervals disjoint from it use independent seed coins. For $W=\sum_i Y_i$, the independent neighborhoods give $b_3=0$ in the Chen–Stein bound, and $b_1+b_2=O(mp^{48})$ by the one- and two-event bounds. Consequently $\Pr(W=0)=\exp(-\mathbb EW)+O(mp^{48})$ with a uniform constant. [Arratia, Goldstein and Gordon, Theorem 1](https://doi.org/10.1214/aop/1176991491)

The coefficients of $\mathbb EW$ through degree $r$ agree with those of $\Pr(W>0)$. For each fixed $k,m$, their difference is bounded by the sum of $\Pr(Y_i=Y_j=1)$ over all unordered pairs, which has order at least 48 in $p$. Also, the difference between $\Pr(W>0)$ and the full blocking probability is at most $10km D^{2r}p^{r+1}$ by the component bound. For the refined error at $r=27$ and $m\geq37$, a minimal blocking set of size 28 or 29 must contain a seed within six stages of an exceptional stage. Otherwise its late white set is supported in ordinary stages with ordinary neighbors, and the cyclic form of the ordinary exclusion applies. Such anchored sets have only $O(m)$ choices because a connected support of bounded size through one seed is counted by bounded-length walks. Losses of size at least 30 contribute at most $O(kmp^{30})$. Thus the computed blocking coefficients through degree $r$ determine the corresponding coefficients of $\mathbb EW$.

To control the remainder uniformly, expand each $\mathbb E Y_i$ by inclusion–exclusion over its earlier overlapping patterns. There is a uniformly bounded number of these earlier patterns, and each intersection has probability $p^u$ where $u$ is the number of distinct lost seeds it requires. The sum of the absolute contributions of degrees at least $r+1$ is $O(p^{r+1})$ per event, with a uniform constant. Hence $\mathbb EW$ equals $mA_k(p)$, with $c_kmp^{27}$ added for $r=27$, up to $O(mp^{r+1})$. The map $x\mapsto e^{-x}$ is 1-Lipschitz on $[0,\infty)$. Combining its error with the Chen–Stein error and the component bound gives the stated approximations. The case $p=0$ holds directly, as does any case with $\mathbb EW=0$.

## Eventual counts at every fixed loss order

Write $M_d(k,m)$ for the number of inclusion-minimal $d$-seed blocking losses in the signed prism cover and $R_{k,m}(p)$ for its independent-loss recovery probability. For each fixed $d\geq1$ there are integers $\alpha_d\geq0,\beta_d$ and rationals $\gamma_d,\delta_d$ such that

$$
M_d(k,m)=m(\alpha_d k+\beta_d),\qquad
[p^d]\log R_{k,m}(p)=m(\gamma_d k+\delta_d)
$$

for all $k,m\geq20(d-1)+19$. The logarithm is expanded at $p=0$, where $R_{k,m}(0)=1$. These identities reduce the eventual dependence on the two cover dimensions at a given order to two constants for each quantity.

First, a connected set of at most $d$ seed sites in the auxiliary graph has a spanning tree of at most $d-1$ edges. Each edge is realized by a path of length at most ten in the original graph. The union of the paths has at most $L=10(d-1)$ edges and connects the seed sites. Each original edge advances by at most one in the cyclic stage coordinate and at most one in the sheet coordinate. Thus the occupied coordinates in each cycle fit in an arc of at most $L+1$ positions. At the stated dimensions the long empty gap outside such an arc is unique. The first occupied position after it fixes the start in that coordinate.

A normalized loss template therefore has fixed offsets within a rectangle of at most $(L+1)\times(L+1)$ coordinate positions, with a vertex label within its stage for each seed. Blocking and the outcomes for all its subsets are determined by the induced radius-eight neighborhood of the template, with its intact seed colors. At time two the white vertices are within distance four of the lost sites, and their colors depend on the initial state within distance eight. Every subsequent update at a remaining white vertex uses only distance two from it. This radius-eight information fits in the template's rectangle enlarged by eight positions on each side in both coordinates.

For a normalized template spanning $s$ stages, the enlarged stage arc has length $h=s+16$. Its two exceptional stages, when present, are the terminal stage and the opening immediately after it in the cyclic order. At all starts whose enlarged arc avoids these two stages the resulting local graph and the template have the same coordinates in ordinary stages. There are $k-(h+1)$ such starts. The other $h+1$ starts are indexed by fixed offsets from the two exceptional stages and each gives local data independent of $k$. A start is valid only if its requested vertex labels are designated seed sites. The stage data apply equally to every sheet translation, giving $m$ possible starts in the sheet coordinate. The dimensions ensure the enlarged arcs do not cover either cycle. The stage graph and signs in these neighborhoods follow the labeled port rules. [Prism stage labels](BLOCK_STABILIZATION.md#the-prism-stage-labels)

For $M_d$, give each valid placement weight one if it is inclusion-minimal and blocking, and zero otherwise. All inclusion-minimal losses belong to the connected sets considered above. Each normalized template has a constant weight at its $k-(h+1)$ ordinary placements and at each exceptional offset. Summing these weights gives the first identity.

For the logarithmic coefficient, first use an independent loss variable $p_v$ for each seed $v$. For a monomial with support $S$, set every variable outside $S$ to zero. The component decomposition proves that the recovery probability with losses allowed only in $S$ factors over the components of $S$ in the auxiliary graph. The formal logarithm is a sum over those factors, so the coefficient vanishes when the monomial uses variables from more than one component. Every contributing support of total degree $d$ therefore fits in the same rectangle as before. Decorate each template with the positive integer exponent of its variable at each site, with the exponents summing to $d$. Its coefficient is computed by the local recovery polynomial with only those variables active, and so depends on the same radius-eight data. Summing the coefficient weights over ordinary and exceptional placements and then setting each $p_v=p$ gives the second identity. The exponents may exceed one because the formal logarithm is taken before the common specialization.

### Analytic recovery rate for growing covers

The fixed-order coefficients of the logarithmic recovery probability define convergent series

$$
F(p)=\sum_{d\geq1}\gamma_d p^d,\qquad G(p)=\sum_{d\geq1}\delta_d p^d
$$

in a disk of radius independent of the cover dimensions. Let $D=3(2^{10}-1)$ and $\rho=1/[16e(D+1)]$. For $k,m\geq19$ put $r=1+\lfloor(\min(k,m)-19)/20\rfloor$. For $|p|\leq\rho/2$ one has

$$
\log R_{k,m}(p)=km F(p)+mG(p)+O\left(km(|p|/\rho)^{r+1}\right).
$$

In particular $F(p)$ is the limit of $(km)^{-1}\log R_{k,m}(p)$ when both dimensions tend to infinity. An ordinary support first blocks at size 30 and contributes the negative of its minimum-loss count to the logarithmic coefficient at that order. The classification below therefore gives $F(p)=-10p^{30}+O(p^{31})$. The cyclic coefficients through order 29 give $G(p)=-5p^{24}-18p^{25}-82p^{26}-138p^{27}-342p^{28}-397p^{29}+O(p^{30})$.

For the uniform analytic bound, let $H$ be the auxiliary graph on the seed sites and let $U$ be any subset of those sites. Write $Z_U(z)=\sum_L z^{|L|}$, summing over losses $L\subseteq U$ that allow recovery. The component decomposition says that such a loss is exactly a collection of connected, individually recoverable sets that are pairwise disjoint and nonadjacent in $H$. This gives a compatible-polymer partition function. [Kotecký and Preiss](https://doi.org/10.1007/BF01211762)

For $v\in U$, separating the term where $v$ survives from those where its loss component is $C$ gives

$$
Z_U=Z_{U\setminus\{v\}}+
\sum_{\substack{v\in C\subseteq U\\ C\text{ connected and recoverable}}}
z^{|C|}Z_{U\setminus N_H[C]},
$$

where $N_H[C]$ includes $C$ and all its neighbors in $H$. The number of connected $s$-sets containing $v$ is at most $(4D)^{s-1}$. Encode a rooted spanning tree by the forward and return steps of its depth-first traversal. The sequence has $\binom{2s-2}{s-1}\leq4^{s-1}$ possibilities, and there are at most $D$ choices for each forward edge. The code and the root determine the visited set. [Connected-set count](LOSS_COMPONENTS.md#a-bounded-degree-search)

Let $\varepsilon=1/[2(D+1)]$. Inductively, for every proper subset $V$ and $u\in V$, the ratio $Z_V/Z_{V\setminus\{u\}}$ differs from one by at most $\varepsilon$. In the recurrence, the ratio $Z_{U\setminus N_H[C]}/Z_{U\setminus\{v\}}$ deletes at most $(D+1)|C|$ vertices from a proper subset. Its modulus is at most $(1-\varepsilon)^{-(D+1)|C|}\leq e^{|C|}$. Thus

$$
\left|\frac{Z_U}{Z_{U\setminus\{v\}}}-1\right|
\leq \frac{e|z|}{1-4eD|z|}<\varepsilon
\quad\text{for } |z|\leq 1/[8e(D+1)] .
$$

The empty-set value is one, so the induction proves nonvanishing. For $|p|\leq\rho$, one has $|p/(1-p)|\leq2\rho$. With $U$ the full set of $N=10km$ seed sites, $R_{k,m}(p)=(1-p)^N Z_U(p/(1-p))$. The logarithm with value zero at $p=0$ is the sum of $N\log(1-p)$ and the logarithms of the successive vertex-deletion ratios. Its modulus is at most $2N$ on $|p|\leq\rho$.

Cauchy's bound now gives $|[p^d]\log R_{k,m}|\leq20km\,\rho^{-d}$. In the coefficient identity above, fix $m\geq20(d-1)+19$ and send $k$ to infinity to obtain $|\gamma_d|\leq20\rho^{-d}$. Taking $k=m=20(d-1)+19$ then gives $|\delta_d|\leq40(20(d-1)+19)\rho^{-d}$. These bounds prove convergence of both series for $|p|<\rho$. The coefficients agree through degree $r$, and summing the remaining geometric tails, with their linear factors in $d$, gives the stated error since $r+1\leq k$.

### The two-dimensional rate at any fixed loss probability

For the signed prism family and every $0<p<1$, the limit

$$
\Phi(p)=\lim_{k,m\to\infty}\frac{\log R_{k,m}(p)}{km}
$$

exists. Let $H_{a,c}(p)$ be the probability of recovery when losses are confined to an $a$-stage by $c$-sheet rectangle of the infinite ordinary graph. This graph repeats the ordinary stage labels and port edges in both coordinates. Put $Q=(a+2)(c+4)$. Then

$$
\frac{\log H_{a,c}(p)+10(Q-ac)\log(1-p)}{Q}
\ \leq\ \Phi(p)\ \leq\ \frac{\log H_{a,c}(p)}{ac}.
$$

The width of the interval is at most $10[-\log(1-p)](1-ac/Q)$. A rectangle containing an ordinary cost-30 fort has $H_{a,c}(p)<1$, so $\Phi(p)<0$. For small positive $p$, $\Phi(p)=F(p)$ by the analytic estimate above.

The intact ordinary graph recovers within two rounds by locality of the intact traces in finite covers. The closure after an isolated rectangle loss uses only the surrounding eight-stage and eight-sheet margins, by the radius-eight argument above.

Two consecutive ordinary stages with their seeds intact separate the remaining white vertices across the first stage by round two. The one-sided stage ancestry fills that stage. A pair of white vertices on opposite sides at distance at most two would have to share a neighbor in the filled stage. The port lists give incoming offsets $0,1,2$ and outgoing offsets $0,9,10,12$. Only offset $0$ can serve both sides, and its outgoing neighbor has seed offset $0$ in the second intact stage. That neighbor is blue. In the sheet coordinate the four-sheet certificate gives separation across the center of four intact sheets by round five. Each statement concerns a strip of seeds intact across the entire other coordinate.

Place these intact strips between the rectangles in a grid, with cuts in ordinary stages and all seeds outside rectangles intact. Use unoccupied margins at the exceptional stages and place strips also along the seams of the cyclic tiling. Any two vertices in distinct regions of this grid at graph distance at most two would have to cross at least one of the guarded cuts in a path of length at most two. After round five no such pair is white. The final white fort therefore splits into separate forts on the regions. Each part uses lost seeds from at most one rectangle, so it lies in the final white set for those isolated losses. Conversely each isolated final white set is contained in the combined final white set by monotonicity. Thus the combined final white set is the union of the isolated ones. [One-dimensional interval argument](CYCLIC_FORT_GROWTH.md#exponential-recovery-rate-and-finite-interval-bounds)

For the upper bound, tile a region away from the exceptional stages by disjoint $a$ by $c$ rectangles. Each rectangle has the ordinary local graph within its eight-position margins. A successful full loss must succeed on every isolated rectangle by monotonicity, giving an upper bound of $H_{a,c}$ raised to the number of tiles. For fixed $a,c$ the number of tiles divided by $km$ tends to $1/(ac)$. For the lower bound, place the same rectangles with two intact ordinary stages between stage intervals and four intact sheets between sheet intervals. Keep the ordinary margins near the exceptional stages. The density of tiles tends to $1/Q$. Require all uncovered designated seeds to survive and let each rectangle have an independent successful isolated loss. This event suffices for full recovery and gives the lower bound. There are ten seed sites per stage-sheet cell in the ordinary graph and $10km$ in the cover. The difference of the two rates is at most the stated width since $(1-p)^{10ac}\le H_{a,c}\le1$. Sending both $a$ and $c$ to infinity proves the limit.

### Minimum survivor density in growing covers

Let $s_{k,m}$ be the smallest number of surviving designated seeds that force the prism cover. For an ordinary rectangle of $a$ stages by $c$ sheets, let $h_{a,c}$ be the smallest number that must survive inside it when every seed outside it survives. With $Q=(a+2)(c+4)$, the limit $\sigma_{\mathrm{prism}}=\lim_{k,m\to\infty}s_{k,m}/(km)$ exists and satisfies

$$
\frac{h_{a,c}}{ac}
\ \leq\ \sigma_{\mathrm{prism}}\ \leq\
\frac{h_{a,c}+10(Q-ac)}{Q}.
$$

A successful cover loss, isolated in any ordinary rectangle, requires at least $h_{a,c}$ survivors there. Summing over disjoint rectangles gives the lower bound. Place an optimal rectangle configuration in each of the tiles with two-stage and four-sheet buffers from the rate proof. Keeping all uncovered seeds makes the full cover recover, giving the upper bound. Since $0\le h_{a,c}\le10ac$, the two bounds differ by at most $10(1-ac/Q)$, which tends to zero. A rectangle containing the seeds of an ordinary finite fort has $h_{a,c}\geq1$, so the limiting density is positive.

Whenever all seeds in an optimal survivor set survive, recovery follows by monotonicity. That event has probability $(1-p)^{s_{k,m}}$. The total number of successful sets is at most $2^{10km}$ and each contributes at most $(1-p)^{s_{k,m}}$. Thus the two-dimensional loss rate also has the high-loss limit

$$
\lim_{p\uparrow1}\frac{\Phi(p)}{\log(1-p)}=\sigma_{\mathrm{prism}}.
$$

## Blocking losses in ordinary stages

The ordinary interior has minimum finite fort cost exactly 30. The greatest projected support inside one or two consecutive ordinary stages with ordinary neighbors on both sides is empty by the endpoint test. Three stages admit a cost-30 fort. At this cost there are ten seed sets for forts confined to three ordinary stages, up to sheet translation. Two have span ten and eight have span eleven. Their closures have 66 to 75 vertices. All 300 one-seed restorations were replayed on each of two representative covers, where completion took eight to sixteen rounds.

A fort supported in the ordinary interior cannot have two empty intervening stages at cost at most 29. Such a gap separates two nonempty forts because no vertex can have a neighbor on both sides. Each part would cost at least 24. The 31-stage band check at 33 blocks excludes any 31 consecutive ordinary stages occupied in every adjacent pair at budget 29. The permitted sources agree in every translated ordinary band, so a candidate occupies at most 30 consecutive stages. For the same reason a pair of empty interior sheets cannot occur. If the sheet span were at least 38, two disjoint bands of width 19 would require at least 30 seeds. The width-19 bound is checked at 35 blocks, which accommodates the full 30-stage window with ordinary neighbors. By translating the candidate into that window and preserving its ordinary neighborhood, it suffices to search 37 interior sheets and two guards. This search excludes every candidate at cost at most 29. The size-30 classification in three stages uses 38 interior sheets and two guards since disjoint bands of widths 19 and 20 require 31 seeds.

At budget 30 the 32-stage ordinary band forces an empty pair. As before, two nonempty parts on opposite sides of an interior gap would cost at least 24 each. Thus it suffices to place the fort in 31 ordinary stages, with ordinary neighbors. A span of 39 sheets would contain disjoint width-19 and width-20 bands costing at least 31 in the 36-block representative. The exact verifier uses 38 interior sheets and two guards and requires the first permitted stage to be occupied. It excludes the ten known losses in every stage and sheet translation. The remaining formula is unsatisfiable, so these ten patterns exhaust the ordinary interior at cost 30.

Radius-eight locality transfers each of the ten seed sets and its restoration outcomes to every suitable ordinary position. For $k\geq21$ and $m\geq28$, there are $k-20$ allowed stage starts with eight ordinary stages of margin on each side. All ten sets occupy all three stages and both extreme sheets, giving at least $10m(k-20)$ distinct minimal 30-seed losses. The complete ordinary classifications at costs through 30 give $\alpha_d=0$ for $d\leq29$ and $\alpha_{30}=10$.

The ordinary exclusions also apply to cyclic forts at smaller periods than the general eventual-count bound. In the ordinary region, an empty stage pair between nonempty parts would split a cyclic fort into two of cost at least 24 each, since the cyclic minimum at these periods is 24. The same stage-band caps therefore fit an ordinary cyclic fort of cost at most 29 into the 35-block window, where the width-19 band excludes sheet wrapping at $m\geq37$ by $15m>19\cdot29$. At cost 30 the 36-block window and the width-20 band exclude wrapping at $m\geq38$ by $16m>20\cdot30$. At 37 sheets the wrapped verifier excludes cost 30 in the same stage window. At 36 sheets width 20 excludes costs up to 28, and the complement of any single sheet splits into bands of widths 17 and 18, containing at least $13+14=27$ seeds in total. Each sheet then has at most two seeds at cost 29 and three at cost 30. The wrapped verifier with the same ordinary stage windows excludes both budgets. At 35 and 34 sheets the complement bounds are 26 and 25 respectively, obtained from widths 17 and 17 or 16 and 17. The corresponding wrapped checks exclude costs 28 through 30 at both periods, and all smaller budgets already unroll by the general 27-seed classification. At 33 sheets the smaller costs already unroll, and the wrapped test excludes cost 30 in the ordinary window. The complete ordinary classification therefore holds from 33 sheets.

### A packing of disjoint ordinary blocking losses

One of the ordinary size-30 templates spans ten sheets. Translate its seed support by the lattice
$\{(2i,3i+4j):i,j\in\mathbb{Z}\}$ in the stage and sheet coordinates. For a seed with stage offset $x$, within-stage label $v$ and sheet coordinate $y$, the residue modulo this lattice is represented by
$(x\bmod2,\ v,\ (y-3\lfloor x/2\rfloor)\bmod4)$.
The [packing verifier](check_finite_fort_span.py) checks all thirty residues are distinct. It also replays the guarded ordinary fort and its thirty one-seed restorations. Thus the translates have disjoint seed sets and their centers have density $1/8$ per stage-sheet cell.

For $k\geq21$ and $m\geq28$, use starts $9,11,\ldots$ through stage $k-12$. Within each chosen stage start, take the matching sheet phase modulo four with the template wholly within the $m$ consecutive sheet positions. This gives at least
$J=\lfloor(k-19)/2\rfloor\lfloor(m-9)/4\rfloor$ disjoint blocking losses. Their full-loss events are independent, so

$$
\Pr(\text{blocking})\geq 1-(1-p^{30})^J.
$$

Every successful seed set keeps at least one seed in each packed support. Taking the growing-cover limit in both conclusions gives

$$
\Phi(p)\leq \tfrac18\log(1-p^{30}),\qquad
\sigma_{\mathrm{prism}}\geq \tfrac18.
$$

In particular, blocking tends to one if $kmp^{30}\to\infty$ in this parameter range.

### Bounds from overlapping losses and periodic survivors

For every $0<p<1$,

$$
\frac15\leq \sigma_{\mathrm{prism}}\leq\frac{151}{128},
\qquad
\frac{151}{128}\log(1-p)\leq\Phi(p)\leq\frac15\log(1-p^{30}).
$$

For the lower survivor bound, use the ordinary 30-seed witness in the [density verifier](check_finite_fort_span.py). No within-stage seed label occurs more than five times in the witness. Take all $(k-20)m$ stage and sheet placements allowed by the ordinary locality range at $k\geq21$, $m\geq28$. For any given seed site and any occurrence of its label in the witness, at most one placement maps that occurrence to the site. Each surviving seed therefore meets at most five of the translated losses. Successful recovery requires a survivor in each translated loss. Consequently $s_{k,m}\geq\lceil(k-20)m/5\rceil$, which gives the density bound.

For the upper probability bound, let $f_i$ indicate that at least one seed survives in placement $i$. Successful recovery implies all $f_i=1$. Under independent losses, integrate their product one seed variable at a time. Each variable appears in at most five factors. Hölder's inequality over that variable bounds its integral by replacing each dependent factor $g$ with $(\mathbb E[g^5])^{1/5}$, taking expectation only in the current variable. Include constant factors equal to one if needed to use five factors. The replacement introduces no new variables, so repeating the argument gives $\mathbb E\prod_i f_i\leq\prod_i(\mathbb E f_i^5)^{1/5}$. Each expectation is $1-p^{30}$. Thus $R_{k,m}(p)\leq(1-p^{30})^{(k-20)m/5}$ and the logarithmic limit gives the upper rate bound.

The upper survivor bound uses a sheet period of 128 and the same phase pattern in every ordinary stage. The verifier lists 151 survivor phases as bit masks indexed by within-stage seed label. It evolves the 16 vertex labels in every sheet phase by the parallel rule. Ordinary stage translations preserve the phase pattern, and every actual neighbor occurrence enters the test for a unique white neighbor. The process colors the whole periodic ordinary graph in $T=668$ rounds.

To place this construction in a growing signed cover, take $m$ to be a multiple of 128. Keep all seeds in stages within stage distance $2T+1$ of either exceptional stage. Use the periodic survivors in every other stage. A vertex within stage distance $2T$ of the exceptional stages has its own and next stages intact, so the two-round ancestry certificate applies. Every other vertex has an ordinary radius-$2T$ neighborhood, where the initial colors contain the periodic survivor profile. Its ordinary round-$T$ forcing proof therefore applies by monotonicity. The intact stage margins cost $O(Tm)$ seeds, so along these covers the survivor density of the construction tends to $151/128$. The established two-dimensional limit gives the upper survivor bound. Requiring all its seeds to survive gives probability at least $(1-p)$ to the power of its survivor count, yielding the lower rate bound after normalization.

## Failure from the ends and the interior

Let $d_*=\min\{d:\alpha_d>0\}$ and $\alpha=\alpha_{d_*}$, using the coefficients of the eventual minimal-loss count. The ordinary interior classification gives $d_*=30$ and $\alpha=\alpha_{30}=10$. For all $k\geq4$, $m\geq33$ and $0\leq p\leq1$ there is a uniform approximation

$$
\Pr(\text{blocking})=
1-\exp\bigl(-5mp^{24}-\alpha kmp^{d_*}\bigr)
+O\bigl(mp^{25}+kmp^{d_*+1}\bigr).
$$

In particular, if $p\to0$, $mp^{24}\to\lambda<\infty$ and $kmp^{d_*}\to\mu<\infty$, the blocking probability tends to $1-\exp(-5\lambda-\alpha\mu)$ in this region. The coefficient of the first interior order enters the limit along with the five minimum patterns per sheet.

For the proof, count the minimal losses through size 30. The size-24 patterns give exactly $5m$ events. Every minimal loss of size 25 through 29 is anchored within six stages of an exceptional stage, so their combined contribution is $O(mp^{25})$. For size 30, the ten ordinary patterns give $10km+O(m)$ placements, with distinct translates and at least $10m(k-20)$ when $k\geq21$. The remaining patterns must be anchored and are counted by bounded-length walks, so they number $O(m)$. Thus the expected event count is $5mp^{24}+10kmp^{30}+O(mp^{25})$. Higher-order events contribute at most $O(kmp^{31})$ by the connected loss bound.

Give each of the selected events a dependence neighborhood consisting of itself and the events sharing one of its seed sites. This neighborhood has bounded size. Indeed, connected sets of size at most $d_*$ containing a fixed seed can be counted by their spanning walks rooted at that seed in the bounded-degree auxiliary graph. The event is independent of the coins used by all events outside the neighborhood, so $b_3=0$ in the zero-event bound. Since there are $O(km)$ events, each of probability at most $p^{24}$, the term $b_1$ is $O(kmp^{48})$.

Among the ordered pairs in $b_2$, there are $O(m)$ with at least one member smaller than $d_*$. The two distinct losses require at least 25 distinct deletions, so their contribution is $O(mp^{25})$. The remaining $O(km)$ ordered pairs each require at least $d_*+1$ distinct deletions, giving $O(kmp^{d_*+1})$. These bounds control the Poisson approximation error, and replacing its mean by $5mp^{24}+\alpha kmp^{d_*}$ changes the approximation by at most $O(mp^{25})$. Adding the probability of blocking through a larger loss proves the formula. [Arratia, Goldstein and Gordon, Theorem 1](https://doi.org/10.1214/aop/1176991491)

### Refined two-intensity approximation through order 29

Put $B(p)=A_k(p)+138p^{27}+342p^{28}+397p^{29}$ for $k\geq5$, so $B$ is the same at all these lengths. The complete catalogue through size 29 gives, for $k\geq5$, $m\geq33$ and $0\leq p\leq1$,

$$
\Pr(\text{blocking})=1-\exp(-mB(p))+O(kmp^{30}).
$$

For all $k\geq5$, $m\geq33$ and $0\leq p\leq1$, the ordinary classification further gives

$$
\Pr(\text{blocking})=
1-\exp\!\left(-mB(p)-10kmp^{30}\right)
+O\!\left(mp^{30}+kmp^{31}\right).
$$

Select the complete catalogue through size 29 and the ordinary size-30 placements. The omitted size-30 losses lie near an exceptional stage and together contribute $O(mp^{30})$. Larger losses contribute $O(kmp^{31})$. Mark the selected events as in the uniform exponential argument. Their neighborhoods have bounded size and the marked variables give an error $O(kmp^{48})$. The mean of the marked count agrees with the selected union probability through degree 30 because simultaneous marks have disjoint seed sets. The terms through degree 29 give $mB(p)$. At degree 30 each ordinary placement contributes its own monomial, since its union with any distinct minimal loss has degree at least 31. Their contribution is $10kmp^{30}+O(mp^{30})$. The size-30 overlap correction from the other selected events is $O(mp^{30})$, and the remaining Taylor tail of the marked mean is $O(kmp^{31})$ by bounded dependence. These bounds give the claimed error.

For $k\geq13$ and $m\geq41$, the exact boundary coefficient further gives

$$
\Pr(\text{blocking})
=1-\exp\!\left(-mB(p)-m(10k+2064)p^{30}\right)+O(kmp^{31}).
$$

The Taylor coefficients of $\log R_{k,m}$ through degree 30 are the negatives of the blocking coefficients because blocking starts in degree 24. The uniform analytic bound on $\log R_{k,m}$ gives a remainder of $O(kmp^{31})$ by Cauchy's estimate on $0\leq p\leq\rho/2$. Both exponents are nonpositive there, so exponentiation preserves the error bound. For $p\geq\rho/2$ the difference of the two probabilities is at most one, which gives the same bound with a larger constant.

### Joint counts and locations of blocking components

On the auxiliary graph of seed sites defined above, call a connected component of the deleted seeds blocking when deleting that component alone prevents recovery. For $k\geq4$ and $m\geq33$, use the five size-24 templates, with $m$ placements each, and the ten ordinary size-30 templates, with $m(k-20)_+$ placements each, where $x_+=\max(x,0)$. The ordinary placements use three consecutive stages with eight ordinary stages of margin on both sides.

The process of blocking components is within $O(mp^{25}+kmp^{31})$ in total variation of independent Poisson variables on these placements, with mean $p^{24}$ at each size-24 placement and $p^{30}$ at each chosen ordinary placement. The comparison process assigns zero mass to every other component. In particular the two counts are approximated jointly by independent Poisson variables of means $5mp^{24}$ and $10m(k-20)_+p^{30}$. Keeping the fifteen template labels gives a product of fifteen Poisson laws as the approximation to the vector of type counts.

To prove the bound, first count occurrences of the chosen minimal losses, whether or not they are full components. Use dependence neighborhoods consisting of placements that share a seed, including the placement itself. As in the preceding proof, the neighborhoods have bounded size, disjoint seed coins give $b_3=0$, and $b_1=O(kmp^{48})$. Distinct overlapping size-24 losses use at least 25 seeds in their union. Every other overlapping pair uses at least 31 seeds because both sets are inclusion-minimal and one has size 30. Thus $b_2=O(mp^{25}+kmp^{31})$. The process form of the Chen–Stein inequality gives the stated error for the full vector of placement indicators. [Arratia, Goldstein and Gordon, Theorem 2](https://doi.org/10.1214/aop/1176991491)

Every chosen pattern is connected in the auxiliary graph. If it occurs and is part of a larger component, at least one seed outside it and adjacent to it in the auxiliary graph must also be lost. There are at most $30D$ choices for such a seed per pattern. A union bound over the placements gives probability $O(mp^{25}+kmp^{31})$ for this to happen anywhere. The probability of seeing any other inclusion-minimal blocking loss is of this same order, by the exceptional-stage count through size 30 and the connected loss bound at size 31. Every blocking component contains an inclusion-minimal blocking loss. Outside these two exceptional events, the blocking components are therefore exactly the chosen patterns that occurred. Coupling the two processes on the original seed coins proves the claimed total variation bound.

Suppose also $k,m\to\infty$ in the joint rare-loss limit. Record each chosen component's initial sheet as $j/m$ on the unit circle, using the first occupied sheet after the unique largest gap, and for ordinary components also record its first stage as $i/k$. For each of the five size-24 templates the rescaled points converge to a homogeneous Poisson process of intensity $\lambda$ on the circle. For each of the ten ordinary templates they converge to a homogeneous Poisson process of intensity $\mu$ on the unit torus. All fifteen limiting processes are independent. In the approximating processes, the intensity measures are uniform grids with weights $p^{24}$ or $p^{30}$. The grids converge by Riemann sums, since the omitted $O(1)$ ordinary stage starts have total intensity $O(mp^{30})$. The Poisson Laplace functionals then converge, and the total variation error tends to zero.

### Uniform losses of a prescribed size

Let $N=10km$ be the number of seed sites. Write the independent-loss blocking probability as $\sum_d c_d p^d$. If the loss set is chosen uniformly among $\ell$-element subsets of the seeds, then

$$
\Pr(\text{blocking at size }\ell)=\sum_{d=0}^{\ell}c_d\,\frac{(\ell)_d}{(N)_d},
\qquad (a)_d=a(a-1)\cdots(a-d+1).
$$

To see this, write the blocking indicator as a multilinear polynomial in the Boolean loss indicators. Its monomial on a site set of size $d$ has expectation $p^d$ under independent losses and $(\ell)_d/(N)_d$ under a uniform loss of size $\ell$. The coefficient $c_d$ sums the monomial coefficients of degree $d$. Thus the cyclic coefficients above give exact probabilities through loss size 27 for $m\geq30$, and at every length of at least five blocks through size 28 for $m\geq30$ and size 29 for $m\geq33$. For $k\geq13$, $m\geq41$ the formula is exact through size 30. The smaller verified cyclic ranges also apply. The number of blocking $\ell$-sets is $\sum_{d=0}^{\ell}c_d\binom{N-d}{\ell-d}$.

The joint component law also extends to a uniform loss of size $\ell$. Set $p=\ell/N$ and let $\Lambda=mp^{24}+kmp^{30}$. For $k\geq4$, $m\geq33$ and $\ell\geq1$, the total variation error is

$$
O\left(mp^{25}+kmp^{31}+\frac{\Lambda}{\sqrt{\ell}}\right).
$$

The independent Poisson comparison now uses means $(\ell)_{24}/(N)_{24}$ and $(\ell)_{30}/(N)_{30}$ per placement. The formula includes zero means when the budget is below the corresponding template size.

For the coupling, draw a uniform permutation of the $N$ seed sites and an independent $B\sim\operatorname{Bin}(N,p)$. Take the first $\ell$ sites for the fixed-size loss and the first $B$ for the independent loss. For a specified $d$-site pattern, the probability of a mismatch of its occurrence indicators, conditional on $B$, is

$$
\frac{\left|\binom{B}{d}-\binom{\ell}{d}\right|}{\binom Nd}
\leq \frac{d\,|B-\ell|\,\max(B,\ell)^{d-1}}{(N)_d}.
$$

Here the inequality follows by summing consecutive binomial differences. Since $\mathbb E(B-\ell)^2\leq\ell$ and $\mathbb E\max(B,\ell)^{2d-2}=O_d(\ell^{2d-2})$, Cauchy–Schwarz gives mismatch probability $O_d(p^d/\sqrt{\ell})$. The moment bound follows by expanding powers of $B$ in falling factorials and using $\mathbb E(B)_j=(N)_j p^j\leq\ell^j$. Summing over the two template families gives $O(\Lambda/\sqrt{\ell})$.

In the fixed-size model any $e$ specified seeds are lost with probability at most $p^e$. The bounds for a chosen template acquiring an adjacent extra loss and for any uncatalogued minimal loss therefore apply unchanged. Finally, for $d\in\{24,30\}$ the difference between $p^d$ and $(\ell)_d/(N)_d$ is $O_d(p^d/\ell)$. For $\ell\geq d$ this follows by bounding the ratio of the means below by $\prod_{j=0}^{d-1}(1-j/\ell)\geq1-d(d-1)/(2\ell)$. The bound also holds for $\ell<d$. Adding independent Poisson variables for the differences of the means changes the comparison process with probability $O(\Lambda/\ell)$.

Consequently under $p\to0$, $mp^{24}\to\lambda$ and $kmp^{30}\to\mu$ with finite limits, the joint count limits agree for both loss models. If $\ell$ stays bounded along a subsequence, both limiting intensities on that subsequence are zero. When both cover dimensions grow, the marked spatial limits also agree.

## Complete classification of minimum-cost finite forts

At four through 17 blocks and at 26 blocks, the width-16 and width-17 band checks give a span bound for every cost-24 fort. Any pair of empty interior sheets would split it into two nonempty finite forts, each of cost at least 24. A span of at least 33 would contain disjoint bands of widths 16 and 17. They would require at least 12 and 13 lost seeds respectively. A cost-24 fort thus fits inside the 32 interior sheets of a 34-sheet guarded strip.

The longer-span verifier translates the first occupied sheet to one and demands an occupied sheet at index ten or higher. It keeps the fort clauses, the guards, the absence of an interior two-sheet gap and the seed ancestry conditions. It permits arbitrary forts including those with proper fort subsets. At 26 blocks it also uses the [projection bounds](BLOCK_STABILIZATION.md#finite-forts-and-repeated-projected-seeds) from the nine- and ten-sheet covers. Those covers have minimum costs 18 and 20, so at budget 24 the respective numbers of duplicate seeds under projection are at most six and four.

The direct cost-24 tests exclude spans of ten or more. For 18 through 25 blocks, the [projected-support verifier](check_prism_projected_support.py) checks budget 24 with both endpoint systems. It excludes a projected support that contains an opening seed and meets every consecutive pair of appended stages. A finite fort at these lengths therefore permits either opening insertion or insertion between an empty stage pair. Both leave every occupied sheet and the cost unchanged. Iterating to 26 blocks gives the same span bound. For every $k\geq27$ the 26-stage band gives a pair of consecutive empty stages. Its contraction again preserves the occupied sheets and cost, so iterating down to 26 blocks gives the bound there as well.

For every $k\geq4$, the 54 shapes and five seed sets above are therefore the complete lists of minimum-cost finite forts and minimum seed blocking sets up to sheet translation.

## Exact cyclic counts

For $m\geq29$, the width-24 band rules out wrapped forts of cost 24 at four through 24 blocks and at 26 blocks by $20m>24\cdot24$. At 25 through 28 sheets, the wrapped verifier handles four through 23 blocks and 26 blocks using the bands through width 28. The width-$(m-1)$ band forces every sheet to contain at most $29-m$ seeds.

The 26-stage contraction preserves the occupied sheets in a cyclic cover, so the absence of wrapping at 26 blocks extends to every greater length. At 25 blocks the base check at budget 24 already excludes a fort containing an opening seed and meeting every consecutive pair of appended stages. This version of the check uses the ordinary fort clauses on the base graph. Hence a cyclic fort at 25 blocks allows one of the two insertions that leave the occupied sheets unchanged, giving the same exclusion as at 26 blocks.

At 24 blocks, a wrapped fort at 22 through 28 sheets would have to contain an opening seed and meet every consecutive pair of appended stages. Otherwise either insertion would give a wrapped fort at 25 blocks. The base budget-23 check at 24 blocks then forces at least 24 distinct projected seed labels. The lifted cost is 24, so each label has one selected copy. The insertion-obstruction verifier imposes these conditions. At 22 through 25 sheets the width-$(m-1)$ band caps each sheet at $29-m$ seeds. At 26 through 28 sheets it partitions the complement of one sheet into two bands whose lengths differ by at most one and are both at least ten. The two bands require at least $m-9$ seeds, leaving a cap of $33-m$ on the omitted sheet. All seven formulas are unsatisfiable.

Once unwrapping holds, every minimum-cost cyclic fort is the projection of one of the listed finite forts. Its span is at most nine, so the outer run of at least $m-9$ empty sheets is strictly longer than any interior run at the periods here. The first occupied sheet after this unique longest run determines the translation. The same argument applies to the seed sets, as each meets both extreme sheets of its fort. The exact numbers are $54m$ minimum-cost cyclic forts and $5m$ minimum blocking sets. Their cyclic fort-size polynomial is $mP(x)$. For a minimum blocking set the final white fort contains all its lost seeds, since any smaller seed intersection would contradict minimal cost.

At 24 sheets the direct verifier excludes wrapped forts of cost 24 at four through 23 blocks and at 26 blocks. The cap is five seeds per sheet. At 23 sheets the width-22 band gives a cap of six, and the direct verifier excludes cost 24 at all lengths from four through 23 blocks and at 26 blocks. Contraction and insertion give the same exclusion at 23 and 24 sheets for every chain of at least 24 blocks. Thus the exact counts and polynomial hold at 23 sheets and every longer period for all chain lengths of at least four blocks. At 22 sheets the width-21 band gives a cap of seven, and the direct verifier excludes wrapping at cost 24 at four through thirteen blocks and at 26 blocks. The contraction and insertion proofs extend the 26-block result to every length of at least 24 blocks. In these ranges there are 1,188 minimum-cost forts and 110 minimum blocking sets at 22 sheets.

The chain has $10k$ seed labels. Among uniform 24-element losses from the $10km$ lifted seeds, the exact probability of blocking recovery is $5m/\binom{10km}{24}$. For independent losses with probability $p$ per seed, the blocking probability at fixed $k,m$ is $5m p^{24}+O(p^{25})$ as $p\to0$.

## Reproduction

```sh
python -B research-twins/check_finite_fort_projection.py
```

The verifier tests all 61,440 nonempty supports in the weighted four-vertex cases with shifts in $\{-1,0,1\}$. It checks all intervals it constructs and independently brute-forces the endpoint inequalities on supports of size at most two. For each graph it compares the greatest support with the union of all accepted supports. It checks that the shifted four-cycle has no finite fort, and realizes the projection of the published prism fort.

The optional PySAT verifier checks the binary comparisons and replays the thirteen shorter-chain exclusions.

```sh
python -B research-twins/check_prism_projected_support.py
```

The width-16 band and guarded-strip checks cover the remaining finite lengths.

```sh
python -B research-twins/check_block_stabilization.py --subbands-from 13 --band-through 16 --band-blocks 4 5 6 7 8 9 10
for blocks in 5 6 7 8 9 10
do
    python -B research-twins/check_finite_fort_strip.py --sheets 33 --blocks "$blocks" || exit 1
done
```

The sheet-band checks for the shorter chains can be replayed with the same verifier as at 26 blocks. The 24-sheet guarantee uses the following runs.

```sh
python -B research-twins/check_block_stabilization.py --subbands-from 13 --band-through 28 --band-blocks 4 5 6 7 8 9 10
python -B research-twins/check_block_stabilization.py --subbands-from 17 --band-through 28 --band-blocks 11 12 13 14 15 16 17 18 19 20 21 22 23
for blocks in 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23
do
    python -B research-twins/check_short_prism_covers.py --wrapped "$blocks" 25 22 28 --wrapped "$blocks" 25 23 28 --wrapped "$blocks" 26 23 28 || exit 1
    python -B research-twins/check_short_prism_covers.py --wrapped "$blocks" 24 21 28 --wrapped "$blocks" 24 22 28 --wrapped "$blocks" 24 23 28 || exit 1
done
for blocks in 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23
do
    python -B research-twins/check_short_prism_covers.py --wrapped "$blocks" 23 20 28 --wrapped "$blocks" 23 21 28 --wrapped "$blocks" 23 22 28 --wrapped "$blocks" 23 23 28 || exit 1
done
for blocks in 4 5
do
    python -B research-twins/check_short_prism_covers.py --wrapped "$blocks" 21 18 --wrapped "$blocks" 21 19 --wrapped "$blocks" 21 20 --wrapped "$blocks" 21 21 --wrapped "$blocks" 21 22 --wrapped "$blocks" 21 23 || exit 1
done
for blocks in 4 5 6 7 8 9 10 11 12 13 26
do
    python -B research-twins/check_short_prism_covers.py --wrapped "$blocks" 22 19 28 --wrapped "$blocks" 22 20 28 --wrapped "$blocks" 22 21 28 --wrapped "$blocks" 22 22 28 --wrapped "$blocks" 22 23 28 || exit 1
done
```

The two- and three-block results use their own band checks and wrapped verifier.

```sh
python -B research-twins/check_block_stabilization.py --subbands-from 13 --band-through 25 --band-blocks 2 3
python -B research-twins/check_short_prism_covers.py
```

The following command reproduces the minimum spans, the cost table and the classifications of the seven-, eight- and nine-sheet minimum-cost forts and their seed families.

```sh
python -B research-twins/check_finite_fort_span.py
```

The restoration-time table and the inclusion-minimal 25-seed loss are checked with the same verifier.

```sh
python -B research-twins/check_finite_fort_span.py --restoration-times
python -B research-twins/check_finite_fort_span.py --ordinary-stage-blocker
python -B research-twins/check_finite_fort_span.py --ordinary-packing
python -B research-twins/check_finite_fort_span.py --ordinary-density
python -B research-twins/check_cost_25_blocking_sets.py --ordinary-size-30-exact
python -B research-twins/check_cost_25_blocking_sets.py --ordinary-threshold
python -B research-twins/check_short_prism_covers.py --ordinary-wrapped 37 30 --ordinary-wrapped 36 29 --ordinary-wrapped 36 30
python -B research-twins/check_short_prism_covers.py --ordinary-wrapped 35 28 --ordinary-wrapped 35 29 --ordinary-wrapped 35 30
python -B research-twins/check_short_prism_covers.py --ordinary-wrapped 34 28 --ordinary-wrapped 34 29 --ordinary-wrapped 34 30
python -B research-twins/check_short_prism_covers.py --ordinary-wrapped 33 30
```

The size-25 checks enumerate four through fourteen blocks and verify the transposed catalogue through 20 blocks. The stage-pair test gives completeness for all larger lengths. The size-26 checks use the same direct range and locality representative, with a separate stage-pair test.

```sh
python -B research-twins/check_cost_25_blocking_sets.py
python -B research-twins/check_prism_projected_support.py --cost-25-stage-pairs
python -B research-twins/check_prism_projected_support.py --cost-26-stage-pairs
python -B research-twins/check_prism_projected_support.py --cost-27-stage-pairs
python -B research-twins/check_prism_projected_support.py --cost-28-stage-pairs
python -B research-twins/check_prism_projected_support.py --cost-29-stage-pairs
python -B research-twins/check_prism_projected_support.py --cost-30-stage-pairs
python -B research-twins/check_block_stabilization.py --subbands-from 13 --band-through 20 --band-blocks 13
python -B research-twins/check_block_stabilization.py --subbands-from 13 --band-through 15 --band-blocks 27 28 29 30 31 32
python -B research-twins/check_short_prism_covers.py --four-sheet-barrier
python -B research-twins/check_short_prism_covers.py --stage-ancestry
python -B research-twins/check_short_prism_covers.py --rectangle-separation
python -B research-twins/check_cost_25_blocking_sets.py --five-block-catalogue witnesses
python -B research-twins/check_cost_25_blocking_sets.py --five-block-catalogue exhaustive
python -B research-twins/check_cost_25_blocking_sets.py --size-30-five-blocks
python -B research-twins/check_cost_25_blocking_sets.py --boundary-catalogue witnesses
python -B research-twins/check_cost_25_blocking_sets.py --boundary-catalogue exhaustive
python -B research-twins/check_cost_25_blocking_sets.py --size-30-boundary
python -B research-twins/check_block_stabilization.py --subbands-from 13 --band-through 25 --band-blocks 25 27 28 29
python -B research-twins/check_block_stabilization.py --subbands-from 13 --band-through 26 --band-blocks 25 29
python -B research-twins/check_block_stabilization.py --subbands-from 13 --band-through 25 --band-blocks 30
python -B research-twins/check_block_stabilization.py --subbands-from 13 --band-through 25 --band-blocks 31
python -B research-twins/check_block_stabilization.py --subbands-from 13 --band-through 34 --band-blocks 26
for blocks in 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24
do
    python -B research-twins/check_short_prism_covers.py --wrapped "$blocks" 33 29 28 || exit 1
done
python -B research-twins/check_short_prism_covers.py --wrapped 25 33 29 26 --wrapped 27 33 29 25 --wrapped 28 33 29 25 --wrapped 29 33 29 26 --wrapped 30 33 29 25
for sheets in 28 29 30 31 32 33 34 35
do
    python -B research-twins/check_short_prism_covers.py --wrapped 5 "$sheets" 30 28 || exit 1
done
for blocks in 25 29
do
    python -B research-twins/check_short_prism_covers.py --wrapped "$blocks" 30 26 26 --wrapped "$blocks" 30 27 26 || exit 1
done
for blocks in 27 28
do
    python -B research-twins/check_short_prism_covers.py --wrapped "$blocks" 30 26 25 --wrapped "$blocks" 30 27 25 || exit 1
done
for blocks in 25 27 28 29
do
    python -B research-twins/check_short_prism_covers.py --wrapped "$blocks" 31 27 25 --wrapped "$blocks" 32 27 25 || exit 1
done
for blocks in 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 26
do
    python -B research-twins/check_short_prism_covers.py --wrapped "$blocks" 30 26 28 --wrapped "$blocks" 30 27 28 --wrapped "$blocks" 31 27 28 || exit 1
done
for blocks in 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20
do
    python -B research-twins/check_cost_25_blocking_sets.py --size-26 "$blocks" || exit 1
done
for blocks in 4 5 6 7 8 9 10 11 12 13
do
    python -B research-twins/check_cost_25_blocking_sets.py --size-27 "$blocks" || exit 1
done
for blocks in 14 15 16 17 18 19 20
do
    python -B research-twins/check_cost_25_blocking_sets.py --size-27 "$blocks" || exit 1
done
for blocks in 4 5 6 7 8 9 10
do
    for sheets in 28 29 30
    do
        python -B research-twins/check_short_prism_covers.py --wrapped "$blocks" "$sheets" 26 28 --wrapped "$blocks" "$sheets" 27 28 || exit 1
    done
done
for blocks in 5 6 7 8
do
    python -B research-twins/check_short_prism_covers.py --wrapped "$blocks" 27 26 28 --wrapped "$blocks" 27 27 28 --wrapped "$blocks" 26 26 28 || exit 1
done
python -B research-twins/check_short_prism_covers.py --wrapped 5 25 26 28 --wrapped 5 25 27 28 --wrapped 6 25 26 28 --wrapped 5 26 27 28 --wrapped 6 26 27 28 --wrapped 7 26 27 28 --wrapped 9 27 26 28 --wrapped 4 25 26 28 --wrapped 4 25 27 28 --wrapped 4 26 26 28 --wrapped 4 26 27 28 --wrapped 4 27 26 28 --wrapped 4 27 27 28 --wrapped 11 28 26 28 --wrapped 11 29 26 28 --wrapped 11 29 27 28 --wrapped 11 30 26 28 --wrapped 11 30 27 28
python -B research-twins/check_short_prism_covers.py --wrapped 12 29 26 28 --wrapped 12 29 27 28 --wrapped 12 30 26 28 --wrapped 12 30 27 28 --wrapped 13 30 26 28 --wrapped 13 30 27 28
for blocks in 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21
do
    python -B research-twins/check_cost_25_blocking_sets.py --size-28 "$blocks" || exit 1
done
for blocks in 5 6 7 8 9 10 11 12
do
    python -B research-twins/check_cost_25_blocking_sets.py --size-29 "$blocks" || exit 1
done
for sheets in 28 29 30 31 32 33
do
    python -B research-twins/check_short_prism_covers.py --wrapped 5 "$sheets" 29 28 --wrapped 6 "$sheets" 29 28 --wrapped 7 "$sheets" 29 28 --wrapped 8 "$sheets" 29 28 || exit 1
done
python -B research-twins/check_short_prism_covers.py --wrapped-with-occupied-pairs 31 35 29 23
python -B research-twins/check_short_prism_covers.py --wrapped 25 34 29 26 --wrapped 27 34 29 25 --wrapped 28 34 29 25 --wrapped 29 34 29 26 --wrapped 30 34 29 25
python -B research-twins/check_short_prism_covers.py --wrapped-with-occupied-pairs 31 34 29 24
python -B research-twins/check_short_prism_covers.py --wrapped-with-occupied-pairs 31 34 29 25
python -B research-twins/check_short_prism_covers.py --wrapped-with-occupied-pairs 31 33 29 25
for blocks in 5 6 7 8 9 10
do
    for sheets in 28 29 30 31 32
    do
        python -B research-twins/check_short_prism_covers.py --wrapped "$blocks" "$sheets" 28 28 || exit 1
    done
done
for blocks in 11 12 13 14 15 16 17 18 19 20 21 22 23 24 26
do
    python -B research-twins/check_short_prism_covers.py --wrapped "$blocks" 30 28 28 || exit 1
done
for blocks in 25 29
do
    python -B research-twins/check_short_prism_covers.py --wrapped "$blocks" 30 28 26 || exit 1
done
for blocks in 27 28 30
do
    python -B research-twins/check_short_prism_covers.py --wrapped "$blocks" 30 28 25 || exit 1
done
for blocks in 25 29
do
    python -B research-twins/check_short_prism_covers.py --wrapped "$blocks" 31 28 26 --wrapped "$blocks" 32 28 26 --wrapped "$blocks" 33 28 26 || exit 1
done
python -B research-twins/check_short_prism_covers.py --wrapped 27 31 28 25 --wrapped 28 31 28 25
python -B research-twins/check_short_prism_covers.py --wrapped-with-occupied-pairs 30 31 28 25
for blocks in 27 28 30
do
    python -B research-twins/check_short_prism_covers.py --wrapped "$blocks" 32 28 25 --wrapped "$blocks" 33 28 25 || exit 1
done
for blocks in 11 12 13 14 15 16 17 18 19 20 21 22 23 24 26
do
    python -B research-twins/check_short_prism_covers.py --wrapped "$blocks" 31 28 28 --wrapped "$blocks" 32 28 28 || exit 1
done
for blocks in 4 5 6 7 8 9 10 11 12 13 14
do
    python -B research-twins/check_short_prism_covers.py --wrapped "$blocks" 25 25 28 --wrapped "$blocks" 26 25 28 --wrapped "$blocks" 27 25 28 --wrapped "$blocks" 28 25 28 --wrapped "$blocks" 29 25 28 || exit 1
done
```

The complete counts use the band checks above and these additional checks. At 26 blocks the long-chain verification supplies the bands through width 25 and the nine- and ten-sheet costs.

```sh
python -B research-twins/check_block_stabilization.py --band-through 28 --band-blocks 26 --certify-sheets 9 10
python -B research-twins/check_block_stabilization.py --subbands-from 13 --band-through 28 --band-blocks 24
python -B research-twins/check_finite_fort_span.py --longer 4 5 6 7 8 9 10 11 12 13 14 15 16 17 26
python -B research-twins/check_prism_projected_support.py --minimum-forts
python -B research-twins/check_prism_opening_insertion.py
for blocks in 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 26
do
    python -B research-twins/check_short_prism_covers.py --wrapped "$blocks" 25 24 28 --wrapped "$blocks" 26 24 28 --wrapped "$blocks" 27 24 28 --wrapped "$blocks" 28 24 28 || exit 1
done
python -B research-twins/check_short_prism_covers.py --insertion-obstruction 22 23 24 25 26 27 28
for blocks in 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 26
do
    python -B research-twins/check_short_prism_covers.py --wrapped "$blocks" 24 24 28 || exit 1
done
for blocks in 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 26
do
    python -B research-twins/check_short_prism_covers.py --wrapped "$blocks" 23 24 28 || exit 1
done
for blocks in 4 5 6 7 8 9 10 11 12 13 26
do
    python -B research-twins/check_short_prism_covers.py --wrapped "$blocks" 22 24 28 || exit 1
done
```
