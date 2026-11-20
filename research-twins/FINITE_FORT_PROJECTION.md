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

For the [signed unpadded prism chain](BLOCK_STABILIZATION.md), the finite blocking numbers at two and three blocks are 16 and 21. Every chain with at least four blocks has finite blocking number 24. The cyclic blocking numbers equal their finite values from eight sheets at two blocks, 22 sheets at three blocks, and 24 sheets at every length of at least four blocks.

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

At 23 sheets and four or five blocks, the width-24 band requires at least 20 seeds. Below budget 20, every sheet would again need a seed. At budgets from 20 through 23, the width-22 band caps the omitted sheet at two through five seeds. The wrapped verifier excludes all four budgets at both lengths, giving $\kappa_{4,23}=\kappa_{5,23}=24$.

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

## All inclusion-minimal 25-seed losses at four through ten blocks

At four blocks there are exactly 22 inclusion-minimal blockers of size 25 up to sheet translation. At five through ten blocks there are exactly 20 at each length. The span of a seed set is the number of sheets from its first occupied sheet to its last, inclusive.

| Blocks | Span 7 | Span 8 | Span 9 | Span 10 | Span 11 | Total |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 4 | 1 | 7 | 8 | 4 | 2 | 22 |
| 5–10 | 1 | 7 | 8 | 4 | 0 | 20 |

Any fort of cost at most 25 has no internal pair of empty sheets, since such a gap would split it into two forts of cost at least 24 each. A span of at least 34 would contain two disjoint 17-sheet bands, requiring at least 26 seeds. There are therefore at most 33 interior sheets, with one empty guard at each end. The [enumerator](check_cost_25_blocking_sets.py) searches the resulting 35-sheet strip and excludes every translate of each of the five minimum seed sets. A remaining fort has cost 25, and its seed set is inclusion-minimal because each proper blocking subset would have to be one of the excluded 24-seed sets. Conversely, any inclusion-minimal 25-seed loss contains the seed intersection of a fort, which must equal the loss. After finding one seed set, the enumerator excludes all its translates in the strip. Unsatisfiability after the last exclusion proves the count. The output gives the seed coordinates with the first occupied sheet normalized to one.

The enumeration at five blocks supplies four patterns supported in the last two stages and 16 in opening coordinates. At six through ten blocks the verifier moves the four terminal patterns to the last two stages, checks all 20 patterns by forcing closure with empty sheet guards, and excludes any additional set in the 35-sheet formula.

At $m\geq30$, the 28-sheet band gives $24m>28\cdot25$, ruling out all wrapped forts of cost at most 25. At 28 and 29 sheets, the width-$(m-1)$ band caps each sheet at two and one seeds, respectively, when the total is 25. The wrapped verifier excludes both cases, and the minimum-budget classification handles costs through 24. For $m\geq28$, every inclusion-minimal 25-seed loss then lifts to one of the listed finite patterns. Each listed finite loss also projects to an inclusion-minimal loss. It occupies at most 11 sheets, and any contained cost-24 pattern has span at most nine, so it can be lifted into the same interval. The cyclic count is $22m$ at four blocks and $20m$ at five through ten blocks.

## The first two terms of the independent-loss probability

For each length from four through ten blocks, the enumerator also checks the unions of pairs of distinct translated 24-seed patterns. Exactly two unions of size 25 occur up to sheet translation, each containing two minimum patterns. Only relative shifts of magnitude at most eight can give such a union, since the two patterns must share a seed and each spans at most nine sheets. For $m\geq28$, these unions and their overlaps have the same counts per translation in the cyclic cover. In particular, each union of overlapping patterns occupies an interval of at most 17 sheets. Its outer gap is longer than every interior gap and determines the lift.

Write $n=10km$ for the number of lifted seeds, with $q_4=22$ and $q_k=20$ for $5\leq k\leq10$. The number of 25-element losses that block recovery is

$$
5m(n-24)+(q_k-2)m.
$$

The first summand counts single extensions of the minimum losses. The overlap subtraction removes the $2m$ double counts, and the $q_km$ inclusion-minimal losses contribute separately. For independent seed losses with probability $p$, the first two nonzero terms at fixed $k,m$ are consequently

$$
\Pr(\text{blocking})=5m p^{24}+(q_k-2)m p^{25}+O(p^{26})
\qquad (4\leq k\leq10,\ m\geq28).
$$

## Complete classification of minimum-cost finite forts

At four through 17 blocks and at 26 blocks, the width-16 and width-17 band checks give a span bound for every cost-24 fort. Any pair of empty interior sheets would split it into two nonempty finite forts, each of cost at least 24. A span of at least 33 would contain disjoint bands of widths 16 and 17. They would require at least 12 and 13 lost seeds respectively. A cost-24 fort thus fits inside the 32 interior sheets of a 34-sheet guarded strip.

The longer-span verifier translates the first occupied sheet to one and demands an occupied sheet at index ten or higher. It keeps the fort clauses, the guards, the absence of an interior two-sheet gap and the seed ancestry conditions. It permits arbitrary forts including those with proper fort subsets. At 26 blocks it also uses the [projection bounds](BLOCK_STABILIZATION.md#finite-forts-and-repeated-projected-seeds) from the nine- and ten-sheet covers. Those covers have minimum costs 18 and 20, so at budget 24 the respective numbers of duplicate seeds under projection are at most six and four.

The direct cost-24 tests exclude spans of ten or more. For 18 through 25 blocks, the [projected-support verifier](check_prism_projected_support.py) checks budget 24 with both endpoint systems. It excludes a projected support that contains an opening seed and meets every consecutive pair of appended stages. A finite fort at these lengths therefore permits either opening insertion or insertion between an empty stage pair. Both leave every occupied sheet and the cost unchanged. Iterating to 26 blocks gives the same span bound. For every $k\geq27$ the 26-stage band gives a pair of consecutive empty stages. Its contraction again preserves the occupied sheets and cost, so iterating down to 26 blocks gives the bound there as well.

For every $k\geq4$, the 54 shapes and five seed sets above are therefore the complete lists of minimum-cost finite forts and minimum seed blocking sets up to sheet translation.

## Exact cyclic counts

For $m\geq29$, the width-24 band rules out wrapped forts of cost 24 at four through 24 blocks and at 26 blocks by $20m>24\cdot24$. At 25 through 28 sheets, the wrapped verifier handles four through 23 blocks and 26 blocks using the bands through width 28. The width-$(m-1)$ band forces every sheet to contain at most $29-m$ seeds.

The 26-stage contraction preserves the occupied sheets in a cyclic cover, so the absence of wrapping at 26 blocks extends to every greater length. At 25 blocks the base check at budget 24 already excludes a fort containing an opening seed and meeting every consecutive pair of appended stages. This version of the check uses the ordinary fort clauses on the base graph. Hence a cyclic fort at 25 blocks allows one of the two insertions that leave the occupied sheets unchanged, giving the same exclusion as at 26 blocks.

At 24 blocks, a wrapped fort at 25 through 28 sheets would have to contain an opening seed and meet every consecutive pair of appended stages. Otherwise either insertion would give a wrapped fort at 25 blocks. The base budget-23 check at 24 blocks then forces at least 24 distinct projected seed labels. The lifted cost is 24, so each label has one selected copy. The insertion-obstruction verifier imposes these conditions. At 25 sheets it uses the width-24 band to cap each sheet at four seeds. At 26 through 28 sheets it partitions the complement of one sheet into two bands whose lengths differ by at most one and are both at least ten. The two bands require at least $m-9$ seeds, leaving a cap of $33-m$ on the omitted sheet. All four formulas are unsatisfiable.

For every $k\geq4$ and $m\geq25$, every minimum-cost cyclic fort therefore unrolls to one of the listed finite forts, and each listed fort projects to the cycle. Its span is at most nine, so the outer run of at least $m-9$ empty sheets is strictly longer than any interior run. The first occupied sheet after this unique longest run determines the translation. The same argument applies to the seed sets, as each meets both extreme sheets of its fort. The exact numbers are $54m$ minimum-cost cyclic forts and $5m$ minimum blocking sets. Their cyclic fort-size polynomial is $mP(x)$. For a minimum blocking set the final white fort contains all its lost seeds, since any smaller seed intersection would contradict minimal cost.

At four through eleven blocks, the wrapped verifier at 24 sheets also excludes cost 24 itself, using the same bands with a cap of five seeds per sheet. The same exact counts and polynomial therefore hold at 24 sheets for these lengths.

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
for blocks in 4 5
do
    python -B research-twins/check_short_prism_covers.py --wrapped "$blocks" 23 20 28 --wrapped "$blocks" 23 21 28 --wrapped "$blocks" 23 22 28 --wrapped "$blocks" 23 23 28 || exit 1
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
```

The complete four- through ten-block enumeration emits a JSON record per chain length.

```sh
python -B research-twins/check_cost_25_blocking_sets.py --blocks 4 5 6 7 8 9 10
for blocks in 4 5 6 7 8 9 10
do
    python -B research-twins/check_short_prism_covers.py --wrapped "$blocks" 28 25 28 --wrapped "$blocks" 29 25 28 || exit 1
done
```

The complete counts use the band checks above and these additional checks. At 26 blocks the long-chain verification supplies the bands through width 25 and the nine- and ten-sheet costs.

```sh
python -B research-twins/check_block_stabilization.py --band-through 28 --band-blocks 26 --certify-sheets 9 10
python -B research-twins/check_block_stabilization.py --subbands-from 13 --band-through 24 --band-blocks 24
python -B research-twins/check_finite_fort_span.py --longer 4 5 6 7 8 9 10 11 12 13 14 15 16 17 26
python -B research-twins/check_prism_projected_support.py --minimum-forts
python -B research-twins/check_prism_opening_insertion.py
for blocks in 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 26
do
    python -B research-twins/check_short_prism_covers.py --wrapped "$blocks" 25 24 28 --wrapped "$blocks" 26 24 28 --wrapped "$blocks" 27 24 28 --wrapped "$blocks" 28 24 28 || exit 1
done
python -B research-twins/check_short_prism_covers.py --insertion-obstruction 25 26 27 28
for blocks in 4 5 6 7 8 9 10 11
do
    python -B research-twins/check_short_prism_covers.py --wrapped "$blocks" 24 24 28 || exit 1
done
```
