# Stabilization in the number of prism-chain blocks

Let $\kappa_{k,m}$ be the minimum number of seeds whose loss blocks recovery in the signed unpadded cyclic prism cover with $k$ blocks and $m$ sheets. For each $m\geq1$,
$$
\kappa_{k,m}=\kappa_{26,m} \qquad (k\geq26).
$$
The common value is exactly 24 when $k\geq24$ and $m\geq27$. The sheet-band refinement reduces the lower bound to a finite strip for at least 34 sheets, and the cyclic checks cover 27 through 33 sheets. An opening insertion argument extends the result to 24 and 25 blocks. The common 24-seed fort gives the upper bound.

## The prism stage labels

Write stage zero for vertices $0$ through $17$. Appended stage $i\geq1$ has labels $18+16(i-1)$ through $33+16(i-1)$. Its seed offsets are $0,1,2,3,4,5,12,13,14,15$. An edge between two consecutive appended stages uses one of the port pairs
$$
(0,0),\ (9,2),\ (10,2),\ (12,1).
$$
The internal edges of each nonterminal appended stage are the same in these offsets. The terminal stage has the same edges together with $(9,10)$. For $k\geq3$ its only edges to stage zero are from offsets $0$ and $12$ to vertex $16$. The stage-zero edges into the first appended stage go from $5,6,14,17$ to offsets $2,2,0,1$, respectively.

To see the pattern, the first append creates the terminal stage with the stated seed offsets and the two links to vertex $16$. In the next iteration of the [base constructor](check_multiple_loss_bounds.py), the hub is vertex $16$. Its ordered neighbors are vertex $8$ and offsets $0$ and $12$ of the old terminal stage. The prism replacement retains label $16$ as the hub and attaches those neighbors to the retained hub and offsets $0$ and $1$ of the new stage, respectively. Replacing the hub by the prism and moving the tail through the new relay removes the two links to vertex $16$ and the tail edge $(9,10)$ from the old terminal stage. Its replacement links to the new stage are exactly the four port pairs above. The new terminal repeats the old internal terminal graph, seed offsets and two links to vertex $16$. The initial links from stage zero to the first stage survive each append. This gives the stated form by induction.

## Two empty stages in every low-cost fort

Use the first 25 appended stages as a band. Temporarily start with just the seeds of the band blue and allow sources only at vertices of the band whose entire neighborhood lies inside it. Such a source can force any of its neighbors under the ordinary rule. Every deletion of at most 23 of these base seeds still colors every vertex of some two consecutive stages in this band.

The [stage verifier](check_block_stabilization.py) checks this band claim by SAT. White variables denote a candidate set that remains white. At each permitted source outside that set, the clauses forbid exactly one white neighbor. Each consecutive stage pair must contain a white vertex. The number of white variables at seed vertices is bounded by 23. If a deletion left no fully filled pair at closure, the final white set of the restricted process would satisfy all the clauses. The two instances are unsatisfiable. For $k=26$ the right end of the band is terminal. For every $k\geq27$ the right end is nonterminal, with the same internal edges and the same set of permitted sources as for $k=27$.

Suppose a fort in any cyclic cover has cost at most 23. Delete its seeds. Within the band, retain all lifted copies of the band seeds except those whose base labels occur among the deleted seeds. At most 23 base labels are excluded. This starting blue set is contained in the surviving blue set, and its restricted forcing process is a pullback of the verified base process. The two filled stages are therefore disjoint from the fort. This argument also works for integer sheets.

## Insertion and contraction

Insert a new empty stage between two consecutive empty appended stages, using the same port pairs. Every changed edge joins empty stages, and the new vertices see no fort vertex. All unaffected neighbors retain their fort memberships.

To contract a pair, delete one ordinary stage and retain the other. Keep the first appended stage if the pair meets it, and keep the terminal stage if the pair meets that end. For the retained stage, the count of fort neighbors at a given vertex consists of contributions from its two sides. Each contribution is the full old count of the corresponding vertex in one of the empty stages, since its old neighbors on the other side and in its own stage were outside the fort. Each old count is zero or at least two. The port rules preserve the contributions under the splice, so their sum cannot be one. Every other surviving vertex keeps the same count of fort neighbors. All links between appended stages have the same increasing-label sheet shift, so the argument applies at each sheet, including modulo $m$. Seed memberships of all surviving labeled vertices are inherited.

In both directions the cost is unchanged. For $k\geq26$, the two adjacent lengths $k$ and $k+1$ both admit a blocking set of size at most 24 by the published witness. If either minimum is at most 23, the corresponding fort admits insertion or contraction, giving the same upper bound in the other length. Applying this to the smaller of the two minima proves equality. If both are 24, they already agree. This proves stabilization across block counts, uniformly over sheet counts.

## Opening insertion at 24 and 25 blocks

Starting with the opening seeds alone fills the opening by round two for each of these two bases. The process lifts to a cyclic or integer-sheet cover. A fort containing no opening seed is consequently disjoint from the opening. Each opening vertex in $\{5,6,14,17\}$ has a single neighbor outside the opening. The fort condition at every lift of these vertices then excludes offsets $0,1,2$ of the first appended stage from the fort, on every sheet.

Insert an empty first appended stage and relabel every old appended vertex by adding 16. The four opening links now go to the empty new stage. The new stage connects to the old first stage at offsets $0,1,2$, which are also outside the fort. All changed edges therefore join vertices outside the fort. Old terminal links and the signed shifts on retained edges are preserved. This insertion preserves the fort and its seed cost.

For each of 24 and 25 blocks, the [opening verifier](check_prism_opening_insertion.py) excludes any base fort of cost at most 23 that contains an opening seed and meets every consecutive pair of appended stages. A projected fort has no greater cost and retains membership in the opening and in each occupied stage. Thus a lifted fort of cost at most 23 can extend by opening insertion if it omits the opening seeds, or by the empty adjacent pair if it contains one. Iterating gives a fort of the same cost at 26 blocks with the same sheet count. Consequently, wherever the 26-block value is 24, the 24- and 25-block values are also 24.

## A smaller sheet threshold for long chains

Work at $k=26$, which suffices for all longer chains. In the integer-sheet lift, seed only the intact seed vertices of a band of ten consecutive sheets, with two unseeded sheets of margin at each end. Permit sources whose entire neighborhood is in the band plus its margins. If at most five of the band seeds are deleted, the resulting process fills two consecutive sheets of the band. The verifier uses a cyclic graph with two further guard sheets. The clauses enforce the fort inequalities at permitted sources, require every consecutive core-sheet pair to contain some white vertex, and bound the number of white seeds in the core. The formula is unsatisfiable. The allowed sources have the same neighborhoods in the integer lift.

The band result extends to widths eleven, twelve and thirteen with respective loss budgets six, seven and eight. For width $w$, use the left and right $(w-1)$-sheet subbands with their own margins. If neither subband fills a pair, each contains at least $w-5$ lost seeds by the preceding width. With at most $w-5$ total losses all are in the overlap. The verifier excludes that case by fixing the first and last core sheets' seeds blue and using the restricted-source clauses. The margins of both subbands lie inside the permitted region of the wider test.

If a fort of cost $b$ has no two consecutive empty sheets, each cyclic thirteen-sheet window must contain at least nine of its seeds, or the band certificate would fill a pair. Counting the seeds in all $m$ windows gives $9m\leq13b$. For $b\leq23$ this rules out the case without a gap at $m\geq34$. When two empty sheets occur, the fort unrolls to a finite fort of the same cost, by the [gap criterion](MULTIPLE_LOSS_TIMING.md#saturation-of-the-blocking-number-in-cyclic-covers). Conversely a finite fort projects at no larger cost. The eventual constant is at most 24, so these inequalities give equality to the constant for every $m\geq34$.

The twelve-sheet band also shortens the search for a finite integer-sheet fort of cost at most 23. After splitting at any internal gap of two empty sheets, a nonempty piece occupies a span of at most 35 sheets. A span of at least 36 would contain three disjoint twelve-sheet bands. Each would need eight seeds, giving cost at least 24. The bounded search can therefore use 37 sheets, with two outer guard sheets.

More generally, at a budget $b\in\{20,21,22,23\}$ choose three band widths from ten through thirteen that sum to $b+13$. Their seed requirements sum to $b+1$, since a width-$w$ band needs $w-4$ seeds to avoid an empty pair. A piece with no such pair therefore spans at most $b+12$ sheets. The verifier uses the same 37-sheet domain at all four budgets.

The extended verifier gives the same loss bound $w-5$ at widths fourteen through eighteen. For a wrapped fort and $m\geq16$, counting the sixteen-sheet bands gives $12m\leq16b$. In particular, a cost-at-most-23 fort must unroll when $m\geq31$, so the finite exclusion alone now settles every $m\geq31$. At widths seventeen and eighteen the inequalities are $13m\leq17b$ and $14m\leq18b$. The latter rules out wrapping at budget 23 for $m\geq30$. The explicit wrapped cases below use the smaller bands in their formulas.

The width bounds continue through 24 using extra inequalities from certified shorter bands. For a width-$w$ core under a budget $b=w-5$, take any contained band of a verified width $j$ from $\max(10,w-5)$ through $w-2$. If the core has no empty pair, that subband contains at least $j-4$ lost seeds. Its margin lies within the active strip of the wider test. At most $b-(j-4)$ losses therefore lie in the rest of the core. The verifier adds these bounds on the complements of the subbands, along with the pinned end sheets and the original total loss bound. Every added restriction follows from an earlier width.

For a wrapped fort in the cyclic cover, apply these local tests to the periodic lift to the integer sheets. A window of width $w$ may pass the same residue more than once, with each occurrence counted on its own integer sheet. Summing over one period counts each lost seed exactly $w$ times, giving $(w-4)m\leq wb$. Width 23 needs at least 19 losses per band and excludes wrapping below cost 24 already at $m\geq28$. Width 21 also rules out any wrapped fort of cost at most 21 at $m=26$, since $17\cdot26>21\cdot21$. Width 24 requires 20 losses and independently rules out wrapping at budget 22 for $m=27$.

Two disjoint sixteen-sheet bands would cost at least 24, so an inclusion-minimal finite fort of cost at most 23 occupies at most 31 consecutive sheets. At a budget $b\in\{20,21,22,23\}$, choose two widths between thirteen and sixteen summing to $b+9$. These need $b+1$ seeds in total, so a piece without an internal empty pair spans at most $b+8$ sheets. The resulting 33-sheet domain with two guard sheets is sufficient for all four budgets. The verifier also excludes the budget-23 formula on this smaller domain and checks the same 24-seed witness there.

## The seven- through ten-sheet cases

The verifier checks the signed 26-block covers with seven, eight, nine and ten sheets. Their blocking numbers are 14, 16, 18 and 20. The SAT clauses require a fort and impose respective budgets of 13, 15, 17 and 19 fort seeds. Rotate a seed belonging to the fort to sheet zero. The additional distance-four clauses follow from the intact two-round process. The instances are unsatisfiable. The full lifted opening obstruction supplies the corresponding upper bounds. Block stabilization gives the same values at these sheet counts for every $k\geq26$.

Take $m=40$ in the stable regime. Reduction to ten sheets is a graph covering because ten divides 40. The image of a fort is a fort at no greater seed cost, so the common stabilized value is at least 20 before the finite-strip check.

## Finite forts and repeated projected seeds

For a budget $b\leq23$, any finite fort of cost at most $b$ contains a nonempty inclusion-minimal fort of cost at most $b$. It cannot straddle an internal pair of empty sheets, since the two sides would separately be forts. By the twelve-sheet band bound, it occupies at most 35 consecutive sheets. Translate it to start on sheet one and place it in the 37-sheet strip with empty guards. Edges span one sheet, so no neighbor count relevant to the fort changes when the two guards are joined cyclically.

Use a Boolean variable for membership of each vertex. The ordinary fort clauses forbid a vertex outside the selected set from having exactly one selected neighbor. The sheet variables require the guards to be empty, the first interior sheet to be occupied, and no pair of empty sheets before the last occupied sheet. For each selected vertex $v$, we can also demand a local reason why removing it alone would break the fort condition. A singleton cannot be a fort in a cubic graph. If removing $v$ breaks the condition, either $v$ has exactly one selected neighbor, or a neighbor outside the original selected set has exactly two selected neighbors before the removal. Inclusion-minimal forts satisfy this necessary condition. For other fort optimization encodings, see [Cameron and Pulaj](https://arxiv.org/abs/2508.07293).

For a selected nonseed, follow a chosen force from its intact arrival round. If the source belongs to the fort, use that earlier vertex. Otherwise the source must have another neighbor in the fort, since it already sees the selected nonseed. This other neighbor belongs to an earlier round as well. Repeating the argument reaches a selected seed through vertices in the interior. The verifier builds these possible seed sets recursively and requires such a seed for each selected nonseed. This is the guarded version of the [seed ancestry condition](LOSS_COMPONENTS.md).

Projection to the ten-sheet cover identifies selected seeds with the same base label and sheet residue modulo ten. The seed cost of the image fort is exactly the number of occupied projected seed labels. It is at least 20, so at budget $b$ the number of selections beyond the first in each projected fiber, summed over fibers, is at most $b-20$. In particular at budget 20 no fiber can contain two selected seeds. For larger budgets, a Boolean variable counts a selected seed when any earlier seed in its fiber is also selected. The same argument gives a repetition bound of $b-18$ using the nine-sheet cover.

The [finite-strip verifier](check_finite_fort_strip.py) finds the budget-23 formula unsatisfiable and checks the 24-seed witness on the same strip. The guarded strip contains every possible inclusion-minimal finite fort at cost at most 23, so the minimum finite cost is exactly 24. For any $k\geq26$ and $m\geq34$, a cyclic fort of cost at most 23 must have two consecutive empty sheets, since $9m>13\cdot23$. It would then unroll to an excluded finite fort. Hence $\kappa_{k,m}=24$ in this range, and recovery survives any loss of at most 23 seeds. The same argument with budget 22 gives recovery after any loss of at most 22 seeds already at $m\geq32$.

## The 33-sheet case

At 33 sheets, any fort of cost at most 23 would have cost exactly 23 by the budget-22 exclusion and the sheet-band bound. It cannot have consecutive empty sheets, since that would give a finite fort of cost 23. Write $x_i$ for the number of selected seeds on sheet $i$ and $y_i=\sum_{j=0}^{12}x_{i+j}$ for the count in each cyclic thirteen-sheet band. Each $y_i$ is at least nine. Their sum is $13\cdot23=299$, two above $9\cdot33$.

Up to cyclic rotation the two excess units are on the same band, or in two bands separated by a distance of one through sixteen. Each of the seventeen choices fixes the $y_i$. The identities $x_{i+13}-x_i=y_{i+1}-y_i$ determine the sheet counts up to a common additive constant, because stepping by thirteen visits every sheet modulo 33. The total cost of 23 fixes that constant. Discarding nonintegral or negative profiles and those that violate any of the certified ten- through thirteen-sheet bounds leaves twelve profiles, all with at most one seed on each sheet.

The [profile verifier](check_33_sheet_profiles.py) excludes a fort for each of the twelve profiles. It enforces the ordinary fort clauses, the local minimality and seed-ancestry conditions, at least one occupied sheet in every consecutive sheet pair, and an empty adjacent stage pair from the 25-stage band. Boolean sheet flags fix the occupied seed sheets in each case. It also checks the 24-seed witness. Together with block stabilization, this proves $\kappa_{k,33}=24$ for every $k\geq26$.

## The 32-sheet case

A candidate with cost below 24 at 32 sheets must have cost exactly 23 and meet every adjacent sheet pair, by the finite-strip exclusion and the thirteen-sheet bound at budget 22. The other 31 sheets around any given sheet can be partitioned into bands of widths 10, 10 and 11. They require at least $6+6+7=19$ selected seeds. Thus at most four seeds are selected on the given sheet.

The [32-sheet verifier](check_32_sheet_cover.py) encodes four exact count flags on each sheet. Flag $j$ means that at least $j$ of that sheet's seeds are selected. As a new seed is scanned, a successful threshold comes from either the previous prefix at the same threshold or the previous prefix one below the threshold together with that seed. The fifth threshold is fixed false. The sum of all final flags is the total seed cost. For each cyclic band of width $w$ from ten to thirteen the flags in the band sum to at least $w-4$. The total is fixed at 23, and rotation places one selected seed on sheet zero.

Along with the fort, ancestry, local minimality, occupied sheet-pair and empty stage-pair clauses, these requirements are unsatisfiable. The verifier also checks the cost-24 witness. Hence $\kappa_{26,32}=24$.

## The 31-sheet case

At 31 sheets a fort of cost at most 21 would contain two consecutive empty sheets, since $9\cdot31>13\cdot21$. Such a fort would unroll to an excluded finite fort. The only remaining costs below 24 are 22 and 23, and both require a fort meeting every adjacent sheet pair. The 30 sheets other than a given sheet split into three ten-sheet bands, requiring at least 18 seeds in total. The cap on the given sheet is therefore four at budget 22 and five at budget 23. The same count-flag verifier excludes both cases and verifies the cost-24 witness at 31 sheets.

## The 30-sheet case

At 30 sheets a fort of cost at most 20 would unroll by the sheet-band inequality. In a wrapped fort of cost 21, 22 or 23, two disjoint thirteen-sheet bands avoiding a given sheet require at least 18 seeds. This caps the given sheet at three, four or five seeds, respectively. The count-flag verifier excludes all three formulas and checks the cost-24 witness. Thus $\kappa_{26,30}=24$.

## The 29-sheet case

The same division as at 30 sheets holds at 29 sheets. For costs at most 20, $9\cdot29=261>13\cdot20$ gives consecutive empty sheets and the finite exclusion applies. For wrapped forts of cost 21, 22 or 23, the other 28 sheets around a given sheet still contain two disjoint thirteen-sheet bands. At least 18 seeds lie in those bands, so the same caps of three, four and five apply. All three formulas are unsatisfiable, and the inherited fort verifies the upper bound of 24 at 29 sheets. Thus $\kappa_{26,29}=24$.

## The 28-sheet case

For costs at most 19, $9\cdot28=252>13\cdot19$ excludes a wrapped fort and the finite result applies. The other 27 sheets around any given sheet contain two disjoint thirteen-sheet bands, so a wrapped fort has at least 18 seeds outside that sheet. The verifier excludes each budget from 20 through 23 using respective sheet caps of two, three, four and five. Its ordered formulas use the ten- through thirteen-sheet inequalities. The inherited cost-24 witness appears at 28 sheets. Thus $\kappa_{26,28}=24$.

## The 27-sheet case

For costs at most 20, the sixteen-sheet bound rules out wrapping, since $12\cdot27=324>16\cdot20$. An empty pair then reduces to the finite exclusion. For a wrapped fort of cost 21, 22 or 23, the other 26 sheets around any given sheet form two thirteen-sheet bands and contain at least 18 seeds. The verifier imposes the resulting caps of three, four and five and the band bounds of widths ten through sixteen. The three formulas are unsatisfiable and the inherited cost-24 fort verifies the upper bound. Block stabilization and opening insertion give the full range of at least 24 blocks and 27 sheets.

## Reproduction

```sh
python -B research-twins/check_block_stabilization.py
python -B research-twins/check_block_stabilization.py --band-through 24
python -B research-twins/check_block_stabilization.py --certify-sheets 7 8 9 10
python -B research-twins/check_finite_fort_strip.py
python -B research-twins/check_finite_fort_strip.py --sheets 33
python -B research-twins/check_33_sheet_profiles.py
python -B research-twins/check_32_sheet_cover.py
python -B research-twins/check_32_sheet_cover.py --sheets 31
python -B research-twins/check_32_sheet_cover.py --sheets 30
python -B research-twins/check_32_sheet_cover.py --sheets 29
python -B research-twins/check_32_sheet_cover.py --sheets 28
python -B research-twins/check_32_sheet_cover.py --sheets 27
python -B research-twins/check_prism_opening_insertion.py
```

The script checks both stage band types and the sheet bands with PySAT and the normalized seed and edge identifications in 120 interior contractions, including splices next to the first or terminal stage.

The optional run also checks the four exact small-sheet thresholds.

The finite-strip command replays the certified budget-23 exclusion and checks the 24-seed witness. Smaller budgets can be selected with the budget argument. A capped run reports an inconclusive search if the cap is exhausted. [PySAT cardinality encodings](https://pysathq.github.io/docs/html/api/card.html)
