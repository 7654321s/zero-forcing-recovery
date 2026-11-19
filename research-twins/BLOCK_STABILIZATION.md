# Stabilization in the number of prism-chain blocks

Let $\kappa_{k,m}$ be the minimum number of seeds whose loss blocks recovery in the signed unpadded cyclic prism cover with $k$ blocks and $m$ sheets. For each $m\geq1$,
$$
\kappa_{k,m}=\kappa_{26,m} \qquad (k\geq26).
$$
The [sheet stabilization theorem](MULTIPLE_LOSS_TIMING.md#saturation-of-the-blocking-number-in-cyclic-covers) gives a single constant when $k\geq26$ and $m\geq34$, by the sheet-band refinement below. The constant is at most 24 by the common finite fort, and at least 18 by projection to the nine-sheet cover. The exact value of the constant remains open here.

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

## A smaller sheet threshold for long chains

Work at $k=26$, which suffices for all longer chains. In the integer-sheet lift, seed only the intact seed vertices of a band of ten consecutive sheets, with two unseeded sheets of margin at each end. Permit sources whose entire neighborhood is in the band plus its margins. If at most five of the band seeds are deleted, the resulting process fills two consecutive sheets of the band. The verifier uses a cyclic graph with two further guard sheets. The clauses enforce the fort inequalities at permitted sources, require every consecutive core-sheet pair to contain some white vertex, and bound the number of white seeds in the core. The formula is unsatisfiable. The allowed sources have the same neighborhoods in the integer lift.

The band result extends to widths eleven, twelve and thirteen with respective loss budgets six, seven and eight. For width $w$, use the left and right $(w-1)$-sheet subbands with their own margins. If neither subband fills a pair, each contains at least $w-5$ lost seeds by the preceding width. With at most $w-5$ total losses all are in the overlap. The verifier excludes that case by fixing the first and last core sheets' seeds blue and using the restricted-source clauses. The margins of both subbands lie inside the permitted region of the wider test.

If a fort of cost $b$ has no two consecutive empty sheets, each cyclic thirteen-sheet window must contain at least nine of its seeds, or the band certificate would fill a pair. Counting the seeds in all $m$ windows gives $9m\leq13b$. For $b\leq23$ this rules out the case without a gap at $m\geq34$. When two empty sheets occur, the fort unrolls to a finite fort of the same cost, by the [gap criterion](MULTIPLE_LOSS_TIMING.md#saturation-of-the-blocking-number-in-cyclic-covers). Conversely a finite fort projects at no larger cost. The eventual constant is at most 24, so these inequalities give equality to the constant for every $m\geq34$.

The twelve-sheet band also shortens the search for a finite integer-sheet fort of cost at most 23. After splitting at any internal gap of two empty sheets, a nonempty piece occupies a span of at most 35 sheets. A span of at least 36 would contain three disjoint twelve-sheet bands. Each would need eight seeds, giving cost at least 24. The bounded search can therefore use 37 sheets, with two outer guard sheets.

## The seven-, eight- and nine-sheet cases

The verifier checks the signed 26-block covers with seven, eight and nine sheets. Their blocking numbers are 14, 16 and 18. The SAT clauses require a fort and impose respective budgets of 13, 15 and 17 fort seeds. Rotate a seed belonging to the fort to sheet zero. The additional distance-four clauses follow from the intact two-round process. The instances are unsatisfiable. The full lifted opening obstruction supplies the corresponding upper bounds. Block stabilization gives the same values at these sheet counts for every $k\geq26$.

Take $m=36$ in the stable regime. Reduction to nine sheets is a graph covering because nine divides 36. The image of a fort is a fort at no greater seed cost, so the common stabilized value lies in $[18,24]$.

## Reproduction

```sh
python -B research-twins/check_block_stabilization.py
python -B research-twins/check_block_stabilization.py --certify-sheets 7 8 9
```

The script checks both stage band types and the sheet bands with PySAT and the normalized seed and edge identifications in 120 interior contractions, including splices next to the first or terminal stage.

The optional run also checks the three exact small-sheet thresholds.
