# Stabilization in the number of prism-chain blocks

Let $\kappa_{k,m}$ be the minimum number of seeds whose loss blocks recovery in the signed unpadded cyclic prism cover with $k$ blocks and $m$ sheets. For each $m\geq1$,
$$
\kappa_{k,m}=\kappa_{26,m} \qquad (k\geq26).
$$
The [sheet stabilization theorem](MULTIPLE_LOSS_TIMING.md#saturation-of-the-blocking-number-in-cyclic-covers) gives a single constant when $k\geq26$ and $m\geq162$. The constant is at most 24 by the common finite fort, and at least 16 by projection to the eight-sheet cover. The exact value of the constant remains open here.

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

## The seven- and eight-sheet cases

The verifier checks that the signed 26-block covers with seven and eight sheets have blocking numbers 14 and 16. Their SAT clauses require a fort and impose respective budgets of 13 and 15 fort seeds. Rotate a seed belonging to the fort to sheet zero. The additional distance-four clauses follow from the intact two-round process. Both instances are unsatisfiable. The full lifted opening obstruction supplies the corresponding upper bounds. Block stabilization gives the same values at these sheet counts for every $k\geq26$.

Take $m=168$ in the two-parameter stable regime. Reduction to eight sheets is a graph covering because eight divides 168. The image of a fort is a fort at no greater seed cost, so the common stabilized value lies in $[16,24]$.

## Reproduction

```sh
python -B research-twins/check_block_stabilization.py
python -B research-twins/check_block_stabilization.py --certify-sheets 7 8
```

The script checks both band types with PySAT and the normalized seed and edge identifications in 120 interior contractions, including splices next to the first or terminal stage.

The optional run also checks both exact small-sheet thresholds.
