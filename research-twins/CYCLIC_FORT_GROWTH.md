# Residue-wise growth of cyclic blocking numbers

Let $G$ be a nonempty finite simple graph with integer shifts $delta_{uv}=-delta_{vu}$ on its oriented edges. Let $S$ be a zero forcing set of $G$. Denote by $kappa_m$ the smallest number of seeds whose deletion blocks recovery when $S$ is lifted to the cyclic cover with $m$ sheets. A fort is a nonempty set with no outside vertex having exactly one neighbor in the set. Its seed cost is the number of lifted seeds that it contains. A fort of least seed cost gives $kappa_m$, since deleting its seeds leaves it white, and a stalled forcing process leaves a fort.

**Theorem.** There is an integer period $Pgeq1$ and a rational affine function for each residue class modulo $P$ such that, for all sufficiently large $m$,
$$
kappa_m=alpha_{mmod P} m+eta_{mmod P}.
$$
The slopes come from minimum mean cycle weights in an explicit weighted directed graph. If a finite fort exists in the integer-sheet lift, all the affine functions are the same constant. If no finite fort exists, every slope is positive. The slopes can differ between residue classes.

## A directed graph of sheet windows

Write $R=max(1,max_{uv}|delta_{uv}|)$, using $R=1$ when there are no edges. A sheet pattern is a subset of $V(G)$ describing which vertices on that sheet belong to a candidate fort. A state is a tuple of $2R$ successive sheet patterns. A window $(X_{-R},ldots,X_R)$ defines the edge
$$
(X_{-R},ldots,X_{R-1})longrightarrow (X_{-R+1},ldots,X_R)
$$
exactly when, for every $u
otin X_0$, the number of neighbors $v$ with $vin X_{delta_{uv}}$ differs from one. The weight of the edge is $|Scap X_0|$.

A cyclic assignment of patterns gives a length-$m$ closed walk by sliding this window. Conversely, repeating a closed walk gives a periodic assignment, since consecutive states overlap and the last state is identified with the first. This also handles $mleq2R$, when the same pattern can appear at several offsets in one window. The edge tests enforce the fort condition on every sheet. The sum of edge weights is the seed cost. A closed walk may be rotated to a state containing a nonempty pattern if and only if its fort is nonempty. Therefore $kappa_m$ is the minimum of the length-$m$ closed-walk weights over starting states containing a nonempty pattern.

There are at most $2^{2R|V(G)|}$ states. For a given $m$, repeated min-plus multiplication or length-by-length dynamic programming gives the exact blocking number. A finite fort in the integer-sheet lift also corresponds to a walk from the all-empty state back to itself through a state containing a nonempty pattern. Extend the walk in both directions by the all-empty loop to recover the finite fort, or surround the fort by sufficiently many empty sheets to obtain the walk. The minimum finite seed cost is thus
$$
min_{x
e 0}, igl(d(0,x)+d(x,0)igr),
$$
where $0$ is the all-empty state and $d$ is ordinary shortest-path distance with the given nonnegative edge weights, taking the value $+infty$ when no path exists. This is an exact minimum-cost counterpart to the [endpoint feasibility test](FINITE_FORT_PROJECTION.md), which decides existence using only the base labels.

## Slopes and periods

Retain the strongly connected components of the directed graph that contain a directed cycle and a nonempty state. For each such component $C$, let $d_C$ be the greatest common divisor of all its cycle lengths and let $mu_C$ be the smallest ratio of weight to length among its directed cycles. All closed walks stay in a single component. The min-plus matrix of a component has path costs as entries of its powers. The classical cyclicity theorem gives a period $P_C$ such that at all sufficiently large lengths its powers, after subtracting $mu_C m$ from each finite entry, repeat modulo $P_C$. This is the min-plus form of the irreducible max-algebra cyclicity theorem. See [Sergeev and Schneider, Sections 1–2](https://arxiv.org/abs/0912.2534).

For each state in $C$, its diagonal entry is finite at sufficiently large lengths exactly when $d_C$ divides the length. Every closed walk decomposes into directed cycles, which proves necessity. For sufficiency, the gcd of lengths of closed walks based at a fixed state equals $d_C$: inserting any cycle at its location into a walk to that location and back gives two lengths differing by that cycle length. A finite set of lengths with this gcd generates all sufficiently large multiples of the gcd by concatenation. Indeed, after dividing by the gcd, the generated residues modulo one of the lengths form an additive subgroup containing all generator residues, hence every residue. Choose one representative length for each residue and add copies of the chosen length.

Take $P$ to be a common multiple of all $P_C$ and $d_C$. At fixed residue $r$, each eligible component $C$ with $d_Cmid r$ contributes an affine function of slope $mu_C$, from the minimum of its eligible diagonal entries. For large $m$ their finite minimum is the function with the smallest slope, and among ties the smallest intercept. In particular,
$$
alpha_r=min_{C: d_Cmid r}mu_C .
$$
The all-full state is eligible and has a loop, so every residue has a candidate. The [finite-fort gap bound](FINITE_FORT_PROJECTION.md#blocking-numbers-of-the-cyclic-reductions) gives eventual constancy in the finite-fort case and a positive linear lower bound otherwise. Together these give the two assertions about the slopes.

## Divisibility and an example with unequal slopes

If $mmid n$, projection from the $n$-sheet cover to the $m$-sheet cover takes any fort to a fort. At an outside vertex adjacent to the projected set, lift the adjacency using a selected preimage of the neighbor. The resulting outside preimage has another selected neighbor, and its two neighbors project to distinct vertices by the local bijection. Pulling back a fort in the other direction also preserves the fort condition and multiplies its seed cost by $n/m$. Consequently
$$
kappa_m leq kappa_n leq (n/m)kappa_m .
$$

On a base four-cycle, put shift zero on three consecutive edges and shift $q>0$ on the last edge around the cycle. The seeds are the first two vertices along the three zero-shift edges. In the $m$-sheet reduction, taking one turn around the base cycle advances the sheet by $q$, so there are $g=gcd(m,q)$ components, each a cycle of length $4m/g$. Each component has $m/g$ adjacent seed pairs, with two white vertices separating successive pairs. If any adjacent seed pair in a component survives, that pair forces the whole component. Deleting one seed in every pair leaves only isolated blue vertices, so no force starts in that component. The exact answer is $kappa_m=m/gcd(m,q)$. In particular $q=2$ gives slope $1/2$ on even moduli and slope $1$ on odd moduli.

## Reproduction

```sh
python -B research-twins/check_cyclic_fort_growth.py
```

The checker compares 1,192 transfer costs to exhaustive seed deletion on small cyclic covers and compares 298 all-empty round-trip existence tests with the endpoint criterion. It verifies the shifted four-cycle formula on 21 moduli and shift choices with both direct forcing and the transfer graph.
