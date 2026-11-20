# Residue-wise growth of cyclic blocking numbers

Let $G$ be a nonempty finite simple graph with integer shifts $\delta_{uv}=-\delta_{vu}$ on its oriented edges. Let $S$ be a zero forcing set of $G$. Denote by $\kappa_m$ the smallest number of seeds whose deletion blocks recovery when $S$ is lifted to the cyclic cover with $m$ sheets. A fort is a nonempty set with no outside vertex having exactly one neighbor in the set. Its seed cost is the number of lifted seeds that it contains. A fort of least seed cost gives $\kappa_m$, since deleting its seeds leaves it white, and a stalled forcing process leaves a fort.

**Theorem.** There is an integer period $P\geq1$ and a rational affine function for each residue class modulo $P$ such that, for all sufficiently large $m$,
$$
\kappa_m=\alpha_{m\bmod P} m+\beta_{m\bmod P}.
$$
The slopes come from minimum mean cycle weights in an explicit weighted directed graph. If a finite fort exists in the integer-sheet lift, all the affine functions are the same constant. If no finite fort exists, every slope is positive. The slopes can differ between residue classes.

## A directed graph of sheet windows

Write $R=\max(1,\max_{uv}|\delta_{uv}|)$, using $R=1$ when there are no edges. A sheet pattern is a subset of $V(G)$ describing which vertices on that sheet belong to a candidate fort. A state is a tuple of $2R$ successive sheet patterns. A window $(X_{-R},\ldots,X_R)$ defines the edge
$$
(X_{-R},\ldots,X_{R-1})\longrightarrow (X_{-R+1},\ldots,X_R)
$$
exactly when, for every $u\notin X_0$, the number of neighbors $v$ with $v\in X_{\delta_{uv}}$ differs from one. The weight of the edge is $|S\cap X_0|$.

A cyclic assignment of patterns gives a length-$m$ closed walk by sliding this window. Conversely, repeating a closed walk gives a periodic assignment, since consecutive states overlap and the last state is identified with the first. This also handles $m\leq2R$, when the same pattern can appear at several offsets in one window. The edge tests enforce the fort condition on every sheet. The sum of edge weights is the seed cost. A closed walk may be rotated to a state containing a nonempty pattern if and only if its fort is nonempty. Therefore $\kappa_m$ is the minimum of the length-$m$ closed-walk weights over starting states containing a nonempty pattern.

There are at most $2^{2R|V(G)|}$ states. For a given $m$, repeated min-plus multiplication or length-by-length dynamic programming gives the exact blocking number. A finite fort in the integer-sheet lift also corresponds to a walk from the all-empty state back to itself through a state containing a nonempty pattern. Extend the walk in both directions by the all-empty loop to recover the finite fort, or surround the fort by sufficiently many empty sheets to obtain the walk. The minimum finite seed cost is thus
$$
\min_{x\ne 0}, \bigl(d(0,x)+d(x,0)\bigr),
$$
where $0$ is the all-empty state and $d$ is ordinary shortest-path distance with the given nonnegative edge weights, taking the value $+\infty$ when no path exists. This is an exact minimum-cost counterpart to the [endpoint feasibility test](FINITE_FORT_PROJECTION.md), which decides existence using only the base labels.

## Slopes and periods

Retain the strongly connected components of the directed graph that contain a directed cycle and a nonempty state. For each such component $C$, let $d_C$ be the greatest common divisor of all its cycle lengths and let $\mu_C$ be the smallest ratio of weight to length among its directed cycles. All closed walks stay in a single component. The min-plus matrix of a component has path costs as entries of its powers. The classical cyclicity theorem gives a period $P_C$ such that at all sufficiently large lengths its powers, after subtracting $\mu_C m$ from each finite entry, repeat modulo $P_C$. This is the min-plus form of the irreducible max-algebra cyclicity theorem. See [Sergeev and Schneider, Sections 1–2](https://arxiv.org/abs/0912.2534).

For each state in $C$, its diagonal entry is finite at sufficiently large lengths exactly when $d_C$ divides the length. Every closed walk decomposes into directed cycles, which proves necessity. For sufficiency, the gcd of lengths of closed walks based at a fixed state equals $d_C$: inserting any cycle at its location into a walk to that location and back gives two lengths differing by that cycle length. A finite set of lengths with this gcd generates all sufficiently large multiples of the gcd by concatenation. Indeed, after dividing by the gcd, the generated residues modulo one of the lengths form an additive subgroup containing all generator residues, hence every residue. Choose one representative length for each residue and add copies of the chosen length.

Take $P$ to be a common multiple of all $P_C$ and $d_C$. At fixed residue $r$, each eligible component $C$ with $d_C\mid r$ contributes an affine function of slope $\mu_C$, from the minimum of its eligible diagonal entries. For large $m$ their finite minimum is the function with the smallest slope, and among ties the smallest intercept. In particular,
$$
\alpha_r=\min_{C: d_C\mid r}\mu_C .
$$
The all-full state is eligible and has a loop, so every residue has a candidate. The [finite-fort gap bound](FINITE_FORT_PROJECTION.md#blocking-numbers-of-the-cyclic-reductions) gives eventual constancy in the finite-fort case and a positive linear lower bound otherwise. Together these give the two assertions about the slopes.

## Minimum density and convergence

Suppose there is no finite fort, and write $\rho=\min_C\mu_C$ over the eligible components. Every closed walk in such a component has cost at least $\rho$ times its length, by decomposition into cycles. A simple cycle attaining $\rho$ can be taken to contain a nonempty state: the all-empty state forms its own strongly connected component when no finite fort exists. This cycle attains $\kappa_m/m=\rho$ at its length, and repeating it attains equality at every multiple. In particular $\rho=\min_{m\geq1}\kappa_m/m$ and $\rho=\liminf_{m\to \infty}\kappa_m/m$.

The normalized blocking numbers converge exactly when some eligible component of period $d_C=1$ has mean $\mu_C=\rho$. That component supplies slope $\rho$ on every residue. Conversely, on the residue $1$ modulo the common period, only components with $d_C=1$ contribute, so their smallest mean must be $\rho$ if there is a limit.

There is also a criterion for attaining the exact minimum density at sufficiently large moduli. In each component with mean $\rho$, keep the edges belonging to cycles of mean $\rho$. Call the resulting subgraph the critical graph. A closed walk attains density $\rho$ exactly when its edges lie in this graph. One implication follows by decomposing a minimum-weight closed walk into cycles. For the converse, write $\rho=p/q$ with $q>0$ and give each edge adjusted weight $qw-p$. There are no negative-weight cycles in such a component. Distances $h$ from a new zero-weight source give nonnegative reduced weights $qw-p+h(u)-h(v)$. Every edge on a minimum-mean cycle has reduced weight zero, because the cycle has total reduced weight zero. Any closed walk along these edges therefore attains density $\rho$.

It follows that at sufficiently large $m$ equality $\kappa_m=\rho m$ holds precisely when $m$ is divisible by the period of at least one strongly connected component of a critical graph. Only components containing a cycle enter this criterion. The periods here are those of the critical graphs, while the criterion for convergence uses periods of the full eligible components.

## Reduction by closed-walk shifts

For a connected base, let $g$ be the nonnegative generator of the subgroup of $\mathbb Z$ consisting of total shifts along closed walks at a fixed vertex. Choose a spanning tree and let $p_v$ be the total shift on its path from the root to $v$. Reindex each copy by $(v,s)\mapsto(v,s-p_v)$. The new shifts $\delta'_{uv}=\delta_{uv}+p_u-p_v$ vanish on the tree. Each non-tree shift equals the total shift on a walk along the tree to $u$, the edge $uv$, and back along the tree. These shifts thus have gcd $g$. This is the spanning-tree normalization of a voltage graph. See [Gross and Tucker](https://doi.org/10.1111/j.1749-6632.1979.tb32796.x).

For $g>0$, let $\widehat{\delta}=\delta'/g$ and write $d=\gcd(m,g)$. The $m$-sheet cover splits into $d$ components, one for each sheet residue modulo $d$, since the attainable translations generate the subgroup of multiples of $d$ modulo $m$. The component at residue $r$ is isomorphic to the $(m/d)$-sheet cover of $\widehat{\delta}$ via $(v,a)\mapsto(v,r+ga\bmod m)$. The map is bijective onto that component since $ga\equiv gb\pmod{m}$ is equivalent to $a\equiv b\pmod{m/d}$. It preserves edges and seed labels. Applying the same coordinate change over the integers gives $g$ copies of the primitive integer-sheet cover.

Writing $\widehat{\kappa}$ for the blocking numbers of $\widehat{\delta}$, this yields the exact formula
$$
\kappa_m=\widehat{\kappa}_{m/\gcd(m,g)} .
$$
A disjoint union blocks when one of its components blocks, so repeating an isomorphic component does not change the minimum. If $g=0$, the sheet components are copies of the base and $\kappa_m=\kappa_1$. A disconnected base is handled by taking the minimum of the values for its base components.

## Divisibility and an example with unequal slopes

If $m\mid n$, projection from the $n$-sheet cover to the $m$-sheet cover takes any fort to a fort. At an outside vertex adjacent to the projected set, lift the adjacency using a selected preimage of the neighbor. The resulting outside preimage has another selected neighbor, and its two neighbors project to distinct vertices by the local bijection. Pulling back a fort in the other direction also preserves the fort condition and multiplies its seed cost by $n/m$. Consequently
$$
\kappa_m \leq \kappa_n \leq (n/m)\kappa_m .
$$

On a base four-cycle, put shift zero on three consecutive edges and shift $q>0$ on the last edge around the cycle. The seeds are the first two vertices along the three zero-shift edges. In the $m$-sheet reduction, taking one turn around the base cycle advances the sheet by $q$, so there are $g=\gcd(m,q)$ components, each a cycle of length $4m/g$. Each component has $m/g$ adjacent seed pairs, with two white vertices separating successive pairs. If any adjacent seed pair in a component survives, that pair forces the whole component. Deleting one seed in every pair leaves only isolated blue vertices, so no force starts in that component. The exact answer is $\kappa_m=m/\gcd(m,q)$. In particular $q=2$ gives slope $1/2$ on even moduli and slope $1$ on odd moduli.

## Exact recovery polynomials by the same sheet windows

Fix the base graph, shifts and designated seed set $S$. Let $Z_m(z)$ count recoverable loss sets in the $m$-sheet cover by cardinality, with weight $z^j$ for a recoverable loss of size $j$. When every vertex is designated, complementing each loss in the full vertex set reverses the coefficients of the zero forcing polynomial. [Boyer and coauthors](https://arxiv.org/abs/1801.08910)

For each possible loss mask $L\subseteq S$ on one sheet, keep the sheet-window edges with $S\cap X_0\subseteq L$. Mark the edge when its center pattern $X_0$ is nonempty. Let $A_L$ be the Boolean relation of all kept edges and let $B_L$ consist of the marked kept edges. A loss word $(L_1,\ldots,L_m)$ blocks precisely when the sheet-window graph has a closed walk following those edge relations and using at least one marked edge. Such a walk gives a nonempty initially white fort, and the pattern sequence of any such fort gives the walk.

After reading a prefix of the loss word, store the pair of Boolean relations $(A,B)$ for all paths and for paths with at least one mark. From the identity pair $(I,\varnothing)$, each letter updates the pair by

$$
(A,B)\longmapsto(A A_L,\ B A_L\cup A B_L).
$$

The loss is recoverable when the final $B$ has empty diagonal. Tracking the mark through the product checks all possible witnesses while counting each loss word once. The pairs form a finite deterministic state space, with at most $3^{|Q|^2}$ states for a sheet-window state set $Q$, since $B\subseteq A$.

Let $T(z)$ have one row and column per reachable relation pair and let its $(u,v)$ entry sum $z^{|L|}$ over all letters taking $u$ to $v$. Let $e$ select the identity pair and $f$ indicate pairs with empty marked diagonal. Then $Z_m(z)=e^\mathsf{T}T(z)^m f$. In particular,

$$
\sum_{m\geq0}Z_m(z)y^m=e^\mathsf{T}(I-yT(z))^{-1} f,\qquad Z_0(z)=1.
$$

This is rational in $y,z$, and the characteristic polynomial of $T(z)$ gives a linear recurrence in the number of sheets. The same construction applies directly to the independent-loss recovery probability by replacing each letter weight with $p^{|L|}(1-p)^{|S|-|L|}$. For a uniformly chosen loss of size $\ell$, recovery has probability $[z^\ell]Z_m(z)/\binom{m|S|}{\ell}$.

For the shifted four-cycle above, let $d=\gcd(m,q)$. A component recovers precisely when at least one of its $m/d$ adjacent seed pairs survives intact. The $d$ components use disjoint seeds, giving

$$
R_m(p)=\bigl(1-(2p-p^2)^{m/d}\bigr)^d.
$$

## Exponential recovery rate and finite interval bounds

Let $s=|S|$, let $t$ be the number of parallel rounds for the intact base forcing set, and keep $R$ as the maximum sheet shift, rounded up to one. Put $b=(4t+2)R$. For independent seed losses with $0<p<1$, let $H_n(p)$ be the probability of recovery on the integer lift when only seeds on $n$ consecutive sheets are subject to loss. The rate

$$
\lambda(p)=\lim_{m\to\infty}\frac{1}{m}\log R_m(p)
$$

exists and has the finite interval bounds

$$
\frac{\log H_n(p)+bs\log(1-p)}{n+b}
\ \leq\ \lambda(p)\ \leq\
\frac{\log H_n(p)}{n}.
$$

The interval has width at most $bs[-\log(1-p)]/(n+b)$. The probability $H_n(p)$ can be computed exactly on the $(n+b)$-sheet cover by allowing losses only on the first $n$ sheets.

Indeed, the intact $t$-round forcing lifts to every cover. An update at a vertex uses only the previous colors within distance two. At time $t$ all remaining white vertices must therefore lie within $2tR$ sheets of some loss. Two loss intervals separated by $b$ sheets whose designated seeds are all intact have at least $2R$ completely blue sheets between their possible white regions at that time. No vertex can have a neighbor in both regions. Restricting any stalled fort to a nonempty region then gives a fort supported near that region alone. Conversely an initially white fort near an isolated loss interval remains white when the other intervals are also subject to loss. The same argument for the periodically repeated configuration of a cyclic cover proves exact factorization for loss intervals separated by these buffers. It also establishes the finite computation of $H_n$.

For an upper bound, partition the cyclic loss word into $\lfloor m/n\rfloor$ disjoint intervals of length $n$, with any remaining sheets at the end. A successful cyclic loss word must recover on every isolated interval by monotonicity on the integer lift. Independence therefore gives $R_m\leq H_n^{\lfloor m/n\rfloor}$. For a lower bound, place $\lfloor m/(n+b)\rfloor$ intervals of length $n$ on the cycle separated by at least $b$ untouched sheets, requiring recovery in each interval and survival of every seed outside them. This gives the claimed lower bound on the limit inferior, while the upper bound holds for the limit superior. Since $(1-p)^{sn}\le H_n\le1$, the two bounds differ by at most the stated width, which tends to zero as $n$ grows.

For the signed prism chains with at least 14 blocks, the [four-sheet certificate](FINITE_FORT_PROJECTION.md#a-finite-representative-for-the-degree-30-boundary-term) gives these same bounds with $b=4$. Across the middle of four intact sheets there are no white vertices within two edges of one another by round five. After lifting a periodically guarded loss to the integer graph, cuts through the intact buffers decompose the final white set into forts whose seed losses lie in single intervals. Each isolated interval therefore contributes exactly its own final white set, by monotonicity and the fort decomposition. In particular $H_n$ can be computed on $n+4$ sheets for these bases.

Equivalently, $\exp(\lambda(p))$ is the spectral radius of the probability-weighted transfer matrix restricted to states reachable from the start and able to reach a recovery state. Each retained path begins and ends in that restriction. The matrix norm gives the upper exponential rate. In a strongly connected component of maximum spectral radius, take returns to a fixed state along lengths permitted by its period. Fixed positive-weight paths into and out of that state give the same exponential rate for the limit superior of accepted walks by Perron–Frobenius. The preceding interval bounds give the limit for all sheet counts.

If the integer lift has a finite fort, choose $n$ containing its seed support. That support is lost with positive probability, so $H_n<1$ and $\lambda(p)<0$. If the integer lift has no finite fort, a loss on finitely many sheets recovers because every white vertex at time $t$ lies in a finite neighborhood of the losses. In this case $H_n=1$ for every $n$ and $\lambda(p)=0$. More specifically, a single intact buffer of $b$ consecutive sheets guarantees cyclic recovery, by isolating the remainder of the cycle. The probability of blocking is at most

$$
\left(1-(1-p)^{bs}\right)^{\lfloor m/b\rfloor},
$$

by testing disjoint potential buffers. For the shifted four-cycle with $q=2$, the exact formula above gives blocking exponents $\log(2p-p^2)$ on odd sheet counts and $\tfrac12\log(2p-p^2)$ on even sheet counts.

## Minimum surviving seeds and the high-loss limit

Let $s_m=ms-\deg Z_m(z)$ be the fewest designated seeds that must survive to force the $m$-sheet cover. There are a rational number $\sigma\geq0$, a positive integer $P$, and rational constants $\tau_0,\ldots,\tau_{P-1}$ such that

$$
s_m=\sigma m+\tau_{m\bmod P}
$$

for all sufficiently large $m$. The slope $\sigma$ is the minimum mean cycle cost in the relation-pair graph restricted to states reachable from the start and able to reach a recovery state, using edge cost $s-|L|$ for loss letter $L$. Moreover,

$$
\lim_{p\uparrow1}\frac{\lambda(p)}{\log(1-p)}=\sigma.
$$

For the slope, remove cycles from any accepting walk. The remaining simple path has bounded length, and each removed cycle has cost at least $\sigma$ times its length. This gives $s_m\geq\sigma m-O(1)$. A fixed prefix and suffix through a minimum-mean cycle of length $\ell$ give accepting words of lengths $a+j\ell$ at cost $\sigma(a+j\ell)+O(1)$. For each large $m$, choose the largest such length at most $m-b$. Isolate its successful loss word and pad the remaining sheets with intact seeds. The guarded-interval result gives recovery and the padding has length between $b$ and $b+\ell-1$. Thus $s_m\leq\sigma m+O(1)$.

For eventual periodicity, subtract $\sigma$ from every edge cost and clear denominators. These integer costs give every cycle nonnegative weight. Every path has weight bounded below by a common constant $-C$, by deleting cycles. An optimal accepted path has total adjusted weight at most a common $C'$ for all large $m$. Its prefix weights therefore stay in $[-C,C+C']$, since any suffix has weight at least $-C$. Track the current state and adjusted weight within this finite interval. Sets of reachable pairs after each step evolve by a fixed map on a finite set, so they eventually repeat periodically. For large $m$ the least accepting weight in this finite construction equals the unrestricted optimum. Undoing the cost scaling gives the stated intercepts.

Disjoint translates of a finite fort can be placed at positive density. At least one seed in each such support must survive, so $\sigma>0$. If the integer lift has no finite fort, keeping one intact buffer of $b$ sheets suffices, giving $\sigma=0$. For the shifted four-cycle, there must be one surviving adjacent pair in each component and each such pair suffices there. Hence $s_m=2\gcd(m,q)$. A lifted edge with both endpoints designated gives $m$ disjoint edges and $s_m=m$.

For the probability limit, an optimal survivor set contributes $p^{ms-s_m}(1-p)^{s_m}$, and there are at most $2^{ms}$ successful loss sets, each of probability at most $(1-p)^{s_m}$. Taking the established exponential rate gives

$$
\sigma\log(1-p)+(s-\sigma)\log p
\ \leq\ \lambda(p)\ \leq\
\sigma\log(1-p)+s\log 2 .
$$

Dividing by $\log(1-p)$ and letting $p$ tend to one gives the claim.

## Reproduction

```sh
python -B research-twins/check_cyclic_fort_growth.py
```

The checker compares 1,192 transfer costs to exhaustive seed deletion on small cyclic covers and compares 298 all-empty round-trip existence tests with the endpoint criterion. It verifies the shifted four-cycle blocking number on 21 moduli and shift choices with both direct forcing and the transfer graph. It checks the closed-walk reduction on the connected three-vertex cases. The relation-pair algorithm also reproduces 894 complete recovery polynomials by exhaustive seed deletion and checks the shifted-cycle recovery probability and minimum survivor count on twelve cases. It checks the positive survivor slope on five lifted-edge covers. For the 298 base instances it checks guarded-interval factorization and the coefficient bounds from isolating losses.
