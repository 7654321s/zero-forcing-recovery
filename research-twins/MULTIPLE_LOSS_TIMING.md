# Recovery from several lost initial blue vertices

Use the synchronous rule and initial-color loss model of the [single-loss bounds](ONE_LOSS_TIMING.md). Let $M_{d,t,k}$ be the largest finite recovery time over graphs of maximum degree at most $d$, initial blue sets with intact completion by round $t$, and losses of exactly $k$ initial blue vertices. A $k$-fault-tolerant set recovers from every loss of at most $k$ seeds, in the terminology of [Fault Tolerant Zero Forcing](https://arxiv.org/abs/2509.07854).

- **Degree two.** For $t\geq1$ and $k\geq1$, the exact value is $M_{2,t,k}=t+k(2t+1)$. On cycles the exact value is $t(k+1)+\lceil k/2\rceil$.
- **One intact round.** For $d\geq4$ and $k\geq2$, put $U=1+\lfloor kd/2\rfloor+2k$. The exact value is $U$ for even $k$ and for $d=4,5$. For odd $k$ it is $U-1$ at $d=6$, and $U-2+(d\bmod2)$ at $d\geq7$.
- **At least two intact rounds allowed.** Put $P=d(d-1)^{t-1}$. For $d\geq6$, $t\geq2$ and $k\geq1$,
  $$
  M_{d,t,k}=\frac{kP}{2}+\frac{kP}{2(d-1)}+O\!\left(\frac{kP}{d^2}\right),
  $$
  with one constant for all such $k,t$. For fixed $t$ the expansion is $kd^t/2-k(t-2)d^{t-1}/2+O_t(kd^{t-2})$.

The upper bounds apply whenever the chosen loss recovers. The lower constructions are connected and $k$-fault-tolerant, and have a minimum killing support of size $k+1$. For $d\geq4$ and $k\leq d$, the constructions also have worst restricted time $t$ over losses of at most $k$ from the support.

## A discrepancy forest

Write $D_j$ for the vertices blue in the intact run and white in the delayed run at time $j$, and $A_j=\bigcup_{r\leq j}D_r$. The $k$ deleted seeds form $D_0=A_0$. Assign parents to new discrepancies by the [historical-source rule](ONE_LOSS_TIMING.md#a-tree-of-all-discrepancies). The parent is the chosen intact source if it has ever been discrepant. In the other case, the parent is a currently discrepant neighbor of that source which blocks its delayed force. The parent is born strictly before the new discrepancy. Each root has at most $d$ children and every non-root at most $d-1$: each source is used once, a direct child cannot later be counted as an outside source for the same parent, and a non-root's intact predecessor has already forced. Therefore
$$
|A_j|\leq\alpha_j^{(k)}:=k\left(1+d\sum_{\ell=0}^{j-1}(d-1)^\ell\right).
$$
At time $t$, every remaining white vertex belongs to $A_t$. A finite delayed run adds at least one blue vertex per unfinished round, so $M_{d,t,k}\leq t+\alpha_t^{(k)}$.

## Degree two

On a path take the left endpoint blue and put $k$ consecutive blue pairs farther along. Use $2t$ white vertices before the first pair and between successive pairs, and $t$ whites after the last pair. The two fronts at each internal gap meet in $t$ rounds, and the last pair fills the terminal segment in $t$ rounds. Delete one seed from each pair. Only the left endpoint can start a force. The graph then fills one white per round, passing the remaining isolated seeds as the front reaches them. There are $t+k(2t+1)$ whites, attaining the forest bound.

The left endpoint and the $k$ pairs are disjoint. After any $k$ losses at least one survives intact, and a blue endpoint or a consecutive blue pair forces the entire path. Losing the endpoint and one seed from every pair leaves only isolated interior seeds. Thus the minimum killing size is $k+1$.

### Exact value on cycles

For cycles and every $t\geq0$, $k\geq1$, the worst finite recovery time is $t(k+1)+\lceil k/2\rceil$. Call a maximal blue block active if it has at least two vertices. With some whites present, a finite run must start with an active block. Between successive active blocks in cyclic order, all initially blue vertices are isolated. Each of the two fronts takes the next white vertex from its own end each round until the fronts meet. To see this, between two consecutive whites along the interval there is at most one initially blue vertex. A newly blue white position either forces the next white itself, if they are adjacent, or enables that intervening blue vertex to force the next white. An isolated blue away from both fronts still sees two whites. Thus an interval containing $w$ white vertices fills in $\lceil w/2\rceil$ rounds. With only one active block, its two ends supply the fronts for the interval wrapping around the cycle.

In the intact run every interval between active blocks contains at most $2t$ whites. Deleting seeds can split or remove active blocks, and every delayed active block lies in one of the original active blocks. A delayed interval meeting $g$ original intervening intervals crosses at least $g-1$ original active blocks between them. Each of those blocks contains a loss, since otherwise an active block would remain inside the delayed interval. Consequently $g\leq k+1$. Including the deleted seeds, each delayed interval contains at most $2t(k+1)+k$ whites. This gives the upper bound. If the intact cycle is fully blue, the delayed run starts with at most $k$ whites, and the same interval rule gives at most $\lceil k/2\rceil$ rounds whenever it recovers.

For equality use $k+1$ consecutive blue pairs with exactly $2t$ white vertices between successive pairs around the cycle. Delete the first member of every pair except one. That remaining pair supplies both fronts for a single interval containing $2t(k+1)+k$ whites. If $t=0$, the sole remaining active block also includes the retained seed immediately before that pair, and the single interval still contains $k$ whites. Any loss of at most $k$ seeds preserves a whole pair, so the set is $k$-fault-tolerant. Deleting the first member of all $k+1$ pairs leaves only isolated blue vertices and gives a minimum killing support.

## Exact values for one intact round

Suppose $d\geq4$ and $k\geq2$. Put $U=1+\lfloor kd/2\rfloor+2k$. Then
$$
M_{d,1,k}=
\begin{cases}
U,& k\text{ even or }d\in\{4,5\},\\
U-1,& k\text{ odd and }d=6,\\
U-2+(d\bmod 2),& k\text{ odd and }d\geq7.
\end{cases}
$$

### Upper bound

Take a finite delayed run. Let $h$ be the number of distinct rounds that restore one or more lost seeds. Group the lost seeds by their restoration times, putting times in the same group if they can be joined by consecutive restoration rounds. Let $c$ be the number of groups and $s$ the number containing just one seed. A boundary slot of a group is either the round before its first restoration round or the round after its last. Count these slots by group, so there are $2c$ slots even if two have the same round number.

Every round after the first and without a seed restoration adds an originally white vertex. Select one such target per round. Choose one original intact source for each selected target. A direct target has a lost seed as its source and uses one incidence at that seed. A single-neighbor target has a retained source with one lost neighbor and uses one incidence at that neighbor. A shared-source target has a retained source with $r\geq2$ lost neighbors and uses one incidence at each of them. Let $a,e,m$ be the numbers of selected targets of these three types, and $\delta=\sum(r-2)$ over the shared-source targets. The incidence count is $a+e+2m+\delta$. All these incidences are distinct, because each intact source forces at most one target, and a direct incidence goes to an originally white target. Write $u=kd-(a+e+2m+\delta)$ for the unused capacity.

A single-neighbor target arrives within one round of the return of its lost neighbor. Its source sees only these two possible whites, so whenever either turns blue the other follows by the next round. Since the selected target arrives in a round without a seed restoration, assign it to the corresponding boundary slot.

For a shared-source target, order its lost neighbors by their restoration times. If the latest two times are $\rho-1,\rho$ or both $\rho$, call the target short. Otherwise call it long, with latest time $\rho$ and second-latest time at most $\rho-2$. A long target cannot be blue by $\rho-2$, since its source would restore the last missing neighbor before $\rho$. It fills by $\rho+1$, since all its lost neighbors are blue at $\rho$. Thus the selected long target uses a boundary slot of the group containing the latest neighbor. Each slot is used at most once by the selected single-neighbor and long targets. In particular $a\leq k$, $e\leq2c$, and there are at most $2c-e$ selected long targets.

For every shared source, count its incidences other than the latest two in $\delta$. For a long target its boundary slot also accounts for the incidence at the second-latest seed. Consider a seed in a group of size one. It contributes at most one incidence to a direct target and at most two incidences to its own single-neighbor and latest-neighbor long targets combined, since both types use its group's two slots. It cannot be among the latest two neighbors of a short target, since those two seeds lie in the same group. Its remaining incidence capacity is either unused, counted in $\delta$, or accounted for by a long target's second-latest incidence. Summing over the singleton groups gives $u+\delta+(2c-e)\geq(d-3)s$.

Set $\Lambda=u+\delta+(k-a)+(2c-e)$. If the delayed time is $S$, the selected rounds give
$$
\begin{aligned}
S&\leq1+h+a+e+m
 =1+\frac{kd}{2}+h+\frac{k}{2}+c-\frac{\Lambda}{2}\\
 &\leq 1+\frac{kd}{2}+2k-\frac{(d-4)s}{2}.
\end{aligned}
$$
The final inequality uses $h\leq k$, $c\leq(k+s)/2$, and $\Lambda\geq(d-3)s$. Taking the integer part gives $U$.

For odd $k$ and $d=6$, a singleton group saves at least one round in this bound. If there is no singleton group, $c\leq(k-1)/2$ already saves half a round before rounding, and $kd$ is even. This proves $U-1$.

For odd $k$ and $d\geq7$, it suffices to save $3/2$ rounds from $1+kd/2+2k$ before rounding. A singleton group supplies this saving. If there are no singletons, it also follows from $h\leq k-1$ or $c\leq(k-3)/2$. The only remaining case has $h=k$, $c=(k-1)/2$, and a unique group of three seeds, with distinct consecutive arrival times. Consider the two outer seeds of that group. At most two of their incidences are for direct targets. At most two more are for single-neighbor targets or long targets for which they are latest, by the two slots of the group. If an outer seed is among the latest two neighbors of a short target, the other must be the middle seed, so there are at most $d$ such outer incidences in total. Their remaining capacity is unused or accounted for in $\delta$ or at the second-latest neighbor of a long target. Thus $\Lambda\geq 2d-4-d=d-4$. This supplies the required saving. Rounding gives $U-2+(d\bmod2)$.

### Constructions attaining the bounds

Start with one blue seed $p$ adjacent to one white prefix vertex. Build blocks with one, two or three designated lost seeds. In a block of two seeds use $d-2$ copies of their pair. In a block of three, set $\ell=\lfloor(d-2)/2\rfloor$ and $b=d\bmod2$. Use $\ell$ copies of the pair of the first two seeds, and $\ell+b$ copies of each pair involving the third. In a block of one use no pairs. Each pair occurrence has its own blue source adjacent to its endpoints and a distinct white target.

Give each designated seed a direct white neighbor. Add two more white vertices, the entry target and the exit target. Each has a blue source adjacent to that target and one designated seed. Use the first designated seed for the entry source, and the second for the exit source, or the only seed if there is just one. Join the first direct neighbor to the entry target, and all other direct neighbors to the exit target. From the preceding prefix vertex use blue relays between consecutive entries of the list of all pair targets, then all direct neighbors, then the entry target. The exit target is the preceding prefix vertex of the next block. Each designated seed has degree at most $d$, every direct neighbor has degree at most four, and the two additional targets have degree at most four.

The intact coloring finishes in one round. Every pair target, each direct neighbor and the two other targets have their own intact force, and $p$ fills the first prefix vertex. After all designated seeds are lost, the relays reach a block only from the preceding exit, or from the first prefix. The direct neighbors stay blocked by their white seed and by the entry or exit target until the entry is reached. From there the entry source restores the first seed. In a block of size two or three, every other seed has a shared source with the first, with its pair target already blue, and returns one round later. The exit target then fills, opening the relay into the next block. No later block can start through an internal source until the relay reaches it, since all its designated seeds and targets are still white.

After the common initial round, a block of size one takes four rounds, a block of size two takes $d+4$, and a block of size three takes $\lfloor3d/2\rfloor+4+(d\bmod2)$. For even $k$ use only blocks of size two, giving $U$. For odd $k$ and $d\in\{4,5,6\}$ use one block of size one and $(k-1)/2$ of size two. This gives $U$ for $d=4,5$ and $U-1$ for $d=6$. For odd $k$ and $d\geq7$ use one block of size three and $(k-3)/2$ of size two, giving $U-2+(d\bmod2)$. The protection below preserves the delays and gives recovery from every loss of at most $k$ seeds.

## Two or more intact rounds

### Upper bound

Apply the [last-two-round argument](ONE_LOSS_TIMING.md#the-first-two-asymptotic-terms) to the forest. At time $j$ write $A=|A_j|$, $D=|D_j|$ and $h=A-D$. Let $Q_j$ count links whose endpoints are both currently discrepant. Each reserves an incidence at its parent, to a spent outside source or a still-discrepant direct child. These incidences are distinct and avoid each non-root's intact predecessor. If $r$ roots have recovered, at most $(d-1)h+r$ links have a restored parent and exactly $h-r$ have a restored child. Thus
$$
Q_j\geq A-k-dh,\qquad
\text{available old incidences}\leq(d-1)D+k-Q_j.
$$

Put $i=t-1$, $X=\alpha_i^{(k)}$ and $Y=\alpha_{i-1}^{(k)}$. For each discrepancy born in round $i$, choose one intact source. Let $B_*$ count births with a chosen source outside $D_{i-1}$ that has at least two neighbors in $D_{i-1}$. Each birth uses at least one old incidence, with a second required for those counted in $B_*$. Adding the number retained to the incidence bound and using $Q_{i-1}$ gives $|D_i|+B_*\leq(d-1)Y+2k=X$.

For the final intact round, call a new target exceptional if its selected outside source sees exactly one old vertex. Let $E,N$ count exceptional and nonexceptional targets. Each exceptional target arrives within one round of its old neighbor. The delayed rounds that color an old vertex or an exceptional target number at most $11Y+3B_*$. The old vertices retained from $D_{i-1}$ and those born from direct sources together number at most $2Y$. These and the $B_*$ births, together with their exceptional targets, occupy at most $3(2Y+B_*)$ rounds. Each remaining old vertex was born from an outside source with one old neighbor in $D_{i-1}$. It and its final-round exceptional targets arrive within two rounds of that neighbor, accounting for at most $5Y$ further rounds. This applies when $t=2$, since $D_{i-1}$ is then the set of lost roots.

With at most $|D_i|$ direct sources, $2N+E\leq d|D_i|+k-Q_i$. This is at most both $(d-1)X+2k$ and $d(X-B_*)+k$. Use their weighted average with weight $6/d$ on the second bound to estimate $N$, then add $t+11Y+3B_*$. This cancels the term in $B_*$ and gives
$$
M_{d,t,k}\leq t+11Y+\frac{(d-1)X+2k}{2}+\frac{3(X-k)}{d}.
$$
With $X=k(P-2)/(d-2)$ and $Y=(X-2k)/(d-1)$ this yields the uniform asymptotic upper bound.

### Lower bound

Use $k$ copies of the nonterminal layers from the [guarded construction](ONE_LOSS_TIMING.md#the-first-two-asymptotic-terms). Each has a designated blue seed adjacent to the $d$ blue predecessors of its white roots. Within the $t-1$ nonterminal layers, every parent has $d-1$ children in the next layer, each joined to its parent by a blue degree-two source. The last nonterminal layer contains $L=kd(d-1)^{t-2}$ vertices. Use a direct white terminal child at each of these vertices and the cyclic pair construction with at most $d-2$ incidences per parent. Partition the direct children into groups of size at most $d-2$. Choose a guard from each group and join it to the other members. Use a common seed $s$ and two white prefix vertices, followed by a list of all pair targets, all nonguard direct children, then all guards. Join consecutive list entries by blue relays as in the single-loss construction.

The intact run fills the nonterminal layers on their prescribed rounds and the remaining terminal vertices at round $t$. The relay list alone cannot reach a guard by then, since there are more nonguard targets than $t-2$. On loss of all $k$ designated seeds, the pair sources still see two old whites and each blue nonguard direct child sees its parent and its guard white. The two prefix vertices, all nonguard targets and the first guard fill one per round. Thus
$$
M_{d,t,k}\geq\left\lfloor\frac{dL}{2}\right\rfloor
-\left\lceil\frac{L}{d-2}\right\rceil+3.
$$
After the relay list fills, the direct children force their old parents, the single-parent sources carry the repair upward, and every missing designated seed returns. Substituting $L=kP/(d-1)$ gives the matching first two terms.

## Protection and a minimum killing support

For either construction with $d\geq4$, add a support $H$ of $k+1$ blue vertices. Take a connected simple graph $J$ on $H$. For every edge of $J$, add a blue vertex adjacent to its two endpoints. Connect one of these new blue vertices to $s$. Use $J=K_{k+1}$ if $k\leq d$, and a path otherwise.

Protect every original blue vertex and every added edge source, except the $k$ designated slow-loss seeds. For each protected vertex attach a private all-blue path of $2k+2$ vertices by one endpoint. Each protected vertex has degree at most three before the attachment. The extra blue vertices leave the intact and designated slow runs unchanged, and the resulting graph is connected with maximum degree at most $d$.

Under any loss of at most $k$ seeds, each private path retains at least $k+2$ vertices. Among them there is a consecutive blue pair, which can restore the path and its protected vertex irrespective of that vertex's other neighbors. The edge sources of $J$ can now spread blue through $H$ from at least one retained vertex. At this point only some of the $k$ designated seeds may still be white among the initial blue set. Monotonicity and recovery from the designated all-$k$ loss show that the whole graph recovers.

Losing all of $H$ leaves each of its external neighbors adjacent to two white vertices of $H$. This loss stalls, so $H$ is minimum by fault tolerance. With losses only in $H$, its repair runs in parallel with the intact original run. The blue edge sources of $J$ spread blue one edge per round from the retained vertices. The worst restricted time over at most $k$ losses is therefore $\max(t,\operatorname{diam}J)$, since a loss of $k$ can retain one vertex with maximum eccentricity. For the clique this is $t$.

## Reproduction

Run the following from the repository root.

~~~sh
python -B research-twins/check_multiple_loss_bounds.py
~~~

The script exhausts losses through the budget on the degree-two examples and the smallest protected one-round example. It also checks the cycle upper bound on all initial sets through cycle order eleven for up to three losses. On the larger graphs it checks designated losses, restricted deadlines, the killing loss and samples of clustered and mixed deletions. The proofs above give the guarantees for arbitrary budgets.
