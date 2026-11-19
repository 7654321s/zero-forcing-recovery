# Recovery from several lost initial blue vertices

Use the synchronous rule and initial-color loss model of the [single-loss bounds](ONE_LOSS_TIMING.md). Let $M_{d,t,k}$ be the largest finite recovery time over graphs of maximum degree at most $d$, initial blue sets with intact completion by round $t$, and losses of exactly $k$ initial blue vertices. A $k$-fault-tolerant set recovers from every loss of at most $k$ seeds, in the terminology of [Fault Tolerant Zero Forcing](https://arxiv.org/abs/2509.07854).

- **Degree two.** For $t\geq1$ and $k\geq1$, the exact value is $M_{2,t,k}=t+k(2t+1)$. On cycles the exact value is $t(k+1)+\lceil k/2\rceil$.
- **Forests and cycle rank.** The exact value on forests of unrestricted degree is $t+k(2t+1)$. At cycle rank $\beta$ and $t\geq1$, an upper bound is $t+k(2t+1)+(2t-1)\beta$. This is exact for $t\geq2$ when $\beta\leq k$, even at degree cap four. For [degree cap three and $t\geq3$](#three-or-more-intact-rounds-at-degree-three), the coefficient is $2t-3$, with equality for $\beta\leq k$. The exact rank classification holds at every rank for $t\geq3$ without a degree cap. For one intact round the exact worst-case time is determined at every cycle rank.
- **One intact round.** The exact value is $1$ for $d=1$ and $1+3k$ for $d=2,3$. For $d\geq4$ one loss gives $5$. For $d\geq4$ and $k\geq2$, put $U=1+\lfloor kd/2\rfloor+2k$. The exact value is $U$ for even $k$ and for $d=4,5$. For odd $k$ it is $U-1$ at $d=6$, and $U-2+(d\bmod2)$ at $d\geq7$.
- **Joint degree and cycle rank.** For one intact round the exact maximum is determined jointly for every degree cap at least three, cycle rank, and loss budget.
- **Two intact rounds.** At degree three, $2+7k\leq M_{3,2,k}\leq 2+9k$, with $M_{3,2,1}=9$. The [maximum for one lost seed at degree three](ONE_LOSS_TIMING.md#cycle-rank-at-degree-three) is seven at rank zero, eight at ranks one through three, and nine at rank at least four. The [degree-three cycle-rank maximum](#a-cycle-rank-bound-at-degree-three) is $2+5k+\beta$ for $\beta\leq k$, $2+6k$ for $\beta=k+1,k+2$, and $3+6k$ for $\beta=k+3$. At degree four, $M_{4,2,k}=2+13k$. Without a degree cap the exact maximum is known at every cycle rank and positive loss budget, for [one lost seed](#two-intact-rounds-and-one-lost-seed-at-every-cycle-rank) and for [multiple lost seeds](#two-intact-rounds-and-multiple-lost-seeds-at-every-cycle-rank).
- **At least two intact rounds allowed.** Put $P=d(d-1)^{t-1}$. For $d\geq6$, $t\geq2$ and $k\geq1$,
  $$
  M_{d,t,k}=\frac{kP}{2}+\frac{kP}{2(d-1)}+O\!\left(\frac{kP}{d^2}\right),
  $$
  with one constant for all such $k,t$. For fixed $t$ the expansion is $kd^t/2-k(t-2)d^{t-1}/2+O_t(kd^{t-2})$.

The upper bounds apply whenever the chosen loss recovers. All lower constructions for $d\geq2$ are connected. The degree-three construction for two intact rounds gives recovery for the designated $k$-seed loss. The other lower constructions for $d\geq2$ are $k$-fault-tolerant and have a minimum killing support of size $k+1$. The constructions with clique support also have worst restricted time $t$ over losses of at most $k$ from that support.

## A discrepancy forest

Write $D_j$ for the vertices blue in the intact run and white in the delayed run at time $j$, and $A_j=\bigcup_{r\leq j}D_r$. The $k$ deleted seeds form $D_0=A_0$. Assign parents to new discrepancies by the [historical-source rule](ONE_LOSS_TIMING.md#a-tree-of-all-discrepancies). The parent is the chosen intact source if it has ever been discrepant. In the other case, the parent is a currently discrepant neighbor of that source which blocks its delayed force. The parent is born strictly before the new discrepancy. Each root has at most $d$ children and every non-root at most $d-1$: each source is used once, a direct child cannot later be counted as an outside source for the same parent, and a non-root's intact predecessor has already forced. Therefore
$$
|A_j|\leq\alpha_j^{(k)}:=k\left(1+d\sum_{\ell=0}^{j-1}(d-1)^\ell\right).
$$
At time $t$, every remaining white vertex belongs to $A_t$. A finite delayed run adds at least one blue vertex per unfinished round, so $M_{d,t,k}\leq t+\alpha_t^{(k)}$.

## Sharp bound for forests and an extension by cycle rank

Let $\beta(G)=|E(G)|-|V(G)|+c(G)$, where $c(G)$ is the number of connected components. If the intact run finishes by round $t\geq1$ and the run with $k\geq1$ deleted seeds finishes at round $T$, then
$$
T\leq t+k(2t+1)+(2t-1)\beta(G).
$$
At $t=0$ there are only $k$ delayed whites initially, giving $T\leq k$. At $\beta(G)=0$ the bound is attained for every $t,k$, already on paths with $k$-fault-tolerant initial sets. The maximum over connected trees therefore has the same value, with no degree restriction.

**Realize the discrepancy forest inside $G$.** For each new discrepancy $v$, let $u$ be its chosen intact source. If $u$ has already been discrepant, add the edge $uv$ to the forest. Otherwise let $x$ be a discrepant neighbor blocking $u$ in the delayed run and add the path $x,u,v$. In this second case $u$ is blue in both runs at the start of the round and has never been discrepant. It stays out of $A_t$ and serves as an intermediate vertex at most once, since it uses its intact force at this step. Thus every attachment adds the new vertex $v$ and possibly a fresh intermediate vertex. The resulting subgraph $F$ consists of $k$ disjoint subtrees rooted at the lost seeds, with the vertices of $A_t$ marked. Along a path from a root there are at most $t$ marked nonroot vertices, since their discrepancy birth rounds strictly increase. Every simple path in one subtree therefore has at most $2t$ marked nonroot vertices, by splitting it at the common ancestor of its endpoints.

**Trace the late rounds backwards.** Use the propagation trail of [Hogben et al., Lemma 4.1](https://arxiv.org/pdf/1410.4191), stopped at round $t+1$. If $T>t$, start from a vertex colored at round $T$. From a vertex $v$ colored at round $r>t+1$, choose a delayed source $u$ that forces $v$ in round $r$. If $u$ became blue at $r-1$, follow $vu$. Otherwise $u$ was already blue at $r-2$. Some other neighbor $x$ must have blocked it at time $r-2$ and become blue by time $r-1$, since $v$ did not fill in round $r-1$. Follow $v,u,x$. This chooses a distinguished vertex of arrival time $r-1$ and ultimately yields one distinguished vertex for every round $t+1,\ldots,T$. All of them are in $A_t$ because they were white at time $t$.

The resulting walk has no repeated edge. Edges from a target to its chosen source run from later to earlier arrival times, and those from a source through a last blocker run from earlier to later arrival times. An edge can appear at most once in either role, because its later endpoint is distinguished and each arrival time has exactly one distinguished vertex. If it occurred in both roles, the later endpoint would have to be the same distinguished occurrence in consecutive steps. The earlier endpoint would then be the chosen source for two forces, which is impossible.

**Count visits after contraction.** Contract each subtree of $F$, retaining loops and parallel edges for the edges outside $F$. The projected walk still uses each edge at most once. A trail using $e$ edges and visiting $v$ distinct vertices has $e+1$ vertex occurrences, so its number of repeated occurrences is $e-v+1$. This is the cycle rank of its connected trace and is at most $\beta(G)$ because contracting the forest preserves cycle rank. Hence there are at most $k+\beta(G)$ visits to the contracted subtrees.

During a visit, the original trail follows a simple path in one subtree. A visit containing the distinguished root has at most $2t+1$ distinguished vertices. In any other visit the path can use at most one branch of the root. Indeed, to pass through the root as an intermediate delayed source, both adjacent trail vertices must be distinguished. An indirect child path starts with a vertex blue by time $t$, whereas a direct child contributes an edge to a marked vertex. The root can have at most one direct child, since it makes at most one intact force. In a single branch, the common ancestor is below the root and the path contains at most $2t-1$ marked vertices below the root. Thus each visit contributes at most $2t-1$ distinguished vertices, with at most two more on the unique visit distinguishing its root. Summing gives $(2t-1)(k+\beta(G))+2k$ distinguished vertices. The argument also works with the cycle rank of the subgraph formed by $F$ and the edges incident to at least one vertex white at time $t$, since each edge of the original trail is incident to a distinguished vertex.

For equality when $t\geq1$, use the [degree-two path construction](#degree-two). At $t=0$, start with all $2k+1$ vertices of a path blue and delete its final $k$ vertices. They fill one per round. Any loss of at most $k$ leaves an endpoint or a consecutive blue pair, and keeping just the $k$ alternating internal vertices stalls. The minimum killing size is therefore $k+1$ here as well.

### Exact values when the cycle rank is at most the loss budget

For $t\geq2$, $k\geq1$, and $0\leq\beta\leq k$, the exact maximum finite recovery time on connected graphs of rank $\beta$ is
$$
t+k(2t+1)+(2t-1)\beta .
$$
This also gives the exact maximum under any degree cap at least four, since the examples have maximum degree four. Their initial sets are $k$-fault-tolerant and have a minimum killing support of size $k+1$. The upper bound is the preceding trail bound.

**Propagation along an arm.** An arm of length $j$ consists of $j$ initially white vertices extending from a center. Place a separate initially blue vertex of degree two between each consecutive pair, including the center and the first arm vertex. When one endpoint of one of these two-edge links is blue, its relay can force the other endpoint one round later. Read each arm from its center outwards.

**Blocks and their intact runs.** Begin with a path of $t$ edges from a blue seed $s$ to a white endpoint, with the other $t$ vertices white. Each block has one designated lost seed $z$ as its main center, with left and right arms of length $t$. Its exit is the far endpoint of the right arm. An ordinary block has its entry at the far endpoint of the left arm.

To give a block one cycle, put an initially white vertex $w$ adjacent to $z$. Give $w$ two arms of length $t-1$ and an initially white leaf $g$. Join the far endpoint of the second arm at $w$ directly to the far endpoint of the left arm at $z$. The far endpoint of the first arm at $w$ is now the entry. Deleting the edge between the two far endpoints leaves a tree, so this block has rank one. The vertex $w$ has degree four. All other block vertices have smaller degree, even after connecting each block to the preceding endpoint by an edge.

In the intact run, the relay arms at $z$ fill from their center, and $z$ forces $w$ in round one. The arms at $w$ then fill outwards, and $w$ forces $g$ in round two. All far endpoints arrive at round $t$. The edges joining far endpoints, and the incoming edges from preceding exits, can give no earlier arrivals because both their endpoints are white through round $t-1$ in this schedule. The initial path fills successively through round $t$. Thus the intact run takes exactly $t$ rounds.

**The designated loss and concatenation.** Delete the center $z$ of every block from the initial set. In either type of block, all white vertices wait for the incoming endpoint. The relays inside the block are initially blocked by two whites. An ordinary block then fills from its entry along the left arm to $z$ and out along the right arm, one new vertex per round for $2t+1$ rounds.

In a block of rank one, the run first traverses the first arm at $w$, then $w$, then its second arm. This takes $2t-1$ rounds. During these rounds $w$ cannot force $z$ or $g$, since both are white. The edge between far endpoints then starts the same $2t+1$ rounds at the left arm of $z$. The leaf $g$ fills in the round after $z$, together with the first white vertex on the right arm at $z$. This contributes no extra round. Each exit starts the next block one round later.

Take $\min(k,\beta)$ blocks of rank one and make the other blocks ordinary. The links between blocks are bridges. If $\beta>k$, add the unused rank by attaching a chain of all-blue triangles at $s$ by bridges. The designated time is $t+k(2t+1)+(2t-1)\min(k,\beta)$.

Use the [seed protection](#protection-and-a-minimum-killing-support) with a path for $J$. It preserves the rank and the designated arrival times. Every protected vertex had degree at most three before its private path is attached, so the final maximum degree is four. This also proves attainment in the fault-tolerant class.

### A lower bound beyond the low-rank range

For $t\geq2$ and degree cap $d\geq4$, put $b=\min(k,\beta)$ and
$$
m=\min\left\{\left\lfloor\frac{\beta-b}{2}\right\rfloor,\ b(d-3)\right\}.
$$
There are connected examples of rank $\beta$ with intact time $t$ and designated delayed time
$$
t+k(2t+1)+(2t-1)b+m.
$$
The protective paths and support have the same guarantees as in the low-rank construction.

Distribute the $m$ extra targets among the $b$ rank-one blocks, with at most $d-3$ in each. In one such block let $u$ be the far endpoint of the main left arm at $z$. For each new target $y_i$, add a separate relay arm of length $t-1$ at $z$ and join its far endpoint directly to $y_i$. Also join $y_i$ directly to $u$. Replace the former crossing edge into $u$ by a direct edge into $y_1$, followed by individual blue relays between the successive members of $y_1,\ldots,y_j,u$, where $j$ is the number of extra targets in the block.

In the intact run each $y_i$ is forced at round $t$ by the far endpoint of its new arm. The edges joining targets and $u$ do not act earlier. In the designated run the end of the second arm at $w$ first forces $y_1$, and the relays then fill the other targets and $u$ successively. Before $u$ is blue, every blue $y_i$ still sees both $u$ and its own new arm endpoint white. After $u$ arrives, these targets force their arm endpoints, and the added arms fill towards $z$ in parallel with the original left arm. Each reaches $z$ in the same round as that original arm. The following arrivals are unchanged, so the block gains $j$ rounds.

The extra arms and their attached targets are trees. Routing the crossing through their targets adds $j$ to the rank, and the $j$ direct edges from the targets to $u$ add another $j$. The degree of $z$ is $3+j$, that of $u$ is $2+j$, and each extra target has degree at most four. The initially blue relays still admit the same private paths. All unused rank can be supplied with the all-blue triangle chain.

<a id="two-intact-rounds-and-one-lost-seed-at-cycle-ranks-two-and-three"></a>

### Two intact rounds and one lost seed at every cycle rank

Let $M_\beta$ be the largest finite recovery time on connected graphs of cycle rank $\beta$ after one lost seed, with intact time at most two and no degree restriction. Then
$$
M_0=7,\qquad
M_\beta=\left\lfloor\frac{\beta+19}{2}\right\rfloor
\quad(\beta\geq1).
$$
The forest bound gives $M_0$. The [extra-target construction](#a-lower-bound-beyond-the-low-rank-range) attains the positive-rank value with $m=\lfloor(\beta-1)/2\rfloor$ and maximum degree at most $\max(4,3+m)$. It gives a one-fault-tolerant initial set, and the same formula is exact under a degree cap $d\geq4$ whenever $\beta\leq2d-4$. In particular, ranks one and two have maximum ten, and ranks three and four have maximum eleven.

#### Near and far arrivals

It suffices to consider $T>2$. Use the discrepancy forest $F$ and late trail for $t=2$. Its only root is the lost seed $z$. Call vertices marked by intact time one old. There can be at most one first-round child $c$ attached directly to $z$. Every other first-round child $w$ is attached through a retained initial source that originally had $w$ as its only white neighbor. The source's only possible delayed whites at the start are $w$ and $z$, so their delayed arrivals differ by at most one round.

Write $r$ for the return time of $z$, and, if $c$ exists, write $s$ for its arrival time. Call the times in $[r-2,r+2]$ and in $[s-1,s+1]$ near, using just the first interval when $c$ is absent. Other times are far. Let $n$ and $f$ count the distinguished near and far vertices, respectively, so $T-2=n+f$. There are at most eight near times. Every distinguished old vertex is near, and their number $O$ is at most four, since they use only $r-1,r,r+1$ and possibly $s$.

Every visit with two or more distinguished vertices contains an old distinguished vertex. A visit distinguishing the root has at most two marks on each side of it. Its distinguished vertices therefore all arrive within two rounds of $z$. For a visit without the distinguished root, the marks lie in one branch. If it has two depth-two marks then their first-round parent must also be distinguished. Otherwise that parent would be an intermediate source between two distinguished vertices, with both downward edges direct, since the intact relays of $F$ are blue by time two. A vertex can make at most one intact force, so this cannot happen. A visit of size at least two in the branch thus distinguishes its first-round child, and the other marks are at most one round away from it. They are near, whether the first-round child is $c$ or another child of $z$.

It follows that each far target occupies its own visit and is a discrepancy born in round two. All discrepancies born in round two are leaves of $F$.

#### Blocking edges for far targets

For each far target $y$, choose one edge outside $F$ by the following rules.

- If its intact source $p$ is a retained relay of $F$, then $p$ has an old neighbor other than the chosen parent of $y$. Without such a neighbor, the source would have only its parent and $y$ as possible whites after delayed round one, and their arrivals would differ by at most one. This would make $y$ near. Choose the edge from $p$ to an extra old neighbor.
- If $y$ is a direct child of an old vertex $w$ and arrives at least two rounds before $w$, choose an edge $yg$ to another vertex white when $y$ returns. Without it $y$ would force $w$ in the next round.
- If $y$ is a direct child of $w$ and arrives at least two rounds after $w$, then $w$ needs another late old neighbor. Its other neighbors were blue in the intact run at time one. If $w=z$, the child $c$ does not exist, since the intact force of $z$ was used on $y$. All old neighbors of $z$ then return by $r+1$, and $y$ would fill by $r+2$. For a first-round child other than $c$, every edge to another old vertex is outside $F$. For $w=c$, the edge $cz$ is in $F$, but it cannot be the only edge to an old neighbor still white when $c$ returns. If $z$ is already blue, $y$ would follow immediately. If $z$ is still white, $y$ would arrive by $r+1$. A far arrival would then have to occur by $r-3$, and $c$ could force $z$ at the next round, a contradiction. In the possible cases choose an edge from $w$ to an old neighbor outside $F$ that returns later than $w$.

Each of these edges joins two vertices of $F$. The first type has a retained relay as an endpoint, the second has a round-two target and its later-arriving neighbor, and the third joins two old vertices. Edges of the first type identify a unique intact source and hence a unique target. Edges of the other types identify their owners by the earlier arrival time. An old source owns at most one direct target. Therefore the chosen edges are all distinct.

#### Charging the rank and the trail sides

Let $N$ count visits with at least one near mark, let $Z$ count visits to $F$ with no distinguished mark, and let $U$ count chosen blocking edges not on the trail. There are $f+N+Z$ visits to $F$. The union of $F$ and the trail is connected. Its rank is at least $f+N+Z-1$, since contracting $F$ gives at least that many repeats of its vertex. Each unused blocking edge adds one to that rank, so
$$
\beta\geq f+N+Z-1+U .
$$

Every chosen edge that is on the trail charges either a free side of a distinguished old vertex or one of the $Z$ visits. A side is free when it has no other distinguished vertex in the same visit. A retained-relay edge is used at a distinguished old endpoint because the relay is already blue by delayed time one. A late direct blocker joins two old vertices, at least one distinguished on the step using it. In either case the edge leaves the visit immediately on the charged side.

For an early direct target, the edge $yg$ cannot be used at the distinguished occurrence of $y$. The later-arriving $g$ cannot be an intermediate source there, and $y$ cannot force $g$ while its parent is white. Thus $y$ is an intermediate source between two distinguished vertices. If the other edge of the step is its sole forest edge to its old parent, charge the side of that distinguished parent ending at $y$. Otherwise both edges leave $F$, so this occurrence of $y$ is a visit with no mark. The charges are distinct because each used side has a single boundary edge and each such unmarked visit has just the one intermediate occurrence of its owner. If $C$ old sides are charged, then $f\leq U+C+Z$. In particular,
$$
\beta\geq2f+N-1-C .
$$

Write $L$ for the number of steps between consecutive distinguished old vertices within the same visit, and $B$ for their number across different visits. The available old sides give
$$
C-N\leq 2O-n-L-B.
$$
To see the within-visit count, consider a near visit with $o$ old marks and $q$ round-two marks. The latter are leaves and can only be endpoints, so $q\leq2$. If $o=0$, it is a singleton round-two visit and has no old sides. Otherwise at most $2-q$ sides are free and the $o-1$ steps between old marks are consecutive within this visit. In both cases the number of free sides minus one is at most $o-q$ minus the number of these internal steps. Summing gives $2O-n-L$ before accounting for the split steps.

Each split step forces one further unused side. A direct step between old vertices uses just one edge. A step through an intermediate vertex also contains at most one chosen blocking edge. If the intermediate vertex is an unmarked retained relay, both edges could belong only to its single intact target. If it is an old vertex, its arrival is earlier than both endpoints of the step, so any old-to-old blocker on the step belongs to its one direct target. If it was born in round two, the only possible owner of a blocker on the step is that same round-two vertex acting as an early direct child. Thus the two facing old sides of a split step receive at most one charge, and these pairs of sides are distinct.

It follows that
$$
\beta\geq2(T-2)-(n+2O+1-L-B).
$$
If $O\leq3$, the term in parentheses is at most $8+6+1=15$. If $O=4$, the times $r-1,r,r+1$ are all occupied by distinguished old vertices, so $L+B\geq2$. The term is again at most $8+8+1-2=15$. Hence $\beta\geq2T-19$, proving the claimed positive-rank upper bound.

<a id="two-intact-rounds-and-multiple-lost-seeds-at-large-cycle-rank"></a>
<a id="exact-values-for-two-lost-seeds-at-every-cycle-rank"></a>

### Two intact rounds and multiple lost seeds at every cycle rank

Write $M_{\beta,k}^{(2)}$ for the largest finite recovery time on connected graphs of cycle rank $\beta$, after $k$ seed losses and with intact time at most two. For every $k\geq2$ and $\beta\geq0$, without a degree cap,
$$
M_{\beta,k}^{(2)}=
\begin{cases}
2+5k+3\beta,&0\leq\beta\leq k,\\
2+8k+\lfloor(\beta-k)/2\rfloor,&k+1\leq\beta\leq k+2,\\
8k-2+3\lfloor(\beta-k+1)/2\rfloor,&\beta\geq k+3.
\end{cases}
$$
The [low-rank constructions](#exact-values-when-the-cycle-rank-is-at-most-the-loss-budget) give the first line, including the upper bound. The [extra-target construction](#a-lower-bound-beyond-the-low-rank-range) gives the second line at degree four, and the [pair construction](#a-construction-from-a-pair-of-lost-seeds) with a detour for each lost seed gives the third line. All examples recover from any loss of at most $k$ seeds. They attain the same values under degree cap $d\geq4$ whenever $\beta\leq k+2d-4$.

#### Counting the visits with shared first-round sources

If $T>2$, take the late trail and the discrepancy forest $F$ at $t=2$. Let $V$ be the number of trail visits to the subtrees of $F$, including visits with no distinguished marks. Each visit with the distinguished root has at most five marks. A visit with no distinguished root has its marks in at most one branch and has at most three marks. If it has at least two marks, it must distinguish the first-round child heading the branch. The argument is the same as for one loss. Joining two depth-two leaves without distinguishing their common parent would require two direct intact forces from that parent. When the visit has three marks, the first-round child occupies the middle of its three consecutive times.

Classify a first-round child according to its chosen intact source. It can be direct from a lost root, from a retained source with one lost neighbor, or from a retained source with two or more lost neighbors. Call the last type shared. Let $B$ be the number of visits without the distinguished root that have at least two marks and distinguish a shared child. For each such visit choose the edge from the retained intact source to a lost neighbor other than its parent in $F$. These edges are distinct and outside $F$, since each intact source is chosen for only one target.

Suppose $Q$ of the chosen edges are used by the trail. Such an edge must use its lost endpoint as a distinguished vertex, since the retained source is blue throughout the delayed run. It exits the visit on a side of that distinguished root with no further mark in the same visit. Each such free side can pay for at most one chosen edge.

The other $B-Q$ edges can be added to the union of $F$ and the trail. If the trail visits $v$ distinct subtrees, that union has rank at least $V-v$ by contraction, and has $k-v+1$ components. At most $k-v$ of the added edges can join components. It follows that
$$
\beta\geq V+B-Q-k.
$$

#### Counting the remaining visits

Give each visit an allowance of $3/2$ marks, or three marks if it is one of the $B$ shared visits. The shared visits stay within their allowance. The rootless visits of size at least two centered at direct children can each exceed their allowance by at most $3/2$. There are at most $k$ direct children.

For a lost root $z$ returning at round $r$, group its distinguished-root visit with the rootless visits of size at least two centered at its single-neighbor children. Let $v_z$ be the number of these visits and $n_z$ the number of marks in them. Each of these marks is in $[r-2,r+2]$. For the root visit this follows from its path lengths, and for the others the retained first-round source puts the center within one round of $z$. Thus $n_z\leq5$. Let $Q_z$ count the chosen edges paid by the free sides of $z$. We claim
$$
n_z-\tfrac32 v_z+\tfrac32 Q_z\leq\tfrac72 .
$$

- If the root is undistinguished then $Q_z=0$. One visit contributes at most three marks, and two or more have at most five marks together.
- If the root visit has marks on both sides then $Q_z=0$. The bound follows from $n_z\leq5$ and $v_z\geq1$.
- If the root visit has marks on just one side then $Q_z\leq1$. With one visit there are at most three marks. With two or more, use $n_z\leq5$.
- If the root is the only mark in its visit then $Q_z\leq2$. A separate visit centered at a single-neighbor child has at most two marks, since a three-mark visit would occupy round $r$ already used by $z$. Thus $n_z\leq1$ for one visit, $n_z\leq3$ for two visits, and $n_z\leq5$ for three or more.

Write $A_z=n_z-3v_z/2+3Q_z/2$ for the contribution of root $z$. Since all visits left out of the groups have at most one mark, $T-2$ is at most $3(V+B-Q)/2+\sum_z A_z+3k/2$. A sharper estimate depends on whether any two restoration rounds differ by at most one.

#### Extra edges for isolated second-round marks

An old vertex is a discrepancy marked by intact round one. As in the [one-loss proof](#blocking-edges-for-far-targets), consider a distinguished second-round mark $y$ whose delayed arrival is outside every root window $[r-2,r+2]$ and differs by at least two from that of its forest parent $w$. We use this argument when every lost seed has a direct first-round child, so no lost seed can be the intact source of a second-round target.

- If $y$ has an indirect parent, the unmarked intact source $p$ is blue by delayed time one. If $p$ has no other old neighbor, its only possible whites after that round are $y$ and the old parent $w$. Their arrivals then differ by at most one, including when $w$ arrives in round one. Choose the edge from $p$ to a second old neighbor.
- If $y$ has a direct parent and arrives first, choose an edge from $y$ to another vertex still white when $y$ arrives. Otherwise $y$ would return $w$ in the next round.
- If $y$ has a direct parent and arrives later, $w$ has another old neighbor still white when $w$ arrives. All neighbors of $w$ besides $y$ were blue by intact time one, and $w$ returns at or after round two. Among these other neighbors, the only possible forest edge to an old vertex is the edge to a lost seed $z$ of which $w$ is the direct child. If $z$ were the sole other neighbor still white when $w$ returns, the arrivals of $y,z$ would differ by at most one. This would put $y$ in a root window. Choose an edge from $w$ to another old neighbor still white when $w$ returns.

These edges lie outside $F$ and have both endpoints in $F$. They are distinct across the three types and among different targets. For the indirect case the edge identifies the intact source, and for the two direct cases the earlier endpoint identifies the target or its unique intact source. An edge of the indirect type also differs from every guard chosen for a shared first-round child, since each intact source forces only once.

Each such edge on the trail uses either a free side of a distinguished old vertex or a visit with no marks. For an indirect edge or a late direct edge, at least one old endpoint is distinguished, and the edge is the boundary on its free side. For the early direct edge $yg$, with $g$ arriving after $y$, it cannot be used at the distinguished occurrence of $y$. The later vertex $g$ cannot be an intermediate source there, and $y$ cannot directly force $g$ immediately after it arrives because $w$ is still white. Thus the edge is used with $y$ as the intermediate source. Its other edge is either the only forest edge $yw$, in which case the guard is the boundary on the free side of $w$, or an edge outside $F$, in which case the visit at that occurrence of $y$ has no marks. These charges are distinct since every side has a single boundary edge and each visit without marks has just one intermediate source.

#### A pair of seeds restored in the same or consecutive rounds

Call two lost seeds a close pair if their restoration rounds differ by at most one. Their root groups use at most six marks in total, since their windows have a union of at most six rounds. In the following count let $n$, $v$, and $q$ be the total marks, visits and used guard charges of just these two groups. Their joint contribution $A=n-3v/2+3q/2$ is at most $9/2$.

- With neither root distinguished, $q=0$. One visit has at most three marks, and at least two visits use at most six marks in total.
- With one root distinguished, $q\leq2$. For $v\geq3$ the six-mark bound gives the claim. For $v=1$ the preceding per-root bound applies. For $v=2$, the root visit has one mark if neither side has further marks, at most three if one side does, and at most five if both sides do. The corresponding bounds on $q$ are two, one and zero. The other visit has at most three marks and the six-mark bound still applies. These bounds give at most $9/2$ in all three cases.
- With both roots distinguished, their rounds are consecutive. The step joining the two marks crosses between their visits. It uses at most one chosen guard edge, since a two-edge step has a single intermediate source and there is at most one chosen edge per source. Let $a$ be the number of root visits with marks on the side away from that step. Then $q\leq3-a$. For $v=2$ we have $n\leq2+2a$, which gives $A\leq7/2+a/2\leq9/2$. For $v=3$ and $a\geq1$ the six-mark bound suffices. For $v=3$ and $a=0$ the third visit has at most two marks, since a three-mark regular child visit would occupy its already used root round. Hence $n\leq4$. For $v\geq4$, use $n\leq6$ and $q\leq3$.

One close pair lowers $\sum_z A_z$ from at most $7k/2$ to at most $7k/2-5/2$. Thus $T\leq(3\beta+13k-1)/2$. If $\beta-k$ is odd, this equals $8k-2+3\lfloor(\beta-k+1)/2\rfloor$.

If $\beta-k$ is even, suppose that $T=(3\beta+13k-2)/2$, the integer upper bound just obtained. The allowances can lose at most half a mark. There must be $k$ direct-child visits of size three, every shared visit counted by $B$ must have size three, and no visit can be empty. A retained source that supplies a used guard can have only lost seeds and its own shared center as delayed white neighbors. The step using the guard cannot lead to the shared center, which has both sides inside its three-mark visit. Therefore each used guard lies on a step between two distinguished roots of a close pair.

There can be only one close pair. Two disjoint pairs would lower $\sum_z A_z$ by five from $7k/2$. If there are multiple close pairs and no two are disjoint, they either form a triangle or share one seed. There can be at most two leaves in the latter case, since the leaves have pairwise restoration gaps at least two and all lie within one round of the common seed. In either case all close pairs lie on just three seeds whose windows cover at most seven times. If their groups pay $q\geq1$ used guards, the $q$ steps between roots involve at least $q+1$ distinguished roots. Their contribution is at most $7-3(q+1)/2+3q/2=11/2$, a reduction of at least five from $7k/2$. If they pay no guards, one visit contributes at most $7/2$ and two or more contribute at most $7-3=4$, giving an even larger reduction. All of these reductions exceed the available three marks.

Only the unique close pair can pay a used guard. Its contribution must be at least four. With $Q=0$, a single visit contributes at most $7/2$ and two or more contribute at most $6-3=3$. Hence $Q=1$ and both roots are distinguished. With $v\geq3$ their contribution would again be at most three, so $v=2$ and $n=6$. Each root visit has three marks, including the root at the end facing the other root. Every other root has $Q_z=0$ and must contribute at least three, so it has exactly one visit with five marks. These root visits use every time in every root window. The only free old sides are on the step between the paired roots, whose two edges go through the retained source of an already counted shared center.

The rank inequality must also be tight, since losing one unit of $V+B-Q$ costs at least $3/2$ marks. If there are $s$ singleton visits left over from the counted groups, then $V+B-Q=2k+2B+s-1=\beta+k$. Since $\beta+k$ is even, $s$ is odd. The allowance permits at most one, so $s=1$. The union of $F$, the trail and the chosen guards is connected and already has rank $\beta$.

Let $y$ be the singleton mark. Its time lies outside all root windows and the three-round intervals of the counted direct and shared centers. If $y$ is old it must be an uncounted shared child. Its retained source has a spare guard to a lost seed besides its parent, distinct from the selected guards. It cannot be on the trail, since the sole free root sides use the source of a counted shared child. If $y$ is a second-round mark within one round of its parent, the parent must also be an uncounted shared child, with the same spare edge. Otherwise the preceding extra-edge argument supplies an edge for $y$. It cannot be used on the pair step, whose two edges belong to the intact source of a different target, or on any other step, because there is no other free old side or empty visit. In every case the extra edge lies outside the connected union and raises the rank. This contradiction gives $T\leq 8k-2+3\lfloor(\beta-k+1)/2\rfloor$ also when $\beta-k$ is even.

#### All seeds restored at least two rounds apart

Suppose the restoration rounds have pairwise gaps at least two. For a shared first-round child, let $r$ be the latest restoration round among the lost neighbors of its retained source. The child returns in $[r-1,r+1]$. If it returned by $r-2$, the source would restore the last lost neighbor by $r-1$, since all its other lost neighbors have already returned by $r-2$. Conversely, after round $r$ it can color the child in the next round. Group every shared rootless visit of size at least two with the root of latest restoration among its source's lost neighbors. The visit lies in that root's window $[r-2,r+2]$. Set aside the extra guard count for shared children.

Give every visit one mark of allowance. Each root group contributes $n_z-v_z\leq4$ above its allowance. A rootless direct-child visit of size at least two contributes at most two above its allowance, and there is at most one for each seed. Every other nonempty visit is a singleton. Let $h=\beta+k-V\geq0$ and let $E$ count empty visits. The upper bound is $T\leq\beta+7k+2$. Its deficit is exactly the sum of $h$, $E$, the root-group deficits $4-(n_z-v_z)$, and the direct-child deficits from a surplus of two per seed. A missing direct-child visit has deficit two. We show that the total deficit is at least one for $\beta\geq k+1$ and at least two for $\beta\geq k+4$.

If the deficit is zero, each root group has one five-mark visit distinguishing its root and using its full window. All $k$ direct-child visits have three marks using their centers' three-round intervals. All distinguished old vertices are internal to these visits. There are $\beta-k$ singleton visits. Their marks are outside the covered intervals and hence are second-round targets at distance at least two in arrival time from every old vertex. The extra-edge argument applies. All roots are visited, so the union of $F$ and the trail is connected and has rank at least $V-k=\beta-h$. There are no free old sides or empty visits and $h=0$, so even one singleton is impossible.

Now let $\beta\geq k+4$ and suppose the deficit is one. If $h=1$, all roots are distinguished. Otherwise $V=\beta+k$ and the trail must meet all $k$ subtrees, since meeting fewer would give rank at least $V-(k-1)>\beta$. The connected union of $F$ and the trail therefore admits at most $h$ more edges between its vertices. In each case below there are at least $\beta-k-1$ singleton marks outside the root windows and the direct centers' three-round intervals. They are second-round marks whose times differ from every old arrival by at least two. Their distinct extra edges can use the remaining rank or charge the available free old sides or empty visits.

- If $h=1$ or $E=1$, the root and direct-child visits are as in the zero-deficit case. There are $\beta-k-1$ singleton marks and no free old side. At most one extra edge can be accommodated.
- If one direct-child deficit is one, that visit has two marks and leaves one time uncovered in its three-round interval. The other direct-child visits and all root visits have their full sizes. There are $\beta-k$ singleton marks, of which at most one can use the uncovered time. The direct children are already distinguished and the root windows are full, so no singleton can be old. There is at most one free old side, at the two-mark direct-child visit.
- If one root-group deficit is one, that group has either one four-mark visit or two visits with five marks. With one visit there are $\beta-k$ singleton marks and just one uncovered time in the window. The four-mark visit has an internal root, so the gap is at $r-2$ or $r+2$, outside the old arrivals associated with this group. The other windows are full and all direct children are distinguished, so all singleton marks are second-round marks. This visit has at most one old endpoint. With two visits there are $\beta-k-1$ singleton marks and the window is full. If neither visit distinguishes the root, their sizes are two and three and they have at most one free old side together. If the rootless visit has three marks it has no free old side, and the two-mark root visit has at most two. In the remaining case the root visit has three marks. The root must be an endpoint, since a middle root would use $r-1,r,r+1$ and leave two nonconsecutive times for the two-mark rootless visit. A three-mark root visit with its root at an endpoint has at most one free old side, as does the two-mark rootless visit. There are therefore at most two free old sides in all cases.

In all cases the $\beta-k-1\geq3$ extra edges exceed the available rank, sides and empty visits. Thus $T\leq\beta+7k+1$ for $\beta\geq k+1$, and $T\leq\beta+7k$ for $\beta\geq k+4$ in this regime. For $\beta-k=1,2,3$ the first bound gives $8k+2,8k+3,8k+4$, respectively. For $\beta-k\geq4$ the second bound is at most $8k-2+3\lfloor(\beta-k+1)/2\rfloor$. Together with the close-pair bound this proves the formula.

### A construction from a pair of lost seeds

The construction works for every intact deadline $t\geq2$. Start with two blue seeds $z_1,z_2$ and $q\geq1$ initially white centers $w_i$. Each center has a separate blue source adjacent to $z_1,z_2,w_i$. Give each center two relay arms of length $t-1$. Join the exit of each center's right arm to the far left endpoint of the next, starting from a prefix path of $t$ edges with just its first vertex blue.

Give $z_1$ an approach arm of length $t$, and join its far endpoint to the last center's exit. Give $z_2$ a departure arm of length $t$. After this arm, use $k-2$ ordinary two-arm blocks of the low-rank construction for the other lost seeds. In the intact run the shared sources fill the centers in round one and their arms by round $t$. The other arms and the white prefix also fill in $t$ rounds.

Delete all $k$ designated seeds. While the shared sources are blocked by both lost seeds, the run traverses the two arms and the center of each block serially from left to right, taking $2t-1$ rounds per center. After the last center, the approach arm brings the run to $z_1$. The shared sources now restore $z_2$ in one round, since all centers are already blue. The departure arm and the remaining ordinary blocks fill in order. The delayed time is
$$
t+(2t-1)q+2t+2+(k-2)(2t+1).
$$

The prefix and the two seeds with their approach and departure arms start with $|E|-|V|=-3$. Adding a center, its arms and its source increases $|E|-|V|$ by one, counting the source's two edges to the existing seeds. Adding the $q+1$ links between the prefix, the centers and the approach arm gives $|E|-|V|=2q-2$ in a connected graph. Its rank is $2q-1$. The ordinary blocks add no rank.

Choose $b$ distinct lost seeds and give each one a detour. Its white center is adjacent to the seed and to a private white leaf. It carries two relay arms of length $t-1$. Insert the detours belonging to $z_1,z_2$ between the prefix and the first shared center. Insert any other detour just before the approach arm of its seed's ordinary block. Each insertion replaces one serial edge by two serial edges and an attached tree, raising the rank by one.

In the intact run a seed with a detour forces its center in round one, and by round two the center forces its leaf. The retained relays color the arms by round $t$. In the delayed run the leaf keeps the returned center from restoring its seed early. The run traverses the detour's two arms and center serially in $2t-1$ rounds. The leaf fills one round after the seed returns, in parallel with the return of $z_2$ or with the first departure vertex of its own seed. Thus the detours add $b(2t-1)$ rounds. Set $q=\lfloor(\beta-b+1)/2\rfloor$. An all-blue triangle attached by a bridge supplies the spare rank when $\beta-(2q-1+b)=1$. The [private-path protection](#protection-and-a-minimum-killing-support), with a path for $J$, preserves the rank and the two propagation times and gives a minimum killing support of size $k+1$. The degree is at most $\max(4,q+2)$ for this augmented family. Taking $t=2$ and $b=k$ attains the third line of the formula.

### All cycle ranks for three or more intact rounds

For $t\geq3$, $k\geq1$, and $\beta\geq0$, the largest finite recovery time on connected graphs of cycle rank $\beta$ with $k$ lost seeds and intact time at most $t$ is
$$
t+k(2t+1)+(2t-3)\beta+2\min(k,\beta).
$$
The examples recover from every loss of at most $k$ seeds and have a minimum killing support of size $k+1$. The same maximum holds under any degree cap $d\geq4$ with $\beta\leq k(d-2)$.

#### Upper bound from long visits

Put $a=2t-3$. Use the late propagation trail and its discrepancy forest $F$. As before, each forest edge in the rooted description is either a direct edge or a two-edge link through an unmarked relay.

A visit without the distinguished root that has more than $a$ distinguished marks must distinguish a child born in round one. Indeed, without a distinguished root the marks are confined to one branch. If its top child is undistinguished, the visit cannot pass through it from one descendant branch to another. The child would be an intermediate source with two distinguished neighbors downwards, both requiring direct intact forces. Therefore the marks lie in a single second-level branch. It has at most $2(t-2)+1=a$ marks on a path. If the top child is distinguished but born at round two or later, there are again at most $t-2$ further marked levels on each side, with the same bound. Call a rootless visit of size more than $a$ long. It has at most $a+2$ marks.

As in the [two-round count](#counting-the-visits-with-shared-first-round-sources), let $V$ count all visits to the subtrees of $F$ and $B$ the long visits whose distinguished first-round child has a shared retained source. Choose for each such visit an edge from its source to a lost neighbor other than its forest parent. These edges are distinct and outside $F$. The $Q$ chosen edges used by the trail pay for distinct free sides of distinguished lost roots. If the trail visits $v$ distinct subtrees, its union with $F$ has rank at least $V-v$ and $k-v+1$ components. At most $k-v$ unused edges can join components, giving
$$
\beta\geq V+B-Q-k.
$$

Allocate $a$ marks to every visit and an extra two to each of the $B$ shared visits. Long visits centered at direct first-round children contribute at most another $2k$ marks, since each lost root makes at most one intact force. Other long visits are centered at children born from retained sources with a unique lost neighbor. Assign them to that neighbor, along with the visit distinguishing that lost root if it is present.

For a particular root $z$, let $v_z$ and $n_z$ count its assigned visits and their marks, and $Q_z$ count chosen edges paid for by its free sides. If $r$ is the return time of $z$, its own visit has marks only within $r-t,\ldots,r+t$. Each of its assigned children returns within one round of $z$, and all marks in the visit around such a child arrive within $t-1$ rounds of the child. Thus $n_z\leq2t+1$. In all cases
$$
n_z-av_z+2Q_z\leq4.
$$

- If $z$ is undistinguished, then $Q_z=0$. A single assigned visit has at most $2t-1=a+2$ marks. Two or more use at most $2t+1$ marks in total.
- If the root visit has marks on both sides of $z$, then $Q_z=0$ and $n_z\leq a+4$.
- If the root visit has marks on one side, then $Q_z\leq1$. With one visit it has at most $t+1$ marks, giving a bound of $6-t$. With two or more the bound is $9-2t$.
- If the root visit has only its root mark, then $Q_z\leq2$. With one visit the bound is $8-2t$. With two, $n_z\leq1+(2t-1)$ gives $10-2t$. With at least three, $n_z\leq2t+1$ gives $14-4t$.

All of these bounds are at most four for $t\geq3$. Summing accounts for the $Q$ paid sides because $\sum_z Q_z=Q$. Since $a\geq3$ and $Q\leq B$,
$$
aV+2B=a(V+B-Q)+aQ-(a-2)B
\leq a(V+B-Q)+2Q .
$$
After the contributions of the direct visits and the assigned visits, the total bound is
$$
T-t\leq a(V+B-Q)+2k+4k
\leq a\beta+(2t+3)k.
$$
Taking the smaller of this bound and the original trail bound $T\leq t+k(2t+1)+(2t-1)\beta$ gives the stated formula.

#### Matching construction

Use the common prefix and the original two-arm block for each lost seed $z$. Give $\min(k,\beta)$ blocks the earlier first-round detour through a white vertex directly adjacent to $z$, with its two arms of length $t-1$ and its white leaf. Use one unit of rank for each such detour. Distribute the remaining $\beta-\min(k,\beta)$ units among those same blocks using detours born in the second round, as follows.

A new detour starts with a retained blue relay from $z$ to an initially white vertex $u$. Join $u$ directly to a white center $w$. Attach two white arms of length $t-2$ to $w$ using the usual blue relays, and attach a white leaf $g$ directly to $w$. In the intact run $u$ arrives in round one, $w$ in round two, and $g$ in round three. The far endpoints of both arms arrive at $t$.

In the block's delayed order, traverse all second-round detours first, followed by its first-round detour and the original two arms at $z$. Join the preceding endpoint to the first entry, and join each detour's exit to the next entry or to the original left arm at $z$. Every detour adds one unit of rank because its vertices are already attached to the tree at $z$, and the chain uses one extra edge per detour. In the intact run these joining edges connect endpoints that only turn blue at $t$, so the arms propagate from their centers as prescribed.

During the designated loss, a second-round detour fills along its incoming arm, then its center $w$, then its outgoing arm. It takes $2t-3$ rounds. The vertex $w$ stays blocked by $u$ and $g$ until $z$ returns. The first-round detour similarly adds $2t-1$ rounds. When $z$ returns, all the vertices $u$ and the first-round detour's leaf fill one round later. The leaves $g$ fill two rounds after $z$, in parallel with its original right arm. Hence these side arrivals add no further rounds.

With $j$ second-round detours in a block that has a first-round detour, the degree of $z$ is $3+j$. Every other vertex has degree at most four after the [private-path protection](#protection-and-a-minimum-killing-support) with $J$ a path. This protection preserves the rank and arrival times. For $\beta\leq k(d-2)$ the second-round detours can be distributed with $j\leq d-3$ in every block, giving the asserted degree cap. Unrestricted degree allows the construction at every rank.

### Three or more intact rounds at degree three

On a connected graph of maximum degree at most three and cycle rank $\beta$, every finite recovery from a $k$-seed loss with intact deadline $t\geq3$ satisfies
$$
T\leq t+k(2t+1)+(2t-3)\beta.
$$
This is the exact maximum for $0\leq\beta\leq k$, and the inequality is strict for $\beta>k$. When $t\geq4$ and $\beta>k$, the bound drops by at least two rounds. In particular, at $\beta=k+1$ the exact maximum for $t\geq4$ is
$$
t+k(2t+1)+(2t-3)k+(2t-5).
$$
The sharp examples recover from every loss of at most $k$ seeds and have a minimum killing support of size $k+1$.

#### Counting long visits at degree three

Set $a=2t-3$ and use the [discrepancy forest and late trail](#upper-bound-from-long-visits). A rootless visit with more than $a$ marks has a distinguished first-round center, with at most $t-1$ marks on either side of it. Since $a\geq t$, such a visit has marks on both sides. It uses both of the center's child incidences, because the parent incidence leaves room for at most two child incidences at degree three. The branch cannot also supply a mark to the root visit: that visit cannot mark the center again, and reaching a descendant would reuse a child edge. Consequently the root incidence associated with a long visit is distinct from all incidences of branches that supply marks to the root visit.

Let $p$ count the distinguished roots, $V$ all visits to the forest, and $\ell_z$ the number of marks in the visit distinguishing root $z$, or zero if there is no such visit. Retain the shared-guard count $V+B-Q\leq k+\beta$. Assign an allowance of $a$ marks to each rootless visit. Charge its excess, at most two, to the root incidence for the first-round center if the center is direct or has a retained source with one lost neighbor. For a shared long visit whose guard is unused, the rank allowance pays $a$ marks and covers its excess. If its guard is used, the trail step using it must connect the two lost neighbors of the shared source. Both sides of the center are already used inside the long visit. A one-mark excess is charged to the root incident to the guard. A two-mark excess is split between the two roots. Each shared charge uses one incidence outside that root's marked branches, and different shared sources use different incidences.

We bound these charges at each root by $2t+1-\ell_z$ when $\ell_z>0$, and by four when $\ell_z=0$. A long center with a single-neighbor retained source is within one round of its root, so its visit fits in the root's $2t+1$-round window. A direct long center cannot precede its root by two or more rounds. A nonfinal mark on a subcubic trail has at most one white neighbor just after it arrives, as otherwise its sole blue neighbor has already spent its force restoring it and the trail cannot continue. The direct center would need both its lost root and another white neighbor to avoid restoring the root early. If the direct center is late by at least two rounds, its root must still have another white lost neighbor when it returns. This reserves a separate incidence at the root.

- If $\ell_z$ is $2t$ or $2t+1$, the root visit uses two branches and has no free side at the root. A direct long center at the remaining incidence cannot be late, because the two other neighbors of the root are retained sources. The root marks and a long visit near the root would overfill its window. Shared used guards require free root sides, so this root has no charges.
- At $\ell_z=2t-1$, there are two marked branches and at most two units on the remaining incidence. At $\ell_z=2t-2$, the same reasoning applies if there are two branches. If there is just one, then $t=3$ since a one-sided visit has at most $t+1$ marks. Two available incidences cannot each charge two units. Both would have to be direct or single-neighbor visits of size $2t-1$, which cannot both fit in one window. A late direct center would reserve yet another incidence. Thus at most three units are charged in this case.
- If $2\leq\ell_z\leq2t-3$, the root visit uses at least one branch and the other incidences carry at most four units. If $\ell_z=1$, all three incidences together charge at most six units, within its allowance of $2t$.
- An undistinguished root cannot be an endpoint of a used shared step. It has at most one direct center and at most one long single-neighbor visit, since two such visits would require at least $4t-4>2t+1$ distinct times in its window. Thus at most four units are charged to it.

The sum of these allowances and the root marks is $(2t+1)p+4(k-p)$. After paying the unused shared guards and the individual charges, the remaining contribution is at most $a(V+B-Q-p)$. Therefore
$$
T-t\leq (2t+1)p+4(k-p)+a(k+\beta-p)
=k(2t+1)+a\beta.
$$

#### When the subcubic bound is attained

Suppose the bound is attained. Each root must use its entire allowance. A visit of length $2t$ uses no units, and one of length $2t-1$ cannot charge two units to its one remaining incidence: a local long visit at that incidence is near the root and would overfill its window. At length $2t-2$ with two branches there are at most two units. In the one-branch case at $t=3$, obtaining three units would require a two-unit local long visit. A near one would overfill the window, and a late direct one would reserve the last incidence for its still-white lost neighbor, leaving no third unit. Among lengths from two through $2t-3$, only $2t-3$ could attain the allowance with four units. This would require two full local long visits, which cannot both be near, or both use distinct child incidences besides the branch and the late direct child's extra lost edge. Length one cannot attain six units when $t=3$, since at most one long single-neighbor visit and one direct long visit are possible, and a shared source supplies at most one unit. For larger $t$, the allowance is greater than six.

An undistinguished root could attain four units only with one full direct long visit and one full single-neighbor visit. The direct center would have to be late, and the root would use its three incidences on that center, its other still-white lost neighbor, and the retained source of the single-neighbor visit. The edge to the lost neighbor is outside the forest and the shared guards. At saturation the union of those guards, the trail, and the forest has rank $\beta$ and is connected: equality in the rank count requires joining all forest subtrees missed by the trail. Thus the edge must be used on the trail. The undistinguished root would have to act as an intermediate source between its lost neighbor and its direct center, since its third neighbor is retained. The center already uses both sides of its long visit. This excludes the undistinguished case, so every root visit is full.

No used guard can meet a full root, and unused shared long visits would lose at least $a-2>0$ in the count. Thus there are no long rootless visits, and at equality each rootless visit has $a$ marks. The full root windows are disjoint. Regular and shared first-round children are within one round of a root, since distinct full roots' returns are at least $2t+1$ rounds apart. A distinguished direct first-round child outside a full root visit likewise has its root's other two incidences used by retained branches and arrives within one round of it. Therefore no first-round child is distinguished outside the full visits. The same branch argument as for long visits now puts each remaining visit in a second-level branch, with a distinguished center born in round two, and $t-2$ marks on either side of it. All distinguished old vertices, meaning roots and first-round births, have both sides inside full root visits.

For a second-round center $y$ with an indirect parent $w$, an arrival gap of at least two would require another old neighbor of its intact source. This extra edge is outside the forest. It cannot lie on the trail because its source is already blue by delayed round one and the old endpoint would need a free side. Rank saturation rules it out. Thus $y$ is within one round of $w$. A center forced directly by a lost root cannot be far from it. The two full branches of that root use initially blue retained sources, leaving the direct center as its only possible white neighbor after the root returns. An early center cannot postpone the root by two rounds by the subcubic trail constraint. For a direct center with a first-round parent $w$, the same constraint excludes a gap of at least two with the center arriving first. If it arrives at least two later, another old neighbor of $w$ must be white when $w$ returns. The only such forest edge could go to its lost root $z$ if $w$ is the direct child of $z$. If this is the only blocker, the center and $z$ return within one round of each other. Any extra old-to-old blocker edge outside the forest would have to use a free old side on the trail. Thus every remaining center is within one round of its parent, except for the direct centers already excluded by their proximity to a lost root.

If the parent $w$ is within one round of a lost root, the center is within two rounds of that root and all $a$ marks lie in its full window. The parent must therefore be an undistinguished early direct first-round child of a root $z$. That root has its other two branches full, so $w$ can only be far before it. The center is also early: otherwise its own arrival would lie in the full window. If the center is direct from $w$, then $w$ needs another white neighbor after both have returned to avoid restoring $z$ early. This guard edge is outside the forest, since any other forest neighbor of $w$ is a relay blue by delayed round one. On the trail the edge would use the undistinguished $w$ as an intermediate source, and its other edge would go to $z$ or to the center. The root visit at $z$ uses other branches, and the center already uses both sides inside its rootless visit. The edge cannot occur at rank saturation. Thus the center is indirect. The early parent $w$ has at most one relay to such a center, since it needs two other incidences to its lost root and to its guard. There are at most $k$ such parents. At equality the $\beta$ extra visits therefore require $\beta\leq k$.

#### One round below the bound for four or more intact rounds

Suppose $t\geq4$ and $T$ is at most one round below the linear bound. In the long-visit count, a unit of slack in $V+B-Q\leq k+\beta$ would lose $a=2t-3\geq5$ marks, and an unused shared long visit would lose at least $a-2\geq3$. Thus the rank count is tight and every shared long guard would have to be used. Every root allowance has deficit at most one. The total deficit, including short rootless visits, is at most one.

A marked root of size one cannot come within one unit of its allowance $2t$, since its incidences carry at most six units. A root visit of size two uses one branch, so at most four units are available against an allowance of $2t-1$. If a visit uses one branch and has at least three marks, it receives at most two units. Indeed, a two-unit charge would require a long local visit of size $2t-1$. A near one would overfill the root's window, and a late direct one would reserve the last incidence for its still-white lost neighbor. Otherwise each of the two available incidences charges at most one unit. This is at least two below the allowance, since a one-sided visit has at most $t+1$ marks. For a root visit with two marked branches, any local long visit at the remaining incidence must be near: there is no room for the blocker of a late direct center. A two-branch visit of size at least four therefore has no units, since a near long visit has at least $2t-2$ marks and would overfill its window. Shared paid guards cannot be used at a two-branch root. A two-branch visit of size three receives at most two units, still more than one below its allowance. Thus every distinguished root has size $2t$ or $2t+1$.

An undistinguished root would need at least three units and therefore both a direct and a single-neighbor long visit. These cannot both be near, so the direct center is late. The additional edge to a still-white lost neighbor must be on the trail at rank saturation. As in the equality argument, the undistinguished root would have to be a delayed source in a step between its direct center and that lost neighbor. The direct center has no free side. Thus all roots are distinguished, and there are no shared long guards or other charges. All root visits are full except for at most one of size $2t$, and every rootless visit has size $a$ or $a-1$. A size-$2t$ root visit misses just one time at distance $t$ from that root. Both sides still have at least $t-1$ marks, so every distinguished old vertex has both sides inside its visit.

The root windows prevent any first-round child from being distinguished in a rootless visit. Two roots cannot restore within one round of each other, since their visits use at least $2t$ times each. This keeps every shared first-round arrival within one round of the later root. A distinguished direct first-round child is also near: if its branch supplies a mark to its root visit, it acts there as an intermediate source and arrives before the root. Otherwise the two other branch incidences use retained neighbors. The subcubic trail constraint bounds how early the child can be. The only missing time in a nonfull root window is too far away for any of these first-round marks.

It follows that every rootless visit is within a second-level branch and distinguishes a center born in round two. A later-born center or a single deeper branch can account for at most $a-2$ marks, and a one-sided path at a second-round center has at most $t-1<a-1$ marks. Thus each center uses both sides inside its visit. The blocking-edge argument from equality applies with the same absence of free old sides. In particular, a direct second-round center cannot be far from its lost root. If the root is nonfull, it uses two other branches, whose retained relays are blue by delayed round one because the center was its only white neighbor at intact time one. An indirect center must be near its old parent, or its extra blocker edge would be outside the rank-saturated union. A direct center with an old first-round parent likewise needs an extra edge to explain a gap of two or more, unless the center is itself near the parent's lost root. Proximity to one of these roots cannot occur: it puts the marked center within two rounds of the root, away from the missing time at distance $t$. Therefore the only possible parents of the rootless centers are undistinguished early direct first-round children. A direct center at such a parent still needs the extra edge to its parent's white guard; the step using that edge cannot use either the lost root or the center, which have no free side. Each parent thus supplies at most one indirect center through its sole remaining relay incidence. The $\beta$ rootless visits require at least $\beta$ such parents, giving $\beta\leq k$. This proves the two-round drop when $\beta>k$.

#### Construction through a second-round center

Use the common $t$-edge prefix and ordinary two-arm blocks. To place one unit of rank in a block, add a white vertex $w$ adjacent to its lost root $z$, a white leaf $g$ at $w$, and a blue relay linking $w$ to a white center $u$. Give $u$ two arms of length $t-2$. Replace the edge entering the main left arm at $z$ by an edge into this detour and an edge from the detour exit into the main arm. Only $z,w,u$ have degree three in the modification. In the intact run $w$ fills in round one and $u,g$ in round two. The detour arm ends fill by $t$, as do the main arm ends and the prefix.

After the designated loss, the run traverses the detour arms and their center in $2t-3$ rounds. When $u$ returns, the relay restores $w$ alongside the next mark. The vertex $w$ stays blocked by $z$ and $g$ until the main approach arm reaches $z$. Then $g$ returns in parallel with the first departure vertex. The detour thus adds exactly $2t-3$ rounds and one unit of rank. For $0\leq\beta\leq k$, use $\beta$ detours and $k-\beta$ ordinary blocks. All retained blue vertices have degree at most two before protection. The [degree-three private paths and path support](#a-cycle-rank-bound-at-degree-three) preserve the degree cap, rank and both designated times. At $\beta>k$, use all $k$ detours and pad with all-blue cycles as in the [two-round construction](#attaining-the-bounds), obtaining $t+k(2t+1)+(2t-3)k$ rounds at every such rank. The same detour with zero arm length at $t=2$ is the earlier degree-three rank-one block.

#### Recursive detours at higher ranks

The same detour can attach to an interior arm vertex or to a detour's white guard. Use each attachment vertex at most once. If it has intact arrival round $i\leq t-2$, its new detour has a center and a guard born at $i+2$, with two arms of length $t-i-2$ at the center. Every serial path still has endpoints at intact time $t$. Put all detour paths of a block in order of decreasing attachment depth $i$, followed by its main path. Link each exit directly to the next entry. A detour now always precedes the serial path containing its attachment vertex, or the path associated with the earlier guard from which that attachment vertex will be restored. The new connection contributes one unit of rank.

The intact run colors each added parent one round after its attachment vertex, and its guard and center one round later. The joining edges have both endpoints white through time $t-1$. In the delayed run, each detour center restores its own parent one round after the serial path reaches it, and that parent waits for its attachment vertex before restoring its guard. This schedule follows by induction along the serial paths. An upcoming detour cannot start from its attachment vertex, which is still white, or through its white guard. Its guard, even when it is an attachment vertex of a deeper detour, stays white until its own scheduled release: the deeper parent sees that guard and its own guard white. On arrival, a serial exit has only its next entry white among its neighbors. This starts the next path one round later. Guards along any chain of attachments return one per round after the serial vertex on which the chain starts. Their intact depths each increase by two, and the starting serial vertex at depth $i$ has at least $t-i$ serial rounds remaining in its path. Thus these guard releases do not prolong the serial time. Each detour adds exactly $2t-2i-3$ rounds at its rank cost of one. The degree-three protection still applies, since all additional retained sources have degree two.

Use the smallest available attachment depth until the rank is spent or all possible attachments are used. Let $H_i$ be the number of attachment sites at depth $i$ when all shallower sites have been used, for $0\leq i\leq t-2$. The main blocks provide $k$ sites at depth zero and $2k$ sites at each positive eligible depth. Every detour attached at $j$ creates one guard site at $j+2$ and two arm sites at each eligible depth from $j+3$ on. Consequently
$$
H_0=k,\qquad H_1=2k,\qquad H_2=3k,\qquad
H_i=H_{i-1}+H_{i-2}+H_{i-3}\quad(i\geq3),
$$
using only terms through $t-2$. With $b_i=\min\{H_i,\max(0,\beta-\sum_{j<i}H_j)\}$, the designated time is
$$
t+k(2t+1)+\sum_{i=0}^{t-2}(2t-2i-3)b_i.
$$
Any unused rank is supplied by all-blue cycles. At $\beta=k+1$ the last detour is at depth one, adding $2t-5$ rounds beyond the rank-$k$ extremum. This attains the improved upper bound for $t\geq4$ and is within one round of the upper bound for $t=3$.

<a id="one-intact-round-at-small-cycle-rank"></a>

### Exact one-round values by cycle rank

Let $\mathcal{M}_{\beta,k}$ be the maximum finite delayed time over connected graphs of cycle rank $\beta$ whose intact run finishes by round one, after exactly $k$ seed losses. For $k\geq1$ and $\beta\geq0$,
$$
\mathcal{M}_{\beta,k}=1+3k+
\begin{cases}
\min\{1,\lfloor\beta/2\rfloor\}, & k=1,\\[2pt]
\max\{\min(k,\lfloor\beta/2\rfloor),\lfloor(\beta-3)/2\rfloor\}, & k\geq2 .
\end{cases}
$$
The upper bound applies to arbitrary graphs with total cycle rank $\beta$. The connected examples attaining it are $k$-fault-tolerant and have a minimum killing support of size $k+1$.

#### Counting extra arrivals

Assume the delay runs past round one. Use the discrepancy forest $F$ and the trail ending at round two from the preceding proof. For a round-one discrepancy with a retained intact source, choose as parent the lost neighbor that returns last, breaking ties arbitrarily. Every marked nonroot is a leaf of a subtree of $F$. Write $\tau(v)$ for the delayed arrival of a vertex $v$.

A visit distinguishing its root $z$ can distinguish at most one child on each side of $z$, and any such child arrives at $\tau(z)-1$ or $\tau(z)+1$. Give this root a deficit of two minus the number of those children. Each root not distinguished has deficit three. Let $D$ be the total deficit, and $m$ the number of roots not distinguished. An extra is a distinguished child outside its root's distinguished visit, or any distinguished child of a root not distinguished. Each extra occupies a visit with exactly one distinguished vertex. If there are $e$ extras, then
$$
T-1=3k-D+e.
$$

Call an extra near if its arrival differs from its root's by at most one. A distinguished root has the two adjacent arrival slots, less the ones used in its own visit. A root not distinguished has at most three such slots including its own round. Thus the number $N$ of near extras is at most $D$. Also, a distinguished root has at most its deficit in free sides, the sides of its visit with no distinguished child. Across distinguished roots there are $D-3m$ free sides.

Each far extra $y$ with parent $z$ needs a blocking edge outside $F$.

- If its intact source $p$ is retained, $p$ would force the later of $y,z$ by one round after the earlier unless another lost seed $z'$ were still white. Choose the edge $pz'$.
- If $y$ is a direct child that arrives after $z$, choose an edge $zz'$ to a different lost seed white when $z$ returns. Such a seed must exist because $y$ is the only initially white neighbor of $z$.
- If $y$ is a direct child that arrives before $z$, choose an edge $yg$ to a neighbor $g\ne z$ still white when $y$ arrives. Otherwise $y$ would force $z$ at the next round.

These edges are distinct within and across the three cases. An edge of the first type identifies its retained source, which is chosen for only one child. An edge of the second type identifies the earlier of two lost seeds, which has only one direct child. An edge of the third type identifies its owner as the earlier endpoint, the initially white direct child. The first type joins a retained source and a lost seed, the second joins two lost seeds, and the third joins an initially white vertex to a vertex still white after round one. Every chosen edge has both endpoints in $F$.

#### Charging blocking edges

Let $R$ count repeated vertex occurrences in the contracted trail, $v_0$ count visits to subtrees without a distinguished vertex, and $u$ count subtrees never visited. The number of visits to subtrees is $k-m+e+v_0$, so
$$
R\geq e+v_0-m+u .
$$
If $U$ chosen blocking edges are unused by the trail, add them to the union of $F$ and the trail. That union has cycle rank $R$ and $u+1$ components. At most $u$ added edges can join components. Consequently $\beta\geq R+U-u$.

A chosen edge on the trail can be assigned to a free side of a distinguished root or to a visit counted in $v_0$. An edge $pz'$ is used at the distinguished occurrence of $z'$ because $p$ was never white in the delayed run. An edge $zz'$ is used at the distinguished occurrence of at least one of its endpoints. In either case the edge immediately leaves that root's visit on the corresponding side. For an edge $yg$ of an early direct child, the trail cannot use it with $y$ distinguished. The later-arriving $g$ cannot be an intermediate source adjacent to that distinguished occurrence, and $y$ cannot force $g$ while $z$ is white. Hence $y$ is an intermediate source on that step, between two distinguished vertices. If the other edge of the step is its sole forest edge $yz$, charge the side of the distinguished $z$ ending at $y$. There is no distinguished child on that side because $y$ is a leaf. Otherwise both edges of the step are outside $F$, and this occurrence of $y$ gives a visit with no distinguished vertex.

The assigned free sides are distinct because each is identified by its boundary edge on the trail. The assigned visits with no distinguished vertex are distinct because each is a single intermediate occurrence with both incident edges outside $F$. Let $C$ count the free-side charges. Then $C\leq D-3m$ and $e\leq N+C+v_0+U$. Write $A=D-N$ and $B=D-3m-C$ for the two unused allowances. Combining the counts, with $S=T-1-3k=e-D$, gives
$$
\beta\geq 2S+2m+A+B .
$$

#### The extra cost beyond one far arrival per seed

The preceding inequality gives $S\leq\lfloor\beta/2\rfloor$. If $S>k$, there are more than $k$ far extras because $N\leq D$. At most $k$ can be direct children, so some far extra has a retained intact source $p$. This is impossible with only one lost seed. In general, with the latest lost neighbor chosen as its root, this extra cannot be late. Once all lost neighbors are blue, $p$ can force it in the next round. It must therefore be blue at least two rounds before the last lost neighbor of $p$. The two latest lost neighbors of $p$ have arrival times equal or one apart. Otherwise $p$ would force the last one before its recorded arrival.

If $m\geq2$, the inequality already gives $\beta\geq2S+4$. If $m=1$, at least one of these two neighbors is distinguished. When exactly one is distinguished, its arrival takes one of the three slots for near extras of the other, giving $A\geq1$. When both are distinguished their times are consecutive, and each occupies a near slot of the other, giving $A\geq2$. Thus $\beta\geq2S+3$ in this case.

If $m=0$, both lost neighbors are distinguished and arrive in consecutive rounds. They occupy each other's near slots, so $A\geq2$. Their two chronological sides facing each other are free. At most one selected blocking edge can be charged to these two sides. A direct trail step between the roots uses only one edge. For a step through an intermediate vertex, both sides can use only the edges of that step. If the intermediate vertex is a retained seed, at most one of the two edges was selected for its single intact target. If it is an initially white vertex, at most one was selected for it as an early direct child. If it is a lost seed, it is earlier than both distinguished roots. Any selected blocking edge there would have to be owned by that intermediate seed as the parent of a late direct child, so again at most one is selected. Consequently $B\geq1$ and $\beta\geq2S+3$.

Thus $S>k$ requires $k\geq2$ and $S\leq\lfloor(\beta-3)/2\rfloor$. Together with the restriction $S\leq\lfloor\beta/2\rfloor$ for all $S$, this proves the stated upper bound.

#### Attainment at every cycle rank

Begin with a blue seed and its white neighbor, which fills in round one. Join successive blocks by an edge or a blue relay from the previous exit. A path block with previous exit $P$ is the path $P,a,z,p,b$. Initially $z,p$ are blue and $a,b$ are white. Its delayed additions after $P$ are $a,z,b$ when $z$ is lost. A rank-two block uses vertices $a,b,c,z,p,q,u$ and edges $Pa,az,ab,au,bu,zp,bp,zq,cq$. Its initial blue vertices are $z,p,q,u$. After $P$, losing $z$ gives successive additions $a,b,z,c$. In particular $u$ forces $b$ after $a$, $p$ can then restore $z$, and $q$ forces $c$. In the intact run both types finish in the first round.

With $s$ rank-two blocks and $k-s$ path blocks, the designated time is $1+3k+s$ and the graph has cycle rank $2s$. Taking $s=\min(k,\lfloor\beta/2\rfloor)$ attains the first term. Extra rank can be added without changing any arrival in the two runs, by attaching a chain of all-blue triangles to the shared seed using bridges.

For $k\geq2$ and $s=\lfloor(\beta-3)/2\rfloor>k$, use $k-2$ rank-two blocks and one [two-seed block from the degree-bounded construction](#constructions-attaining-the-bounds) with $q=s-k+2$ shared-source targets. After its incoming endpoint, it fills $q$ pair targets, two direct children, an entry target, the two lost seeds and the exit target, in that order and one per round. It contributes $q+6$ rounds. Including the incoming relays but excluding the incoming endpoint, the block contributes $3q+11$ vertices and $5q+14$ edges, hence $2q+3$ to cycle rank. The assembled graph has cycle rank $2s+3$, to which one all-blue triangle can be added for even $\beta$. The designated time is $1+3k+s$.

Use [seed protection](#protection-and-a-minimum-killing-support) with a path for $J$ in both constructions. Its added graph is a tree attached by a bridge, preserving cycle rank and the designated delay. It gives recovery from every loss of at most $k$ seeds and a minimum killing support of size $k+1$.

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

With just one loss the [general upper bound](ONE_LOSS_TIMING.md#upper-bounds) is five. A single block of size one attains it for every maximum degree cap at least four.

### Maximum degree at most three

At degree one a recoverable loss deletes at most one seed from each edge and no seed from an isolated vertex. Every missing seed returns in one round. A disjoint union of $k$ blue edges attains this time.

For degree at most three, use the same groups of seed restoration times as above. In every round after the first that restores no seed, choose a target with a retained intact source if one is available. A single-neighbor target or a long shared-source target uses a boundary slot of its group and one incidence at the corresponding seed. A short shared-source target uses two incidences in one group, at its latest two neighbors.

It remains to choose a target in a round $j$ whose additions all have direct intact sources. At least one such target $x$ either arrives within one round of its lost source or arrives after that source was restored. Otherwise every addition $x$ would still have its source white in round $j+1$. Choose a delayed source $p$ that forces $x$ in round $j$. The vertex $x$ must see at least two white neighbors after round $j$: its lost source and one other, since otherwise it would restore that seed next. With degree at most three, $p$ is the only blue neighbor of $x$. The source $p$ has used its force, and $x$ cannot force either white neighbor. A newly enabled force in round $j+1$ must come from one of the new blue vertices or a blue neighbor of one. Neither can cause an addition here, so the run would stall with a seed still white.

If the chosen direct target arrives within one round of its source, use the boundary slot of that source's group and one incidence. Otherwise its source was blue by round $j-2$. This source has a lost neighbor still white at round $j-2$, since its only originally white neighbor is $x$ and it would otherwise have forced $x$ by round $j-1$. Charge two incidences in the source's group: the direct edge and the edge to that lost neighbor. The latter is between two lost seeds and cannot be charged as an edge to a direct target or to a retained source. A seed supplies this extra incidence at most once, since it has at most one direct target in the intact run.

Thus each group of $p$ seeds can spend up to two boundary slots at one incidence each, and every other assigned target costs two incidences in the group. The group has at most $3p$ incidences. It can account for at most $\lfloor3p/2\rfloor+1\leq2p$ targets if $p\geq2$, or at most two if $p=1$. There are at most $2k$ selected target rounds and at most $k$ seed-restoration rounds, giving $M_{3,1,k}\leq1+3k$. The degree-two path construction attains equality at both caps.

## One intact round with both degree and cycle rank fixed

Let $M(d,\beta,k)$ be the maximum finite recovery time on connected graphs of maximum degree at most $d$ and cycle rank exactly $\beta$, with intact time at most one and exactly $k\geq1$ losses. For every $\beta\geq0$,
$$
M(3,\beta,k)=1+3k,\qquad
M(4,\beta,k)=1+3k+\min(k,\lfloor\beta/2\rfloor).
$$
For $d\geq5$ and $\beta<2k$, the exact value is $1+3k+\lfloor\beta/2\rfloor$. For $d\geq5$ and $\beta\geq2k$, put $\ell=d-4$, $n=\lfloor k/2\rfloor$, and $P=\ell n$. Define $D=P$ except for odd $k\geq3$ and $d\geq9$, when $D=P+\lfloor(\ell-3)/2\rfloor$. Write $\beta-2k=(2\ell+3)a+b$ with $0\leq b<2\ell+3$. Then the exact value is
$$
\begin{aligned}
E_{\mathrm{pair}}&=\min\{P,\ \ell a+\max(0,\lfloor(b-3)/2\rfloor)\},\\
E_{\mathrm{triple}}&=\min\{D,\ \lfloor(\beta-2k-3n-5)/2\rfloor\},\\
M(d,\beta,k)&=1+4k+\max\{E_{\mathrm{pair}},E_{\mathrm{triple}}\}.
\end{aligned}
$$
The triple term can exceed the pair term only when it exceeds $P$. If the gain is positive and at most $P$, its least rank is $2k+2e+3\lceil e/\ell\rceil$. For $P<e\leq D$ the least rank is $2k+2e+3n+5$. All maxima have connected $k$-fault-tolerant witnesses with a minimum killing support of size $k+1$.

### Rank spent by groups of lost seeds

Let $T>1$ be a finite delayed time, and put $S=T-1-3k$. Group all lost seeds by consecutive restoration rounds, including seeds that return in the same round. The trail argument gives $\beta\geq2S+2m+A+B$, where $m$ counts undistinguished roots and $A,B$ count unused near slots and free trail sides.

Consider a group of $p$ seeds restored over $r$ distinct consecutive rounds. Write $t_*$ for the number distinguished by the trail and $j$ for the number of distinguished children in their roots' distinguished visits. The group's deficit is $2t_*+3(p-t_*)-j=3p-t_*-j$. Every distinguished child in a root visit and every near extra in the group sits within its $r$ restoration rounds or one of the two boundary rounds. The $t_*$ distinguished roots also occupy distinct times in that same window. Thus the number of near extras in the group is at most $r+2-t_*-j$, and the group contributes at least $3p-r-2$ to $A$.

Among the $r$ times, mark the $t_*$ times of distinguished roots. At most $r-t_*+1$ consecutive runs of marked times are possible, so there are at least $2t_*-r-1$ pairs of consecutive marked times. For each such pair the two free trail sides facing each other can receive at most one blocking-edge charge, by the step count in the [cycle-rank proof](#the-extra-cost-beyond-one-far-arrival-per-seed). The sides of different pairs are distinct, including when a distinguished root is in two pairs. The group therefore contributes at least $2t_*-r-1$ to $B$. With the $2(p-t_*)$ units from undistinguished roots, its total contribution is at least
$$
w=5p-2r-3=3(p-1)+2(p-r).
$$
Consequently $\beta\geq2S+\sum w$ over all restoration groups. The degree-three and degree-four upper bounds follow from their separate degree bounds and the cycle-rank bound. The trail bound $S\leq\lfloor\beta/2\rfloor$ also gives the upper bound for $\beta<2k$ at all higher degrees.

### Degree spent within each restoration group

For each round after one that restores no lost seed, select one arriving vertex and one intact source as in the degree count. Assign a direct target to its lost source's group. A single-neighbor or long shared-source target uses a boundary slot of the group of its latest lost neighbor. A short shared-source target uses two incidences in the group containing its two latest lost neighbors, whose returns are equal or consecutive.

In a group of $p$ seeds and $r$ distinct restoration rounds, let $a,b,q$ be the numbers of direct, boundary-slot and short shared-source targets. The counted incidences at the lost seeds are distinct, giving
$$
a\leq p,\qquad b\leq2,\qquad a+b+2q\leq dp.
$$
The group accounts for at most $r+a+b+q$ rounds. Their sum covers all rounds after one. A singleton has no short targets and accounts for at most four rounds. For $p\geq2$, the contribution above $4p$ is at most
$$
r-p+\left\lfloor\frac{(d-5)p}{2}\right\rfloor+1.
$$

Give each group an integer $u$ defined by $u=\lfloor p/2\rfloor$, except when $p$ is odd and $r<p$, when $u=\lceil p/2\rceil$. The degree contribution above $4p$ is at most $\ell u$. For even $p$, this follows directly from the last bound. For odd $p$ with distinct return times, take the seeds in even positions in their consecutive order. They meet every consecutive pair, so every short target uses an incidence at one of these seeds and $q\leq d(p-1)/2$. The resulting gain is at most $\ell(p-1)/2$. For odd $p$ with ties, the last incidence bound gives a gain of at most $\lfloor(d-5)p/2\rfloor\leq\ell\lceil p/2\rceil$.

The rank cost satisfies $w\geq3u$ in every group. If $p$ is odd and $r<p$, then $p\geq3$ and $w\geq3(p-1)+2\geq3u+2$. With $e=T-1-4k$ positive, the degree bound gives $e\leq\ell\sum u$. In every case, $\beta-2k\geq2e+3\lceil e/\ell\rceil$. If $e>P$, at least one odd group has a tied return, because otherwise $\sum u=\sum\lfloor p/2\rfloor\leq n$. Hence in this case $\sum w\geq3(n+1)+2$, so $\beta-2k\geq2e+3n+5$. The [separate degree bound](#exact-values-for-one-intact-round) gives $e\leq D$. These inequalities give the stated upper bound.

### Sharp constructions

For degree three, start with the extremal path for intact time one. Attach cycles using bridges in a chain at a retained seed of the last blue pair. In each cycle the two vertices used as ports are adjacent, and the other route between them has $2k+2$ interior vertices, all initially blue along with the ports. Every loss of at most $k$ leaves two consecutive interior vertices blue. They restore the entire route and its ports without help from outside the cycle. The designated loss and killing support leave the attachment seed blue, preserving their outcomes on the path. Each cycle adds one to the rank while keeping maximum degree at most three.

At degree four, use $\min(k,\lfloor\beta/2\rfloor)$ rank-two blocks from the [cycle-rank construction](#attainment-at-every-cycle-rank), with path blocks for the remaining seeds. Use the same rule for $d\geq5$ and $\beta<2k$. For $\beta\geq2k$, start with $k$ rank-two blocks, of total rank $2k$. Replacing two of them by a two-seed block with $2+x$ shared-source targets increases the time by $x$ and the rank by $2x+3$. Any $1\leq x\leq\ell$ fits the degree cap, including after protection. Distribute any feasible gain $e\leq P$ over $\lceil e/\ell\rceil$ replacements, saturating all but the last. This attains $E_{\mathrm{pair}}$. The seeds in these blocks return in distinct rounds, so imposing distinct return rounds also gives an exact classification with $D=P$.

For odd $k\geq3$ and $P<e\leq D$, use $n-1$ full two-seed blocks and one three-seed block with $q=e-(n-1)\ell+5$ shared-source targets. Use the pairs of the [degree-bounded three-seed block](#constructions-attaining-the-bounds), removing enough occurrences to leave $q$. Retain at least one occurrence joining the first lost seed to each of the other two. Both other seeds still return one round after the first. There are $D-(n-1)\ell+5$ available occurrences, and thinning preserves the degree cap.

The three-seed block contributes $q+7$ rounds, including its two seed-restoration rounds. It adds $3q+14$ vertices and $5q+18$ edges, including the incoming relays and excluding the incoming endpoint. Its rank increment is $2q+4$, so the total rank of these $n$ blocks is $2k+2e+3n+5$. This attains the triple term whenever it exceeds $P$.

In the degree-four and higher constructions, a chain of all-blue triangles uses the unused rank, and seed protection with a path for $J$ preserves the rank and both propagation times.

### Least rank attaining the degree-only bound

For $d\geq5$ the least rank attaining the degree-only maximum is $2k+2D+3n$ when $D=P$, and $2k+2D+3n+5$ when $D>P$. In particular, with $d=9$ and $k=3$, the exact value is $18$ rounds at ranks $24$ and $25$, and $19$ rounds at rank $26$.

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

### Finite bounds for two intact rounds

For every $d\geq4$ and $k\geq1$, let $m_d=M_{d,2,1}$ be the [exact single-loss value](ONE_LOSS_TIMING.md#quadratic-growth-with-the-maximum-degree), namely $15$ at $d=4$, $19$ at $d=5$ and $\lfloor d^2/2\rfloor+6$ at $d\geq6$. Then
$$
M_{4,2,k}=2+13k,\qquad
2+k(m_d-2)\ \leq\ M_{d,2,k}\ \leq\
2+\left\lfloor\frac{k(d^2+11)}{2}\right\rfloor\quad(d\geq5).
$$
The bounds differ by at most $2k$ rounds. The lower bound holds on connected $k$-fault-tolerant graphs.

#### Upper bound

Let $h$ of the $k$ lost seeds return in delayed round one, and let $b$ new discrepancies be born in that round. Choose one intact source for each birth. There are $a$ direct births from lost seeds, and $B_*$ births from retained sources with at least two lost neighbors. Count one incidence at the source for a direct birth, and one incidence at every lost neighbor of the source for any other birth. The total is $J=b+\nu$, with $\nu\geq B_*$. These incidences are distinct since sources force at most once. A seed restored in delayed round one must have an additional neighbor that had no white neighbors before the loss. The additional edge is outside this count, so $J+h\leq kd$.

At time one there are $D=k-h+b$ old discrepancies. First-round incidences at seeds still white are unavailable for the second-round count. A retained source used in round one has already used its intact force. A direct incidence leads to a first-round target that is already blue in the intact run and still white in the delayed run. It cannot give an intact second-round target or a source blue in both runs. The $h$ restored seeds accounted for at most $(d-1)h$ of the $J$ incidences. Thus at least $Q=J-(d-1)h$ are unavailable at the unreturned seeds. Separately, every old discrepancy that was initially white has an intact predecessor already used in round one. The remaining old incidence capacity is at most $(d-1)D+k-h-Q$.

In the final-round classification above, let $N$ count nonexceptional targets and $E$ count exceptional targets. At most $D-a_{\rm live}$ sources can act directly in intact round two, where $a_{\rm live}$ counts the unreturned seeds that were chosen as direct sources in round one. These sources have already used their force. The final-round cost satisfies
$$
\begin{aligned}
2N+E
&\leq dD+k-h-Q-a_{\rm live}\\
&\leq (d+1)k+(d-1)b-\nu-2h-a_{\rm live}\\
&\leq k(d^2+1)-d(\nu+h)-a.
\end{aligned}
$$
The last step uses $b+\nu+h\leq kd$ and $a\leq a_{\rm live}+h$.

For the delayed rounds after time two, group each old discrepancy with its exceptional targets. The initially lost seeds and the old vertices born from retained sources with one lost neighbor occupy at most three rounds per initial lost seed. The old vertices in that group arrive within one round of the seed. Its exceptional targets arrive within two rounds of the seed. If these groups contain $E_0$ exceptional targets, they occupy at most $\min(5k,3k+E_0)$ rounds after time two. Their contribution to the round count minus $E_0/2$ is at most $4k$.

There are $a+B_*$ other old discrepancies. Each of those and its exceptional targets occupy at most three rounds. With $E_1$ exceptional targets in these groups, the analogous count minus $E_1/2$ is at most $2(a+B_*)$, using $\min(3(a+B_*),a+B_*+E_1)$. Thus the full time is at most
$$
2+\frac{k(d^2+1)}2+4k+\frac{3a}{2}+2B_*-\frac d2(\nu+h).
$$
Since $a\leq k$, $B_*\leq\nu$ and $d\geq4$, this gives a preliminary upper bound of $2+\lfloor kd^2/2\rfloor+6k$.

#### Saving for each lost seed

Keep the slack in both counts. Put $\lambda=kd-J-h$. Let $u$ count physically unused old incidences in the final-round count, excluding the unavailable first-round incidences and the predecessors already subtracted. Let $v$ count initially white members of $D_1$ that are not chosen as direct final-round sources. The incidence inequality can then subtract an additional $(d-1)\lambda+u+v$ on the right of $2N+E\leq k(d^2+1)-d(\nu+h)-a$: substitute $b=kd-\nu-h-\lambda$, subtract the unused incidences from the capacity, and subtract $v$ from the direct-source allowance.

Write $R_z$ for the set of rounds after time two occupied by the regular group of a lost seed $z$, and $W_w$ for the corresponding set of an irregular old vertex $w$. Their exceptional-target counts are $E_z$ and $E_w$, respectively. These groups have nonnegative slacks
$$
4-|R_z|+E_z/2,\qquad 2-|W_w|+E_w/2.
$$
We may also subtract the sum of the group sizes minus the size of their union, and the number of nonexceptional targets arriving in that union. The preliminary bound counted these rounds more than once.

Call a lost seed good if it uses all $d$ first-round incidences and is chosen as a direct source. For each other seed we already save at least one round: the number of such seeds is at most $(k-a)+h+\lambda$, while the preceding bound saves $3(k-a)/2+dh/2+(d-1)\lambda/2$. For every good seed we will find at least one further round of slack at $d=4$ and at least half a round at $d\geq5$.

Let $z$ be good, let $w$ be its first-round target, and let $r$ be the delayed restoration time of $z$. The other $d-1$ neighbors of $z$ are retained sources already blue. If $R_z$ lacks any of $r-1,r,r+1$, then $|R_z|\leq\min(4,2+E_z)$ and its slack is at least one. If all three rounds occur and $w$ is still white at $r-2$, then $w$ returns in one of those rounds: $z$ can force it by $r+1$. The sets $R_z,W_w$ therefore overlap, saving one round.

It remains that $w$ is blue by $r-2$ and all three central rounds occur. At round $r-2$ the vertex $w$ has another white neighbor besides $z$, since otherwise it would force $z$ by $r-1$. If $w$ was not selected as a direct final-round source, it contributes one unit to $v$. Its white neighbor supplies an unused incidence at $w$ in $u$, because it is white at time one in the delayed run and so cannot be a retained source in that count. This gives a whole round of slack.

If $w$ has a selected direct final-round target $y$, consider its other white neighbors at $r-2$. If there are none besides $z,y$, then $y$ is still white at $r-2$ and fills by $r+1$, since $z$ returns at $r$. Thus $y$ arrives in $R_z$. It is counted in $N$ and saves a round by arriving in the union of the group rounds. Otherwise an additional white neighbor supplies an unused incidence at $w$, saving half a round. For $d=4$, the predecessor $z$, the target $y$ and this extra neighbor leave room for at most one exceptional source at $w$. With $E_w\leq1$, the slack $2-|W_w|+E_w/2$ is at least another half round.

The local contributions can be added. Distinct good seeds have distinct target vertices $w$, so their unused incidences, direct-source allowances and irregular group slacks are distinct. Their selected final-round targets $y$ are also distinct. The overlaps used here are between disjoint pairs of group identities $(R_z,W_w)$, so even when several pairs overlap at one time, the excess multiplicity counts every such pair. We have saved at least $k$ rounds in degree four and $k/2$ rounds in the other degrees. Applying these savings to the preliminary upper bound before taking the integer part gives the stated bounds. The concatenated construction gives equality at degree four.

#### Concatenated lower construction

Use $k$ copies of the [sharp single-loss constructions](ONE_LOSS_TIMING.md#quadratic-growth-with-the-maximum-degree), keeping the substantive vertices and omitting the individual prefixes and supports. Add one common two-round prefix. Use the last white vertex of each copy as the prefix endpoint for the relay list of the next. For $d=4,5$, retain the internal splice through the old vertex $w_0$. The only link into that copy from its predecessor is the relay into the first target of its list.

In the even-degree construction at $d\geq6$, reserve room for the outgoing relay at the last white vertex $u$. Keep only the edge from $u$ to the direct child of its late parent $w_3$, and its edge to its blue source. The other direct children keep their guard $G$. Until the final old-seed repairs begin, each is blocked by its own old parent and by $G$. In the final sequence $G$ may now fill in the same round as $z$. The vertex $u$ still waits for $w_3$, which returns in the round after $z$, so the time of $u$ is unchanged. The odd and small-degree constructions already have space for the outgoing relay.

The intact sources of each copy still finish in two rounds. After the $k$ designated seeds are lost, no copy starts before its prefix endpoint is blue: its old vertices are white, its retained sources are blocked, and its relays see two white endpoints. When the prefix endpoint becomes blue, it starts exactly the single-copy delayed sequence after the prefix. The last target of that copy then activates the successor. Thus the shared first two rounds are followed by $k$ further intervals of length $m_d-2$. The protection below preserves the degree cap and gives recovery from every loss of at most $k$ seeds.

### Two intact rounds at degree three

For every $k\geq1$,
$$
2+7k\leq M_{3,2,k}\leq 2+9k.
$$
For $k=1$ the [exact value is nine](ONE_LOSS_TIMING.md#two-round-colorings-at-bounded-degree).

#### Upper bound

Use the two-round incidence and group counts above, which hold before imposing a degree restriction. At $d=3$ they give the preliminary upper bound
$$
2+\frac{21k}{2}-\frac{3(k-a)}2-\frac{3h}{2}-\lambda
  +2B_*-\frac{3\nu}{2},
$$
before subtracting $u/2$, $v/2$ and group slacks. Since $\nu\geq B_*$, the last two terms together add at most $B_*/2$.

Each of the $B_*$ first-round targets has already used one of its three incidences on its intact predecessor. If it is chosen as a direct final-round source, it can have at most one exceptional target, and the slack of its irregular group is at least $1/2$. Otherwise it contributes $1/2$ through $v$. These distinct contributions absorb $B_*/2$.

We save at least another $3/2$ per lost seed. A seed that is not a chosen direct source already contributes $3/2$ through $k-a$. A chosen direct source with fewer than three counted first-round incidences contributes at least one through $3h/2+\lambda$, since $h+\lambda=3k-J$. Its regular group has at most one first-round target besides the seed. The old vertices therefore occupy at most two rounds, and at most one of the two outer rounds $r-2,r+2$ can occur, where $r$ is the seed's restoration round. With $E_z$ exceptional targets the group occupies at most $\min(4,2+E_z)$ rounds. Its slack is at least one.

Now consider a good seed $z$, with all three first-round incidences used, direct first-round target $w$ and restoration round $r$. No exceptional target uses an incidence at $z$. Each outer round in $R_z$ requires an old regular child in the adjacent central round. If one of $r-1,r,r+1$ is absent, at most one outer round can occur. When $r$ itself is absent, $r\leq2$ and the earlier outer round is outside the count. Thus $|R_z|\leq\min(3,2+E_z)$ and the group saves at least $3/2$.

If all three central rounds occur and $w$ is white at $r-2$, the overlap of $W_w$ with $R_z$ saves one round as above. There is another $1/2$ from the slack of $W_w$ if $w$ has a selected direct final-round target, and from $v$ otherwise. If $w$ is already blue at $r-2$ and has no selected direct final-round target, it supplies an unused incidence and contributes to $v$. The unused incidence and the predecessor leave at most one exceptional target, giving another $1/2$ from the slack of $W_w$.

If $w$ is blue at $r-2$ and has a chosen direct target $y$, there are two possibilities. With a further white neighbor besides $z,y$, the unused incidence, $z$ and $y$ fill all three slots at $w$. Its group has no exceptional targets and has slack at least one in addition to the unused incidence. With no such neighbor, $y$ arrives in $R_z$ as above, saving one round. The direct target and predecessor leave at most one exceptional target, again giving at least $1/2$ from the slack of $W_w$.

The charges for direct first-round targets use groups and incidences distinct from those used for the $B_*$ targets. The good-seed overlaps and direct-target arrivals can be charged together by the same disjointness argument as in the higher-degree bound. Subtracting $3k/2$ from $2+21k/2$ proves the upper bound.

#### Concatenated lower construction

Use $k$ copies of the twelve-vertex block in the [nine-round certificate](check_single_loss_bounds.py). In each block the initial seeds are $0,8,9,10,11$, the entry is $5$, and the exit is $6$. Begin with a three-vertex path whose first vertex is blue. A blue degree-two relay links its last vertex to the first entry. Other blue degree-two relays link each exit to the following entry. The graph has $13k+3$ vertices and maximum degree three. In the intact run each copy fills $1,2,3$ in round one and $4,5,6,7$ in round two, independently of the relays.

Delete seed $0$ in each copy. Before its incoming relay can force, every local blue source is blocked and all white vertices in the copy remain white. Once the preceding endpoint turns blue, the local newly blue sets in successive rounds are
$$
\{5\},\ \{7\},\ \{4\},\ \{1\},\ \{0,2\},\ \{3\},\ \{6\}.
$$
The outgoing relay sees two white endpoints until either its exit or the next entry turns blue. Inductively the next copy stays white at its entry until this relay fires. The shared prefix takes two rounds, and each copy adds seven rounds. This proves the lower bound for the designated losses.

<a id="cycle-rank-one-at-degree-three"></a>
<a id="cycle-rank-two-at-degree-three"></a>

#### A cycle-rank bound at degree three

For a connected graph of maximum degree at most three and rank $\beta$, with intact time at most two and a recoverable loss of $k\geq1$ seeds,
$$
T\leq 2+5k+\beta.
$$
This is sharp for every $0\leq\beta\leq k$. At $\beta=k+1$ or $k+2$ the exact value is $2+6k$. For every $\beta\geq k+2$ there is a stronger bound $T\leq5k+\beta$, also sharp at $\beta=k+3$. The examples through rank $k+2$ tolerate every loss of at most $k$ seeds. The [single-loss classification](ONE_LOSS_TIMING.md#cycle-rank-at-degree-three) gives exact values for all ranks when $k=1$.

**A local constraint on the trail.** In a delayed propagation trail on a graph of maximum degree three, a distinguished vertex other than the final mark has at most one white neighbor after it arrives. If it still had two, its only blue neighbor would be the source that just restored it. The vertex itself could not force in the next round, and the source that restored it has already spent its force. These are the two ways the trail can continue. In particular, a distinguished direct first-round child $w$ of a lost seed $z$ cannot arrive two or more rounds before $z$. It would see $z$ and another white neighbor, since otherwise it would force $z$ in the next round. It could not be the final mark while $z$ is still white.

A direct child whose arrival is at most one round after its root therefore lies within one round of the root. If it arrives at least two rounds after its root, the root has a separate edge to another lost seed still white when the root returns. The direct child was its root's unique white neighbor at intact time zero. Thus a late direct child reserves an incidence to another lost seed, separate from all first-round child incidences and all shared guards. As in the general count, a single-neighbor child of a retained source always arrives within one round of its associated root.

**Assign the extra marks.** Let $p$ count distinguished roots, let $\ell_z$ be the number of marks in the visit distinguishing root $z$ (zero if there is none), and let $V$ count all visits to the discrepancy subtrees. A rootless visit of size $m$ contributes $m-1$ above an allowance of one mark. A rootless visit of size at least two has a distinguished first-round center, and a three-mark visit has its center in the middle. Use the $B$ chosen shared guards and the $Q$ used guards from [the rank count](#counting-the-visits-with-shared-first-round-sources). We will bound
$$
\sum_{\text{rootless visits}}(m-1)-B+Q
\ \leq\ \sum_z c_z,\qquad
c_z=\begin{cases}5-\ell_z,&\ell_z>0,\\4,&\ell_z=0.\end{cases}
$$

For direct or single-neighbor visits of size at least two, charge one unit to the associated root's incidence for the first-round child, and one more to that incidence for a triple. For a shared visit, the term $-B$ absorbs one unit. A shared two-mark visit then costs only one unit if its chosen guard is used, charged to the incidence of the paid guard. A shared triple costs one unit even if its guard is unused. Its retained source has degree three, with exactly two lost neighbors besides the center. If the guard is used, the trail step must join those two roots, since the three-mark visit already uses both sides of its center. Charge the guard unit at the root paying for the guard and the triple unit at the other root's incidence with the same source. Both root visits have free facing sides and hence size at most three. For an unused guard of a shared triple, assign the triple unit to either adjacent root whose visit has fewer than five marks. Such a root exists. Two full root visits occupy disjoint five-round windows, so their times differ by at least five. The shared center would then arrive within one round of the later root, since an earlier center would let its source force that root early and a later center could be forced in the next round. The triple would overfill the later root's window.

Each shared unit uses a distinct root incidence, separate from the branches supplying marks to the root visit. For the nonparent root this is because the guard edge is outside the forest. For the parent root, a branch with an indirect first-round child can only supply a mark to the root visit if that child itself is marked there. Reaching a second-round mark without marking the indirect first-round child would require at least three original edges in one trail step. This also separates all single-neighbor visit incidences from the branches used by the root visit. For a direct child the same separation holds for a triple: its two child edges are already used, and its center cannot be marked again. The only possible shared use of an incidence is therefore a direct two-mark visit whose branch also supplies one mark to the root visit. In that case its center is an intermediate source on the step from or to the root and is already blue before the root arrives. Its visit uses times within the root's five-round window.

**Check each root's allowance.** A root visit of size four or five uses at least two branches. It cannot coexist with a long single-neighbor or direct visit assigned to that root. For a single-neighbor child the marks would overfill the five-round window. For a direct child, either its branch contributes a mark to the root visit, which puts the child's arrival within one round, or the two other branches exhaust the remaining incidences at the root. In the latter case the root has no adjacent lost seed to keep the child late. The marks again overfill the window. At most one shared unit is available if $\ell_z=4$, and no shared unit was assigned to a root with $\ell_z=5$.

For $\ell_z=3$, a single-neighbor triple would overfill the window. A direct triple must be late and uses both its own incidence and an edge to another lost seed, leaving just the root visit branch. Its two units fit the allowance. Otherwise each incidence outside the root visit carries at most one unit, for a total of at most two. If the root visit also shares a direct two-mark branch, it must have used two branches to reach its three marks. Only one incidence then remains outside the visit, so the total is still at most two.

For $\ell_z=2$, the root visit uses one branch. If it shares the branch of a direct two-mark visit, no single-neighbor triple can also occur because the three visits would exceed the five-round window. There are then at most three units including the shared branch. Otherwise only two incidences are available. They cannot both carry two units. Two single-neighbor triples overfill the window, as do a single-neighbor triple and a direct triple within one round of the root. A late direct triple reserves an additional incidence. Thus there are at most three units in this case as well.

For $\ell_z=1$ or $0$, all three incidences are available before assigning rootless visits. Among the direct and single-neighbor triples, at most one can lie within the root window. A second must be a late direct triple and must reserve a separate incidence. There are therefore at most four units, even when two incidences carry two units each. Empty visits decrease the left side of the claimed inequality.

Finally, $V+B-Q\leq k+\beta$. Adding the root marks, one mark per rootless visit, and their excess gives
$$
T-2\leq \sum_z\ell_z+(V-p)+B-Q+\sum_z c_z
\leq \sum_z\ell_z+(k+\beta-p)+\sum_z c_z
=5k+\beta.
$$

##### When the linear bound can be attained

Suppose $T=2+5k+\beta$. All visits are nonempty, every root attains its allowance $c_z$, and $V+B-Q=k+\beta$. Let $H$ be the union of $F$, the trail, and the chosen guards. If the trail meets $v$ subtrees, the rank proof first gets rank at least $V-v$ and at most $k-v$ component joins from the $B-Q$ added edges. Equality requires all $k-v$ joins, so $H$ is connected and has rank $\beta$. In particular, every edge of the original graph with both ends in $F$ must already be in $H$.

**Direct centers are near their roots.** A late direct two-mark visit cannot use its root's whole allowance. It spends incidences at the direct child and at a separate lost neighbor. A root visit of size two or three still needs another branch, leaving only the one unit of the direct visit. For a root visit of size zero or one the last incidence gives at most two more units, short of four. A root visit of size four or five already excludes direct long visits.

For a late direct triple with center $w$ at root $z$, one neighbor $u$ of $z$ is another lost seed still white when $z$ returns. The remaining neighbor of $z$ must be a retained source. If $\ell_z=3$ it is the source of the root visit's branch. If $\ell_z=0$ or $1$ it supplies the two remaining units through a single-neighbor triple. The case $\ell_z=2$ leaves no incidence for the third unit, so equality excludes it. The edge $zu$ is outside the forest and the chosen guards and must occur on the trail. Since $u$ arrives later than $z$, the step using this edge can distinguish both roots directly only by a force from $z$ to $u$ immediately after $z$ returns. The white vertex $w$ prevents that force. Otherwise the step uses $z$ as an intermediate source and distinguishes $u$ and $w$, since the third neighbor of $z$ is retained and cannot be a mark. Both sides of the marked $w$ are already used inside its triple. This also rules out late direct triples. All units from direct and single-neighbor visits are therefore represented by marks within their associated root's window.

**Shared units near a root or between roots.** A used guard either joins two distinguished roots in one trail step or joins its paying root with the center of a shared two-mark visit. In the latter case both marks lie in the paying root's window. An unused guard of a shared triple must have exactly one root with a nonfull visit. If both roots were nonfull, the triple unit could be assigned to either of them by the preceding argument. Moving it would violate the allowance of the other root, since both allowances are already attained.

Let $z$ be that nonfull root and $f$ the full root. The triple avoids the full window of $f$. Its center cannot be earlier than that window. If it were, the retained source would make the restoration rounds of $z,f$ differ by at most one. Then $z$ could not be distinguished because its own time is already used, and at most one time in its window would be free for local visits. There would be no local two-unit charge, as all direct and single-neighbor visits are near. Its three incidences could supply at most three units, short of $c_z=4$. Hence the triple follows the window of $f$. The retained source has to wait for $z$, whose return is more than one round after that of $f$. The center is then within one round of $z$ and its triple lies in $z$'s window.

The remaining used guards join two distinguished roots in one step. These steps form disjoint paths of consecutive root marks along the trail. In a path of $h\geq2$ roots, the union of root windows contains $h+4$ times. Each of the $h-1$ steps gives at most two units to the roots, one at each end if it comes from a shared triple. All other units assigned to these roots are represented by distinct marks in the union of windows, apart from the marks in their own root visits. Since $c_z+\ell_z=5$ at each distinguished root, at least $5h-2(h-1)=3h+2$ times are needed. This exceeds $h+4$. Thus no such steps occur. Every assigned unit is now represented by a visit inside its root's window that uses strictly more marks than units. A distinguished root with $c_z>0$ would require more than five times including its root visit. An undistinguished root would need at least two visits to supply four units, again requiring more than five times. Therefore all $k$ roots have full five-mark visits.

**Singleton visits cost separate direct children.** The full root windows are disjoint. All regular and shared first-round arrivals lie within one round of a root, because the two neighbors of any shared source are now full roots with restoration times at least five apart. A distinguished direct first-round child could only be outside the full visits if its root used two other branches. Those branches and the direct child account for all three root incidences, so the child lies within one round of the root as well. Consequently every remaining visit is a singleton second-round mark outside all root windows. In particular all distinguished old vertices are internal to their full root visits.

Write $y$ for a singleton mark and $w$ for its forest parent. If the parent is indirect, an arrival gap of at least two needs another old neighbor of its intact source, since the source would otherwise see only $w,y$ as possible whites after round one. The extra edge is outside the forest and could be used on the trail only at a distinguished old endpoint. All distinguished old vertices have both sides inside their visits, so the extra edge would increase the rank of $H$. It follows that $y$ is within one round of $w$.

For a direct second-round mark $y$, its parent cannot be a lost root $z$. A full root visit would use the other two incidences at $z$ on retained first-round sources, so $z$ could force $y$ within one round when it returns. In the other direction, a marked $y$ arriving at least two rounds early would have to see another white neighbor to block its force to $z$. The same argument excludes a gap of at least two with $y$ earlier than its first-round parent $w$. If $y$ arrives at least two rounds later than $w$, another old neighbor of $w$ must be white when $w$ returns. The only possible forest edge from $w$ to such a neighbor is to its own lost root $z$. If that were its sole other white neighbor, $y$ and $z$ would arrive within one round of each other. Thus there is an extra old-to-old edge outside the forest. No such edge can be on the trail, since its distinguished old endpoint would need a free side. In either direct or indirect case we have shown that $y$ is within one round of its parent $w$.

The only old vertex $w$ close enough to an out-of-window singleton is an undistinguished direct first-round child of some root $z$. Its full root visit uses two other branches, so $w$ cannot arrive later than one round after $z$. Thus $y$ arrives at least three rounds before $z$ and $w$ at least two rounds before $z$. If $y$ were direct from $w$, the vertex $w$ would need another white neighbor $g$ after both $w,y$ have returned. Otherwise it would return $z$ early. The edge $wg$ is outside the forest: $wz,wy$ are the direct edges, and any other forest neighbor of $w$ would be a relay blue by round one. The only way to use $wg$ on the trail would be through the unmarked $w$ as a source, since $g$ is later than $w$. The other end of that step cannot be $z$, whose full visit uses other branches. It cannot be $y$ either: $g$ arrives after $y$, and $w$ would see both $g,z$ white after $y$ arrives, so it cannot force $g$ in the next round. This contradicts rank saturation. Every singleton is therefore indirect through a relay at its parent $w$. When $w$ returns early it needs two white neighbors, $z$ and a guard blocking the force to $z$. It has room for at most one relay to an indirect singleton. There are at most $k$ direct first-round children, hence at most $k$ singleton visits. Equality gives $V=k+\beta$, so $\beta\leq k$ as claimed.

##### A stronger bound when all root visits are full

Suppose the late trail has a five-mark visit at every lost root. Then, writing $s=T-2-5k$ for the number of remaining distinguished marks, we have
$$
\beta\geq s+\max(0,s-k).
$$
In particular, $T\leq 2+5k+\min\{\beta,\lfloor(\beta+k)/2\rfloor\}$. At $\beta=k+2$ the stronger bound $T\leq2+6k$ holds for these trails.

The full root windows are disjoint, so any regular or shared first-round child lies within one round of a root. A distinguished direct first-round child outside the full visits would have a root using two other branches. Its arrival would likewise be within one round of that root. Thus the remaining visits are singletons or empty visits, and singleton marks are second-round targets outside every root window. The union of the trail and $F$ is connected and has rank at least $s+E$, where $E$ is the number of empty visits to $F$.

Use the singleton analysis above, now allowing extra edges that are outside this connected union. A singleton with an indirect source whose old parent arrives within one round must have an undistinguished direct first-round parent $w$. The parent returns early and needs a guard in addition to its lost root, so it has room for only one relay to such a singleton. There are at most $k$ singletons of this type. Every other singleton needs an extra edge. For an indirect source it is an edge to another old neighbor, which cannot be on the trail because all distinguished old vertices are internal to their full visits. For a direct target separated from its parent, the only possible case is a late arrival with an extra blocking edge between old vertices. Again no such edge can be used on the trail. For a direct target near its early parent $w$, it is the edge $wg$ to a neighbor still white after both the parent and the target return. As above, the edge cannot be used through $w$ on a step with its full lost root or with the direct target. The indirect edges identify their intact sources, and the direct edges identify their intact sources by their earlier endpoints. The edges from different singletons are therefore distinct. This proves the rank bound.

Now let $\beta=k+2$ and suppose $s=k+1$. There must be exactly $k$ singletons with an early direct first-round parent and one other singleton, whose extra edge uses the last unit of rank. In particular there can be no shared first-round child. Its retained source would require another edge to the root other than its forest parent, outside the trail because the root has a full visit. This edge is distinct from the exceptional singleton's edge, since a retained source cannot have both an intact first-round and an intact second-round target. Thus the old vertices are the roots, the regular first-round marks at times $r_z-1,r_z+1$ in each root visit, and one early direct parent at each root. Each root has its three incidences used by its two branches and its early direct child. That child uses its three incidences on the root, its singleton relay, and a neighbor still white when the child returns.

If the exceptional singleton has an indirect source, both old neighbors of that source must be regular first-round marks. Neither a root nor one of the early direct parents has an incidence available for this retained source. The marks at the two old neighbors occur at least two rounds apart, since they lie at offsets $-1,+1$ in disjoint full windows. The singleton, which is outside all windows, has to be at least two rounds before the later of those marks. Otherwise, once both old marks have arrived, its source can fill it within one round of the later mark. But if the singleton and the earlier old mark are both blue at least two rounds before the later mark, this source would force the later old vertex early. This rules out the indirect case.

If the exceptional singleton is direct from a regular first-round mark, that mark's branch uses two retained relays, one to the lost root and one to the distinguished second-round mark. The singleton is a different target, so the parent could force it within one round of returning. It also cannot arrive at least two rounds earlier than its parent by the subcubic trail constraint. If its parent is the early direct child of a root, the parent's third edge must be to the exceptional singleton, since its other neighbors are the root and its ordinary singleton's relay. A singleton arriving before the parent's return would let the parent restore the root too early. A singleton arriving afterward lies within one round of the root, as the parent can force whichever of the root and the singleton returns last. A lost root itself has already used its intact force on its first-round child. These contradictions rule out $s=k+1$.

##### A necessary condition one round below the linear bound

Suppose $\beta\geq k+2$ and $T=1+5k+\beta$. Then $V+B-Q=k+\beta$, there are no empty visits to $F$, and the root allowances are tight except for a deficit of exactly one unit at a single root. To see this, write $h=k+\beta-(V+B-Q)$, and let $d$ be the sum of the deficits in the root allowances. The mark count gives the exact identity $h+d+E=1$, since an empty rootless visit loses its allowance of one mark. We show that $d$ cannot be zero.

With all root allowances tight, late direct two-mark visits are excluded as in the equality proof. For any late direct triple, the additional edge to a lost neighbor is outside the trail and the chosen guards by the same local argument. These edges are distinct because the earlier lost endpoint identifies the direct center. Adding them in the rank count shows that there are at most $h$ late direct triples. If there are none, the argument that places all charges in root windows, or on steps between consecutive roots, again forces every root visit to be full. Then $s=\beta-1$, which violates the full-root bound for $\beta\geq k+3$ and the stronger full-root bound at $\beta=k+2$.

The remaining case has $h=1$ and just one late direct triple, centered at a child $w$ of root $z$. The three incidences of $z$ are to $w$, another still-white lost seed $u$, and a retained source. The retained source is used on the root visit's branch when $\ell_z=3$, or for a single-neighbor triple when $\ell_z=0$ or $1$. In particular $z$ has no shared source. All shared units still fall within their assigned root's windows or on steps joining consecutive root marks. The argument for an unused shared triple is unchanged, as its nonfull endpoint cannot be $z$ and has no late direct triple. Any path of paid steps between consecutive roots also avoids $z$, so the same window count excludes such paths. All roots except $z$ must therefore have full visits. But just after $z$ returns, its only white neighbors are $u,w$. Either one can let $z$ force the other in the next round, so their arrivals differ by at most one. The late triple at $w$ now overfills the full window of $u$. This eliminates $d=0$ and proves the necessary condition.

##### Excluding the remaining one-unit deficit

Suppose $\beta\geq k+2$ and $T=1+5k+\beta$. The preceding necessary condition gives a connected, rank-saturated union $H$ of the forest, trail and chosen guards, with exactly one root short of its allowance by one unit. Every edge with both ends in the forest must be in $H$. We classify the shared visits before counting the remaining singleton visits.

**Direct long visits are near.** A late direct triple remains impossible with the one-unit deficit. Its root $z$ needs one incidence to the child $w$ and another to a still-white lost seed $u$. The third incidence must go to a retained source: for $\ell_z=2,3$ it is the source of a different root-visit branch, and for $\ell_z=0,1$ it must supply at least one additional unit. In the latter case $z$ has no other direct first-round child, so the extra unit uses a retained source. The edge $zu$ cannot be on the trail. The original late-triple argument still applies: $w$ would block a direct step from $z$ to $u$, and a step through $z$ would have to use an occupied side of the triple center $w$.

A late direct two-mark visit can only be at the defective root $z$, with $\ell_z=0,1$ or $3$. At size three the root visit needs the third incidence, a retained branch source. At size zero or one the remaining incidence must carry two units, through a single-neighbor triple. Thus $z$ has no shared source. The late two-mark visit's center must be consecutive to $u$ on the trail, since the edge $zu$ can only be used with $z$ intermediate between $u$ and $w$. Both marks of the visit therefore lie in $u$'s window. To see that $u$ is full, first note that an unused shared triple with two nonfull roots must involve the defective root: its unit could otherwise move to the other root and exceed an already tight allowance. Here there is no such triple, since $z$ has no shared source. An unused shared triple earlier than the window of its full endpoint also cannot occur, by the earlier window argument at the nonfull endpoint, which has a tight allowance and no late direct visit. Thus all shared units lie in their assigned windows or on steps between consecutive roots, and any path of those steps avoids $z$. Every other root has a tight allowance. The window argument excludes these paths and makes every other root full. The two marks in $u$'s window give a contradiction.

**Two possible configurations of root visits.** There is at most one unused shared triple with two nonfull endpoints. Each such unit must be assigned to a tight root and could be moved to the unique defective root. Moving two units would exceed its allowance. For an unused shared triple with a full endpoint $f$, a center earlier than $f$'s window would force the other root $z$ to be undistinguished and at most one round from $f$. Its window would have at most one free time, so its at most three units from shared incidences cannot meet a tight allowance of four. Thus $z$ is the defective root. All three units would have to come from unused shared triples earlier than the full windows of their other endpoints. No used guard can charge an undistinguished root, and a triple with two nonfull endpoints must be charged to the tight endpoint. There is at most one full root within one round of $z$, and its two full-visit branches leave room for at most one such shared source. Three units are impossible. Thus every unused triple with a full endpoint can be charged within the other endpoint's window.

For the possible unused triple with two nonfull roots, assign its unit within a root window if it fits in one. If it lies in neither window, its two roots restore at most one round apart. Indeed, with a gap of at least two the retained source puts the center within one round of the later root. There is therefore at most one assigned unit outside a window apart from used guards on steps between roots. In a path of $j\geq2$ such steps' roots, at least $5j-2(j-1)-2=3j$ times are needed in the union of the windows, allowing for both the one-unit deficit and the one unused triple's unit. The union contains $j+4$ times. The only possible path has two roots. Equality requires that both the deficient root and the recipient of the unused triple's unit are on that path, that the step uses a shared triple's guard and pays two units, and that no unit on these roots requires a visit inside a window. The two root visits then have three marks apiece and their free sides face the step. Their incidences are exhausted by the two shared sources and the root-visit branch at each root. All other roots are full.

If there is no such path, a triple outside both windows is impossible. Its two nonfull endpoints would need at least four distinct marks each in their windows, even allowing for the deficit and the unit charged outside a window. For an undistinguished endpoint the remaining three units require at least two visits, using at least five marks. The two windows have at most six times in total. Therefore with no root-to-root paid step, every unit is charged within a window. Exactly one root $z$ is nonfull. It has $c_z-1$ units, and every visit supplying units consumes more marks than units. The possibilities are $\ell_z=4$ with no charged visit, $\ell_z=3$ with one charged two-mark visit, $\ell_z=2$ with one charged triple, or $\ell_z=0$ with a two-mark visit and a triple. Size one would require at least two visits to supply its three units, overfilling the window. Size two is also impossible. The two root marks use $r_z$ and an adjacent time, leaving three nonconsecutive times for the triple. At size zero both visits are local, from direct or single-neighbor children. A paid guard cannot charge an undistinguished root, and an unused shared triple would use three of the available times for just one unit. At size three or zero the charged visits and root marks use the full five times. At size four they leave one time at distance two from $r_z$.

**Singletons and edges outside the forest.** In the two-root configuration the two three-mark root visits and the paid step occupy their entire joint six-round window. Both shared triples are already counted. There can be no other shared long visit: neither paired root has another incidence outside its marked branch, and a shared child of two full roots is near the later full root. An additional shared source's edge to its nonparent lost root would have to be on the trail. The only free root sides face the already occupied step of the paired roots, so no such source exists. In the single-nonfull-root configuration, all other roots are full. The nonfull root's visit and charged visits use at least four times in its window, so it cannot restore within one round of a full root. Thus any shared child arrives within one round of the later root. No uncharged shared two-mark visit fits in the remaining times. In fact the only possible shared child is the charged two-mark center when $\ell_z=3$. An edge from any other shared source to its nonparent lost root must be on the trail, but could only use a free side of $z$. Such a side faces the center of the charged two-mark visit, and a shared source can connect $z$ only to the other lost neighbor or to its own center in that step.

There is no edge between lost roots in the single-nonfull-root configuration. Such an edge is outside the forest and the chosen guards. It cannot attach directly to a distinguished full root on the trail. If it uses a full root as an intermediate source, the other endpoint of the step besides $z$ must be a marked child on one of that full root's two branches: these two branches consume both remaining incidences, and a retained neighbor cannot be a mark. An old child on a full branch has no free side for a step leaving that visit. In the two-root configuration the paired roots' incidences are already exhausted, and the same reasoning excludes edges between full roots. In particular a direct first-round singleton cannot be late, because its parent lost root has no other lost neighbors. It cannot be early by more than one round by the subcubic trail constraint. All singleton marks are therefore second-round targets. The only possible singleton inside a root window is at the missing outer time of a four-mark visit.

For a singleton outside the occupied windows, a near indirect parent again has to be an unmarked early direct first-round child. Its lost parent and its white guard leave room for only one relay to such a singleton. Call these the ordinary singletons. A lost root cannot directly supply a far second-round singleton. If its intact force is to such a target, its other two incidences go to retained sources on its full branches or on the branches counted in the nonfull configuration. A root of the shared pair has no spare incidence outside its shared sources and counted branch. For all other far singletons the extra-edge argument for full roots applies: the exceptional edge is from a second-round source to an additional old neighbor, or joins an old parent to a white blocker. Rank saturation requires the edge on the trail. In the indirect case or the late direct case it uses a free side of a distinguished old vertex. For a direct target near its early unmarked parent $w$, the extra $wg$ edge to a later vertex must be used through $w$. The other mark cannot be the singleton, since the still-white lost parent blocks the force. The step must therefore join the lost parent with $g$, using a free side of the lost parent. The exceptional edges are distinct by the same intact-source and earlier-endpoint arguments used for full roots.

**Counting the singleton visits.** Write $s$ for the number of singleton visits outside the counted root and long visits.

- For the shared pair, the two roots' only free sides face the step through the retained shared source. That source's intact force is already used in round one, so no exceptional singleton edge can be used there. No ordinary singleton can be supplied by either paired root, all of whose first-round children are already counted. Thus $s\leq k-2$. Here $V=k+s+2$, $B=2$, and $Q=1$, giving $\beta=s+3\leq k+1$.
- For $\ell_z=4$, there are no long visits. There is at most one old free side at the short end of the root visit, and one vacant outer time in the window. To have $s\geq k+2$ would require $k$ ordinary singletons, a near singleton $b$ at the vacant time, and an exceptional edge on the step facing it. If its source is indirect, the intermediate source would see the distinct second-round target $b$ white at intact time one, which is incompatible with its intact force to the exceptional singleton. For a late direct exceptional target the extra edge must use its old parent $x$ as the intermediate source, since $b$ is new. With $k$ ordinary singletons, every unmarked direct first-round child already uses a root, an ordinary relay, and a guard. It cannot also have both a direct exceptional target and an extra edge to the old short-end mark. Every regular first-round mark other than the short-end mark has both its predecessor incidence and its branch's second-round incidence in use. It likewise has no room for both edges. A near direct exceptional target would need a free side at its lost parent, and all lost roots are internal. Thus $s\leq k+1$ and $\beta=s\leq k+1$.
- For $\ell_z=3$, the root must be an endpoint of its visit: a middle root would leave two nonconsecutive times for the two-mark visit. The two marks occupy the other side of the window, with their old center next to the root in time because the center is within one round of it. The only old free sides face each other on that step. It can pay at most one exceptional edge. A two-edge step through an unmarked second-round source can pay only for that source's own intact target. Through an old source, both old-to-old blocking edges would have that same earlier endpoint as owner. In the near direct case the other edge of the step is the forest edge to the lost parent. If the charged visit is direct, its root supplies no ordinary singleton and $s\leq k$. If it is shared, the step already uses the retained first-round source and cannot pay an exceptional edge. If it is single-neighbor and all $k$ ordinary singletons occur, $z$ uses both retained first-round sources and its early direct child. The retained sources have already spent their intact forces, and the early direct child has no room for a direct exceptional target and another old blocker. Thus no exceptional edge can be used on this step beyond $k$ ordinary singletons. In every case $s\leq k$, and $\beta=s+1\leq k+1$.
- For $\ell_z=0$, the two visits are contiguous groups of sizes three and two partitioning the window. Their first-round centers are within one round of $z$, so the two-mark center faces the triple's second-round endpoint. This is the sole old free side. There is room for at most one exceptional edge. If there are $k$ ordinary singletons, both local visits at $z$ must come from retained sources. The triple's center already uses all three incidences, every other regular old vertex except the two-mark center has two branch incidences in use, and each unmarked direct first-round child has its ordinary relay and lost root. A late direct exceptional target could only be paid by an older old source intermediate on the step to the triple's second-round mark, so none of these vertices has room for both the direct target and the extra edge. An indirect source on that step would see two distinct second-round targets, and the near direct case needs a distinguished lost root with a free side. Therefore $s\leq k$, and $\beta=s+1\leq k+1$.

All cases contradict $\beta\geq k+2$. Since the linear bound itself is strict in this range, the integer upper bound is $T\leq5k+\beta$.

##### Attaining the bounds

**Construction.** Use the [two-arm blocks](#exact-values-when-the-cycle-rank-is-at-most-the-loss-budget) at $t=2$. In each of the first $\beta$ blocks, replace the edge entering the far endpoint of the left arm by a two-edge path through a new white vertex $y$. For that block's lost seed $z$, add a white neighbor $w$ of $z$ and a white leaf $g$ at $w$. An initially blue relay links $w$ to $y$. This adds one unit of rank per modified block. Only $z$, $w$ and $y$ can have degree three inside the modification, and the only initially blue one among these is the designated lost seed.

Intact, $z$ forces $w$ in round one, and $w$ and its relay then force $g$ and $y$ in round two. Under the designated loss, the previous endpoint first forces $y$. In the next round $y$ starts the left arm and the relay restores $w$. The white leaf $g$ keeps $w$ from restoring $z$ early. The rest of the two-arm block takes its original five rounds, with $g$ filling in parallel with the first right-arm vertex. Thus the total is $2+5k+\beta$.

All retained blue vertices of these blocks have degree at most two before protection. Use the [private paths and path support](#protection-and-a-minimum-killing-support), connecting the prefix seed to the far endpoint of a private path of a support edge source. This leaves room for the private path at each edge source. A far endpoint remains an endpoint of the propagation along its private path, so a consecutive blue pair on the path can still restore the entire path and its protected vertex. The attachment is a bridge and preserves the rank, intact deadline and designated arrival times. The resulting graph is connected, has degree at most three, tolerates every loss of at most $k$ seeds, and has a minimum killing support of size $k+1$.

At rank $k+1$ or $k+2$, begin with all $k$ blocks modified and attach one or two all-blue cycles linked by bridges at the end of the prefix seed's private path. Each cycle has length $2k+4$, with its attachment ports outside an interior path of $2k+2$ cycle vertices. This path keeps a blue pair under any loss of at most $k$ seeds and restores the cycle independently. The attachment preserves the degree cap, the original private-path repairs, and both designated times. Each cycle adds one unit of rank and keeps the recovery time $2+6k$.

##### Mixed constructions at higher ranks

For every $k\geq1$ and $\beta\geq0$, there is a connected subcubic example with intact time two and a designated $k$-seed loss taking
$$
2+5k+\min(k,\beta)+\min\!\left(k,\max\!\left(0,\left\lfloor\frac{\beta-k}{3}\right\rfloor\right)\right)
$$
rounds to recover. For $\beta\leq k$ this is the preceding low-rank construction. For $\beta\geq k$, start with $k$ rank-one blocks and replace $a=\min(k,\lfloor(\beta-k)/3\rfloor)$ of them by the [seven-round blocks](#concatenated-lower-construction-1). Each replacement increases the recovery time by one round and the rank by three.

Put the seven-round blocks first, with their common two-round prefix. Their final exit then feeds the remaining rank-one blocks through a direct edge into the first entry. Each interblock connection is a bridge. The seven-round exit has room for this edge and its other neighbor is already blue when it returns in the designated run. Both endpoints of the new edge are white at intact time one and blue by time two. In the designated run the next block waits for the exit and then begins its serial recovery as in the low-rank construction. Pad to the prescribed rank with all-blue cycles attached by bridges to the prefix seed. At $\beta=k+3$ a single seven-round block gives $3+6k$, attaining the improved upper bound. For example, the construction gives fifteen rounds at $k=2,\beta=5$, and sixteen at $k=2,\beta=8$. The mixed examples certify recovery for the designated loss.

## Protection and a minimum killing support

For the constructions using this protection at $d\geq4$, add a support $H$ of $k+1$ blue vertices. Take a connected simple graph $J$ on $H$. For every edge of $J$, add a blue vertex adjacent to its two endpoints. Connect one of these new blue vertices to the prefix seed $s$. The constructions at a prescribed cycle rank use a path for $J$. The other protected constructions use $J=K_{k+1}$ if $k\leq d$, and a path otherwise.

Protect every original blue vertex and every added edge source, except the $k$ designated slow-loss seeds. For each protected vertex attach a private all-blue path of $2k+2$ vertices by one endpoint. Each protected vertex has degree at most three before the attachment. The extra blue vertices leave the intact and designated slow runs unchanged, and the resulting graph is connected with maximum degree at most $d$.

Under any loss of at most $k$ seeds, each private path retains at least $k+2$ vertices. Among them there is a consecutive blue pair, which can restore the path and its protected vertex irrespective of that vertex's other neighbors. The edge sources of $J$ can now spread blue through $H$ from at least one retained vertex. At this point only some of the $k$ designated seeds may still be white among the initial blue set. Monotonicity and recovery from the designated all-$k$ loss show that the whole graph recovers.

Losing all of $H$ leaves each of its external neighbors adjacent to two white vertices of $H$. This loss stalls, so $H$ is minimum by fault tolerance. With losses only in $H$, its repair runs in parallel with the intact original run. The blue edge sources of $J$ spread blue one edge per round from the retained vertices. The worst restricted time over at most $k$ losses is therefore $\max(t,\operatorname{diam}J)$, since a loss of $k$ can retain one vertex with maximum eccentricity. For the clique this is $t$.

## Reproduction

Run the following from the repository root.

~~~sh
python -B research-twins/check_multiple_loss_bounds.py
~~~

The script replays the full arrival sequence of the low-rank, shared-center and two-level detour constructions and the contracted trails on five branched trees attaining the forest bound, on the cyclic degree-three construction with up to 32 designated lost seeds, and on the one-round constructions at prescribed cycle rank and degree cap. It exhausts losses through the budget on the degree-two examples, on the small cycle-rank constructions with one or two losses, and on the smallest protected two-loss example. It checks the cycle upper bound through cycle order eleven for up to three losses, and the subcubic one-round upper bound on every labeled simple graph through order five. It also checks the exact local arrival rounds of the degree-three construction and seven higher-degree concatenated examples. On the larger protected graphs it checks designated losses, restricted deadlines, the killing loss and samples of clustered and mixed deletions. The proofs above give the guarantees for arbitrary budgets.
