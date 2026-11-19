# Recovery from several lost initial blue vertices

Use the synchronous rule and initial-color loss model of the [single-loss bounds](ONE_LOSS_TIMING.md). Let $M_{d,t,k}$ be the largest finite recovery time over graphs of maximum degree at most $d$, initial blue sets with intact completion by round $t$, and losses of exactly $k$ initial blue vertices. A $k$-fault-tolerant set recovers from every loss of at most $k$ seeds, in the terminology of [Fault Tolerant Zero Forcing](https://arxiv.org/abs/2509.07854).

- **Degree two.** For $t\geq1$ and $k\geq1$, the exact value is $M_{2,t,k}=t+k(2t+1)$. On cycles the exact value is $t(k+1)+\lceil k/2\rceil$.
- **Forests and cycle rank.** The exact value on forests of unrestricted degree is $t+k(2t+1)$. At cycle rank $\beta$ and $t\geq1$, an upper bound is $t+k(2t+1)+(2t-1)\beta$. The bound is exact for $t\geq2$ when $\beta\leq k$, even at degree cap four. For one intact round the exact worst-case time is determined at every cycle rank.
- **One intact round.** The exact value is $1$ for $d=1$ and $1+3k$ for $d=2,3$. For $d\geq4$ one loss gives $5$. For $d\geq4$ and $k\geq2$, put $U=1+\lfloor kd/2\rfloor+2k$. The exact value is $U$ for even $k$ and for $d=4,5$. For odd $k$ it is $U-1$ at $d=6$, and $U-2+(d\bmod2)$ at $d\geq7$.
- **Joint degree and cycle rank.** For one intact round the exact maximum is determined jointly for every degree cap at least three, cycle rank, and loss budget.
- **Two intact rounds.** At degree three, $2+7k\leq M_{3,2,k}\leq 2+9k$ and $M_{3,2,1}=9$. At degree four, $M_{4,2,k}=2+13k$. For one loss, the exact maximum at positive cycle rank is $\lfloor(\beta+19)/2\rfloor$.
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

The script replays the full arrival sequence of the low-rank constructions and the contracted trails on five branched trees attaining the forest bound, on the cyclic degree-three construction with up to 32 designated lost seeds, and on the one-round constructions at prescribed cycle rank and degree cap. It exhausts losses through the budget on the degree-two examples, on the small cycle-rank constructions with one or two losses, and on the smallest protected two-loss example. It checks the cycle upper bound through cycle order eleven for up to three losses, and the subcubic one-round upper bound on every labeled simple graph through order five. It also checks the exact local arrival rounds of the degree-three construction and seven higher-degree concatenated examples. On the larger protected graphs it checks designated losses, restricted deadlines, the killing loss and samples of clustered and mixed deletions. The proofs above give the guarantees for arbitrary budgets.
