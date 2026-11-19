# High-girth covers and fault-tolerant zero forcing

For each fault budget $f\geq 0$, each block count $k\geq 1$, and each prescribed minimum girth, there is a finite three-vertex-connected cubic bipartite graph with a seed set that completes in exactly two parallel rounds. Every loss of at most $f$ seeds still permits recovery. One designated deletion of a union of $k$ seed fibers completes in exactly $6k+2$ rounds. The construction lifts the existing prism-chain waves through mod-two homology covers.

## From fort size to the number of failed seeds

Let $G$ be a finite simple graph of girth $g$, minimum degree $\delta\geq 3$, and maximum degree $\Delta$. Let $S$ be a seed set completing in $t$ parallel rounds. Write $\kappa(G,S)$ for the smallest number of seeds whose loss prevents full recovery. Set
$$
R=\left\lfloor\frac{g-1}{4}\right\rfloor,
\qquad
Q=\left\lfloor\frac{g-3}{4}\right\rfloor,
\qquad
M(\Delta,2t)=1+\Delta\sum_{i=0}^{2t-1}(\Delta-1)^i.
$$
Then
$$
\kappa(G,S)\geq
\left\lceil
\frac{\max\{1+\delta\sum_{i=0}^{R-1}(\delta-1)^i,\ 2\sum_{i=0}^{Q}(\delta-1)^i\}}
     {M(\Delta,2t)}
\right\rceil.
$$
Empty sums are zero. For cubic graphs with $t=2$, the denominator is $46$ and the numerator is at least $3\cdot 2^R-2$. Thus the guaranteed fault budget grows exponentially in $g$ along the cover sequence.

**Fort size.** A fort is a nonempty set $F$ such that each vertex outside $F$ has either zero or at least two neighbors in $F$. Form a subgraph with the edges that have at least one endpoint in $F$. A vertex in $F$ has at least $\delta$ incident edges in this subgraph. Every outside vertex reached by such an edge can continue to another vertex of $F$. Start at a vertex of $F$. Take each outgoing edge and, if it reaches an outside vertex, extend it by one edge back into $F$. This gives $\delta$ branches of length at most two. At each subsequent vertex in $F$, repeat while excluding the incoming edge. The resulting walks are nonbacktracking, and each vertex after the root gives at least $\delta-1$ branches. After $R$ branching steps each walk has length at most $2R$. Their endpoints are distinct, including across different depths, since two different such walks from the root that end at the same vertex would give a cycle of length at most $4R<g$. Counting the root and the endpoints proves the first fort-size bound.

For the second bound, take two vertices of $F$ joined by a path of length at most two whose interior, if present, is outside $F$. Such a path comes from any edge leaving a fort vertex, extending once if needed. Grow branches from both endpoints, excluding the first edge toward the other endpoint at each root. Each root now has at least $\delta-1$ branches. Count both trees to depth $Q$. An endpoint coincidence across the two trees would give a cycle of length at most $4Q+2<g$, by using the original path between their roots. Within each tree the previous argument still applies. This proves the second bound. The branching argument is related to the tree bound for stopping sets of a Tanner graph. [Orlitsky, Urbanke, Viswanathan and Zhang](https://doi.org/10.1109/ISIT.2002.1023274)

**Seed loss.** The final white set after a blocking deletion is a fort. More generally, for any fort $F$, the initial set $S\setminus F$ leaves every vertex of $F$ white. One parallel round depends on the previous colors at graph distance at most two, since a force inspects its source and all neighbors of the source. After $t$ rounds every vertex of $F$ therefore lies within distance $2t$ of some seed in $S\cap F$. Each such graph ball contains at most $M(\Delta,2t)$ vertices. Divide the fort-size bound by this maximum ball size and round up. This applies to every fort, and the minimum seed intersection of a fort equals $\kappa(G,S)$.

## The cover and its connectivity

Start with a finite connected graph and a spanning tree. If the cycle rank is $r$, assign an independent coordinate of $\mathbb F_2^r$ to each of the $r$ chords. The lift has one copy of every base vertex at each coordinate vector. A lifted tree edge preserves the vector, and a lifted chord toggles its coordinate. A walk around a fundamental cycle toggles the corresponding coordinate, so the lift is connected. This is the standard mod-two homology cover. [Arzhantseva, Guentner and Špakula](https://arxiv.org/abs/1101.1993)

A closed lifted walk projects to a closed walk traversing every chord an even number of times. The tree edges traversed an odd number of times would have even degree at every base vertex, which is impossible for a nonempty subgraph of the tree. Thus every base edge is traversed an even number of times, so the cover is bipartite. A lifted cycle projects to a nonbacktracking closed walk, which uses at least $g$ distinct base edges, each at least twice. Conversely, traversing a shortest base cycle twice lifts to a simple cycle of length $2g$. After the first traversal the vector has changed, and each base vertex on the cycle has a different lifted copy on the second traversal. The cover has exactly twice the base girth.

Suppose the base is three-edge-connected and $r\geq2$. For a nonempty proper set of lifted vertices $X$, let $a_u$ count its members above each base vertex $u$. The lifted matching over an edge $uv$ has at least $|a_u-a_v|$ edges across the cut of $X$. If the counts are nonconstant, choose a threshold that separates the base into two nonempty parts. At least three base edges cross that threshold, so at least three lifted edges cross the cut. If the counts are constant, the crossing count of each lifted matching is even. A cut of size two would therefore use only edges above a single base edge $e$.

The base graph with $e$ removed is connected. Its closed-walk voltages form a codimension-one subspace of the full cycle space, since the binary cycle vectors with zero $e$-coordinate have dimension $r-1$. In spanning-tree coordinates, the chord parities identify the binary cycle space with $\mathbb F_2^r$. Each component of the lift with the entire fiber of $e$ removed meets the fiber over any fixed root. Its intersection with that root fiber is a coset of the closed-walk voltage subspace. Thus there are exactly two components. Each lifted copy of $e$ joins different components, because an alternative path within one component would close a walk traversing $e$ once. A cut using only this matching must then cut all $2^r$ copies, so the cover is three-edge-connected.

In a simple cubic graph, three-edge-connectivity implies three-vertex-connectivity. A cut vertex would leave a component attached by at most one edge. If deleting two vertices disconnects the graph, each resulting component needs at least three attachment edges. There must be exactly two components with three edges each, and the deleted vertices are nonadjacent. If either deleted vertex sends all three edges to one component, the other deleted vertex sends all three to the other component, contradicting connectivity. In particular one deleted vertex sends two edges to one component. Including that vertex with that component gives a two-edge cut. This excludes every two-vertex separator.

## Lifting the delay

For $k=1$, start with the existing sixteen-vertex cubic certificate, and for $k\geq2$ start with the unpadded cubic prism chain. These are [three-connected certificates with intact time two and designated delay $6k+2$](MULTIPLE_LOSS_TIMING.md). In a cover, for any starting coloring constant on each fiber, the parallel updates are exactly the pullbacks of those on the base. The local bijection preserves the color at each corresponding neighbor. This holds for the intact coloring and for the coloring obtained by deleting all copies of the $k$ designated seeds. It preserves both exact times.

Each iteration of the cover keeps the graph cubic and three-connected, makes it bipartite, and doubles its girth. With maximum degree three and intact time two, the bound above eventually exceeds any given $f$. For example, girth at least $36$ guarantees recovery after any twenty-two seed losses, since $Q\geq8$ gives $\lceil(2\sum_{i=0}^8 2^i)/46\rceil=23$ from the two-root bound. The designated deletion always refers to entire fibers. Its size is the block count times the total cover degree.

## Reproduction

```sh
python -B research-twins/check_high_girth_covers.py
```

The script builds the 8,192-vertex first homology cover of the sixteen-vertex certificate. It checks girth six, every local neighbor bijection, intact time two, and all eight waves after the designated 512-seed deletion. It also checks three-edge-connectivity directly in the 32-vertex cover of $K_4$ and enumerates small forts in $K_4$ and the Heawood graph to check the two fort bounds. The proof gives the unbounded cover sequence. The explicit verifier constructs one iteration of the delay certificate.
