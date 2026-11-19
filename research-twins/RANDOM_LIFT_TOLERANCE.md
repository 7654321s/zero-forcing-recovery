# Linear fault tolerance in random lifts of delay certificates

For each fixed cubic bipartite delay certificate with intact time two, a uniform random $n$-sheet lift has a minimum seed blocking size of order $n$ with probability tending to one. The intact time stays two and the designated deletion retains its exact propagation waves. In particular the existing certificates give three-vertex-connected cubic bipartite examples with linear fault tolerance and designated propagation time $6k+2$ for every fixed $k\geq1$ and every sufficiently large sheet count.

More quantitatively, let $G$ be a simple three-edge-connected cubic base of order $N$ with a seed set completing in $t$ rounds. Set $D=5e$ and $\alpha=1/(D\cdot24^5)$. With probability at least $1-O(N/n)$ its $n$-sheet lift is three-vertex-connected and has blocking number greater than
$$
\frac{2\alpha n}{5 M(3,t)},\qquad
M(3,t)=3\cdot 2^t-2.
$$
The constant in the probability estimate is absolute. Thus at $t=2$ every loss of at most $\lfloor\alpha n/25\rfloor$ seeds permits recovery on that event. For a fixed base, this is also a constant fraction of the lifted vertex count.

## A small fort would produce a dense subgraph

A nonempty fort $F$ has the property that each outside vertex has zero or at least two neighbors in it. Write $f=|F|$ and $b=|N(F)\setminus F|$, and let $U$ consist of $F$ and those $b$ neighbors. Keep the edges that meet $F$. If $e_{\rm out}$ is the number of edges leaving $F$, then $2b\leq e_{\rm out}\leq 3f$ and the retained subgraph on $U$ has at least
$$
\frac{3f+e_{\rm out}}{2}\geq\frac32 f+b\geq\frac65 |U|
$$
edges. Also $|U|\leq5f/2$. If the retained subgraph is disconnected, at least one of its components has edge count at least $6/5$ times its vertex count, by averaging. Bounds of this type are related to bounds on stopping sets in random Tanner graphs. [Orlitsky, Viswanathan and Zhang](https://doi.org/10.1109/TIT.2004.842571)

## Small connected sets in the random lift

Use one independent uniform matching between the two $n$-vertex fibers over each base edge. The edges at any lift vertex can be specified by their base incidences. For each connected $h$-vertex set, choose a rooted spanning tree and traverse it in depth-first order. Describe each walk step by a tree descent with one of at most three base incidences, or a return along the tree edge. For a fixed root the possible descriptions number at most $12^{h-1}$. There are $h-1$ descents and $h-1$ returns, with at most $4^{h-1}$ choices for their order and at most $3^{h-1}$ incidence choices. The root itself has $Nn$ possibilities.

For a fixed description, explore the matchings only as the descents require. Discard the description if a descent reaches an already visited vertex. Conditional on a successful exploration transcript, precisely the $h-1$ tree edges have been exposed and the remaining matchings are independent uniform completions. To reach edge count $\lceil6h/5\rceil$, the explored set must have at least
$$
\ell=\lceil 6h/5\rceil-(h-1)=1+\lceil h/5\rceil
$$
more edges. For any prescribed list of $\ell$ distinct non-tree pairs, inconsistent prescriptions have probability zero. For a consistent list, each successive prescribed match has conditional probability at most $1/(n-h-\ell+2)$. The denominator is at least $n/2$ for $h\leq\alpha n$. The probability of a dense connected set of size $h$ is at most
$$
Nn\,12^{h-1}\binom{\binom h2}{\ell}(2/n)^\ell
\leq Nn\,12^{h-1}(D h/n)^\ell.
$$
Sets of size at most three cannot have the required density in a simple graph. For $h=4,5$ the displayed bound is $O(N/n)$ because $\ell=2$. For $h\geq6$ it is at most
$$
NDh\,[12(Dh/n)^{1/5}]^h.
$$
For $6\leq h\leq n^{1/10}$ the factor in brackets is at most $12D^{1/5}n^{-9/50}$, and the sum is $O(Nn^{-54/50})$. For $n^{1/10}<h\leq\alpha n$ the bracket is at most $1/2$, giving an exponentially small tail after factoring out $N$. This proves a total failure probability $O(N/n)$ with an absolute constant.

Consequently, on the complementary event every fort has more than $(2/5)\alpha n$ vertices. The [fort charging bound](HIGH_GIRTH_COVERS.md#the-fort-charging-bound) shows that a fort can occupy at most $M(3,t)$ vertices per seed in it. Thus the minimum seed intersection of a fort is greater than $2\alpha n/(5M(3,t))$, as claimed. Losing all lifted seeds gives the upper bound $n|S|$, so the asymptotic order for a fixed base is linear.

## Connectivity and propagation

Fix a base edge $uv$. The base graph without it is connected, and its cycle rank is $N/2\geq2$. Relabel the lifted fibers along a spanning tree so that its matchings are the identity. Conditional on the tree matchings, the remaining $j=N/2$ chord matchings act as independent uniform permutations. The lift of the edge-deleted base is connected if these permutations generate a transitive action. If they do not, a common invariant set can be chosen of size $1\leq s\leq n/2$. A fixed $s$-set is preserved by each permutation with probability $1/\binom ns$. Union over the $s$-sets and then over the sizes to bound failure by $\sum_{1\leq s\leq n/2}\binom ns^{1-j}=O(1/n)$. The term $s=1$ is at most $1/n$, and the remaining terms are at most $1/\binom n2$ each. One more union over the $3N/2$ base edges gives a failure probability of $O(N/n)$. For general results on the connectivity of random graph lifts, see the papers of [Amit and Linial](https://doi.org/10.1007/s004930200000) and [Silas](https://doi.org/10.37236/6639).

If deleting any one edge fiber leaves the lift connected, a cut of size at most two is impossible. Unequal counts of cut-side vertices over base fibers force at least three crossing edges, by applying a threshold to the fiber counts and using base edge connectivity. Equal fiber counts make the number of crossing edges even in every lifted matching. A cut of size two would therefore be contained in one edge fiber. For cubic simple graphs, [three-edge-connectivity implies three-vertex-connectivity](HIGH_GIRTH_COVERS.md#the-cover-and-its-connectivity). A bipartite base supplies the lifted bipartition.

In a fiber-constant coloring each force is preserved by the local neighbor bijection. Use the [existing bipartite chain](MULTIPLE_LOSS_TIMING.md#bipartite-chains-tolerating-any-three-seed-losses), whose intact time is two and whose designated deletion takes $6k+2$ rounds. Both times and the designated wave lengths lift exactly. The designated deletion includes all copies of the selected base seeds. The estimate is uniform over these bases. Since the bipartite base has $N=26k+O(1)$ vertices, for any budget $f$ choose $n$ with $n\geq C N$ and $\alpha n/25\geq f$, where $C$ is a sufficiently large absolute constant. A lift satisfying the connectivity and loss bounds then exists. This gives a graph of order $O(k(k+f))$ with intact time two, tolerance of $f$ losses, and designated time $6k+2$. Taking $n$ proportional to $N$ yields a sequence with both guaranteed loss tolerance and designated completion time of order at least the square root of the number of vertices.

## Reproduction

```sh
python -B research-twins/check_random_lift_tolerance.py
python -B research-twins/check_random_lift_tolerance.py --certify-eleven-losses
```

The first command builds a reproducible 420-vertex lift with seven sheets, checks exact timing and connectivity, and verifies cubic equality examples for the fort charging bound at deadlines one through four. The sample completes in two rounds intact and fourteen rounds after a designated 28-seed deletion. The optional PySAT command checks that every loss of at most eleven seeds in that finite sample permits recovery. The linear asymptotic guarantee follows from the counting proof above.
