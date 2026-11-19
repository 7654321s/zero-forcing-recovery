# Independent groups of deleted seeds

Fix a finite simple graph $G$ and an initial seed set $S$ that colors the graph in $t$ parallel zero forcing rounds. A force uses a blue source with exactly one white neighbor at the start of a round. For any deletion $D\subseteq S$, the arrival time of every vertex can be reconstructed from separate simulations of connected groups of deleted seeds. The same groups determine the worst completion time and whether recovery can fail. For the standard parallel propagation-time convention, see [Hogben and coauthors](https://arxiv.org/abs/1410.4191).

## The seed contact graph

Write $a(v)$ for the intact arrival time of vertex $v$. For each nonseed $v$, choose any source $u$ that forces it in its intact arrival round. Call $u$ and its neighbors other than $v$ the prerequisites of this chosen force. Every prerequisite has intact arrival strictly before $a(v)$.

Define $A(v)$ to be the set of seed ancestors obtained by following these prerequisites. In particular $A(s)=\{s\}$ for a seed $s$. For each seed $s$ let $R_s=\{v:s\in A(v)\}$. Two distinct seeds are joined in the contact graph if their regions intersect or some pair of vertices from their regions has graph distance at most two.

If $A(v)\cap D$ is empty, the loss of $D$ leaves the arrival time of $v$ unchanged. Induct on $a(v)$. For a seed this is immediate. For a nonseed, all prerequisites have unchanged arrivals by the induction hypothesis. The chosen force can therefore act by the intact round if the target is still white. Removing seeds can only delay an arrival, by monotonicity of each parallel update, so the time is $a(v)$.

## Exact reconstruction

Let $D_1,\ldots,D_r$ be the components induced by $D$ in the seed contact graph. For each component write $U_i=\bigcup_{s\in D_i}R_s$. The regions $U_i$ are disjoint and at pairwise distance more than two. Under deletion of $D$, every vertex outside their union follows its intact trace. On $U_i$, its trace under deletion of $D$ agrees at every round with its trace under deletion of $D_i$ alone.

At round zero, the two runs have identical colors inside $U_i$. An update at a vertex of $U_i$ depends only on the previous colors at distance at most two, since a source and all its neighbors lie within that distance of the target. This neighborhood does not reach any other $U_j$. Vertices there outside $U_i$ follow the same intact trace in both runs. An induction on the rounds proves the agreement, including vertices that remain white forever.

Consequently the completion time after deleting $D$ is the maximum of the intact time and the completion times after the separate component deletions, with a failed recovery treated as infinite time. The factorization also gives the individual vertex arrivals. In particular every inclusion-minimal blocking set is connected in the contact graph. For an at-most-$b$ deadline test it suffices to check the empty deletion and connected deletions of size at most $b$.

## A bounded-degree search

Every prerequisite is within graph distance two of its target. Hence $R_s$ lies inside the ball of radius $2t$ about $s$, and contacting seeds are at distance at most $4t+2$ in $G$. At maximum degree $\Delta\geq2$, the degree $d$ of the contact graph is at most $M(\Delta,4t+2)-1$, using the [ball count](HIGH_GIRTH_COVERS.md#the-fort-charging-bound).

For a connected set of $j$ seeds, choose a root and a rooted spanning tree of the set. Encode its depth-first traversal by $j-1$ forward moves and $j-1$ returns, with at most $d$ choices per forward move. The number of connected $j$-sets is at most $|S|\max(1,4d)^{j-1}$. An enumeration can avoid repeated sets by choosing their least seed as root and extending a frontier. Once a branch skips a frontier seed, it excludes that seed from the rest of the branch. Every connected set can be reached, since until it is complete there is a frontier edge to some remaining member. Each next choice must be the first available frontier member of that set.

Testing all such sets by ordinary propagation gives a fixed-parameter algorithm for blocking and deadline decisions in $(b,\Delta,t)$. An array of white-neighbor counts and a queue for the successive waves give a linear-time propagation replay per tested set. One can also restrict a replay to $U_i$ and its distance-two neighborhood, assigning all boundary colors from their intact arrivals. There are at most $|D_i|M(\Delta,2t)$ vertices in $U_i$. The equivalence of the region replay follows from the same two-neighborhood induction.

## Reproduction

```sh
python -B research-twins/check_loss_components.py
```

The verifier compares 4,104 complete arrival traces, including 650 deletions with more than one component. It enumerates all four-vertex graphs and their forcing seed sets, and also checks a path and a signed cyclic prism cover. For the exhaustive cases and the path, it verifies the connected-set enumeration by comparison with the full list of candidate deletions.

With the source choices in the verifier, the 350-vertex signed cover has 210 seeds and 106,337 connected three-seed deletions, out of 1,521,520 triples. A deadline test at budget three also checks the empty case and connected deletions of sizes one and two.
