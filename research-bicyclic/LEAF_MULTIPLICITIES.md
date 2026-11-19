# Reducing pendant leaf multiplicities to two

**Theorem.** Let $G$ be a finite nonempty simple graph. For each vertex $v$ of $G$, attach $m_v$ new leaves adjacent only to $v$. The resulting graph satisfies `EveryMinimumSupport` exactly when the graph with $\min(m_v,2)$ new leaves at each $v$ satisfies it. The reduction preserves the existence of a budget-one counterexample with a two-element minimum killing support and finite recovery under every singleton loss. It preserves the times of those certificates.

This statement uses the [initial-color loss model](../README.md#模型与定理). The fort criterion for zero forcing and the role of twin vertices in fault tolerance appear in [Vertex Fault Tolerant Zero Forcing](https://arxiv.org/html/2509.07854v4#S2).

The [general twin truncation theorem](../research-twins/RESEARCH.md) extends the timing argument to adjacent and nonadjacent twin classes anywhere in the graph.

## Why the reduction works

Write $G_2$ for the graph with truncated multiplicities and $G_m$ for the full graph. We view $G_2$ as an induced subgraph of $G_m$ by keeping two designated leaves in every group of at least two. A pair in any group with the same parent is a fort. If a forcing blue set omits one leaf of such a group, then removing another blue leaf from it kills. Omitting two would already make the original coloring fail. Hence every blue set that survives all singleton losses contains every leaf in each group with at least two. If there is no such group, the two graphs are identical.

For a blue set that fails under some singleton loss, every minimum killing support has size one. Budget zero compares the intact run, and at larger budgets both comparison domains allow the whole support to be removed. For a set that survives all singleton losses, any group of at least two leaves supplies a killing pair, so the minimum killing size is two. Again, the only budget to examine is one. Thus we can work with blue sets that contain all the leaves of the repeated groups, and consider intact, singleton and double-loss states.

Consider such a blue set in $G_2$ and its extension to $G_m$ with all extra leaves blue. Suppose a loss removes at most one of the two retained leaves from each repeated group. At least one retained blue leaf then remains in every repeated group. A parent that starts white is restored by such a leaf in round one. All extra leaves stay blue and can only force their parents, so the extra leaves cannot create a force into an old vertex any earlier. Existing vertices have the same white-neighbor counts on both sides at round zero. From round one onward all parents of repeated groups are blue. Induction on the rounds gives identical colorings on $G_2$ throughout, so the completion times agree, including failure to complete.

This projection applies to the intact coloring and to every singleton loss at a retained vertex. A singleton loss at an extra leaf has the same time as a loss at a retained sibling, by the automorphism swapping the two. The initial blue set contains both leaves, so this swap leaves the set unchanged before the loss. Hence singleton tolerance and all distinct singleton times correspond under the reduction. In particular, every singleton-tolerant set on either graph is the extension or restriction of such a set on the other graph.

Now compare killing pairs for these corresponding singleton-tolerant sets. A pair of siblings from one group kills on both graphs, and its two singleton times are the time of one representative leaf loss. A pair of any other kind can be moved into $G_2$ by permuting siblings in the repeated groups. This pair removes at most one retained leaf from each group, so the projection gives the same double-loss outcome. Conversely, each pair in $G_2$ is a pair of the same kind in $G_m$. Thus minimum supports correspond with the same restricted time. The unrestricted worst singleton time also agrees. Adding the intact run to either comparison gives the same budget-one deadline condition, proving the equivalence. The same argument transports any given two-element counterexample and its exact times.

## Direct leaves on the four positive bicyclic cores

Apply the theorem to each of the [four positive leafless bicyclic cores](NEARBY_FAMILIES.md#bicyclic-graphs-of-minimum-degree-two). Attach any number of direct leaves at any vertices of one core. The property holds exactly in the following cases.

- For two triangles sharing a vertex, all new leaves are at the shared vertex.
- For the diamond $\Theta(1,2,2)$, all new leaves are at its two degree-three vertices. One of those vertices has no new leaves, or both have at least two.
- For $\Theta(2,2,2)$ and $\Theta(2,2,3)$, no leaves are attached.

The positive cases follow from [the previous direct-leaf proofs](ATTACHMENTS.md#direct-leaves-at-the-two-positive-sites), [the two-sided diamond proof](NEARBY_FAMILIES.md#leaves-and-paths-on-a-diamond) and the unadorned core checks. For the exclusion, enumerate vectors with entries in $\{0,1,2\}$ on each core, keeping the lexicographically first vector under each core automorphism. The truncation of any attachment is one of these configurations up to relabeling. The finite check finds and replays a two-loss certificate in each of the 420 negative configurations. The reduction lifts each certificate to all larger multiplicities with the same truncation.

| Core | Compressed positive configurations | Compressed negative configurations |
| --- | ---: | ---: |
| Two triangles sharing a vertex | 3 | 60 |
| $\Theta(1,2,2)$ | 4 | 32 |
| $\Theta(2,2,2)$ | 1 | 59 |
| $\Theta(2,2,3)$ | 1 | 269 |

## Negative bicyclic cores through order eight

Let $G$ be a finite connected simple bicyclic graph of minimum degree at least two with at most eight vertices, and suppose $G$ is outside the four positive classes. Attaching any number of direct leaves at any vertices of $G$ still gives a negative graph. In fact every such attachment has a budget-one certificate with a two-element minimum killing support and finite recovery under every singleton loss.

The [bicyclic decomposition](NEARBY_FAMILIES.md#bicyclic-graphs-of-minimum-degree-two) lists the possible cores by sorted lengths. For each negative core through order eight, enumerate leaf counts in $\{0,1,2\}$ up to its automorphisms. The following counts give the verified scope. The checker constructs and replays a certificate for every row of the enumeration. Truncation then gives the result for unbounded leaf counts. Consequently the previous classification on the four positive cores also classifies all bicyclic graphs whose core has at most eight vertices and whose off-core vertices are direct leaves.

| Order of the core | Negative cores | Compressed configurations with certificates |
| ---: | ---: | ---: |
| 5 | 1 | 135 |
| 6 | 4 | 1,116 |
| 7 | 8 | 6,534 |
| 8 | 12 | 28,122 |
| **Total** | **25** | **35,907** |

## Reproduction

```sh
python -B research-bicyclic/check_leaf_multiplicities.py
```

On the four positive cores, the checker generates 429 compressed configurations, checks the nine positive configurations exhaustively, and searches for then verifies every negative certificate. It also increases the multiplicities in each applicable negative configuration on these cores and replays 363 enlarged certificates. On the negative cores through order eight, it generates and checks the further 35,907 certificates. The option `--max-negative-core-order` changes that finite search bound. In both parts the search uses the mandatory blue leaves of any repeated group. The reduction itself applies to any finite base graph.
