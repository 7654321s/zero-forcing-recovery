# 完整有限树分类与证明入口

## 定理

对任意有限树 G，EveryMinimumSupport 当且仅当 G 是非空路径、星形，或两个中心各至少带两片叶子的双星。星形在规范表示中至少有两片叶子；更小的图归入路径。

该性质同时量化所有初始强制集 B、所有点数最少的致败集合 H、所有失效预算 k 和所有截止轮数 T。失效后的顶点与边保留，同步轮数按轮初状态计算。

主定理为 `FaultObservationResearch.finite_tree_everyMinimumSupport_classification`。`full_tree_classification_statement` 证明全称目标 `FullTreeClassificationStatement`。两者位于 `formalization-full-tree-classification.lean`。

## 正向类别

路径上的任意初始强制集满足该性质。星形及上述双星的全部最小致败集合也保留所有预算下的最坏完成时间。图同构传输把规范模型结论用于任意顶点标签。

| 结论 | 主要模块 |
| --- | --- |
| 路径的全部预算性质 | `formalization-path-support.lean` |
| 双星的完整目标 | `formalization-double-star-complete.lean` |
| 规范类别与同构传输 | `formalization-tree-target.lean` |

## 其余树的排除

含同中心叶子对的有限树，若满足该性质，就必须是上述星形或双星。至多有一个分叉点的剩余情形，由长分支与单短分支反例排除，最终得到该范围的完整分类。

对于无同中心叶子对、且至少有两个分叉点的树，选两个分叉点之间最长的简单路径。两端的每个外侧删点连通分支都是以附着点为端点的非空路径，每端至少有两个这样的分支。

把两端分支按长度排序。每端的两条最短路径与另一端的两条最长路径，分别用于严格时间差比较。若严格比较出现，就得到原树上的反例。若严格比较都不出现，算术穷尽迫使两端各有两条路径，长度均为 `[1, L]`，其中 L≥2。全部长度为 1 的情形会形成同中心叶子对。

若两个中心不相邻，等长模型给出反例。若相邻，移除四条路径后的核心仍然连通，两个中心在核心中互为唯一邻点。故核心只有两个顶点，原图同构为已核验的相邻等长模型，该模型同样给出反例。

| 论证 | 模块或定理 |
| --- | --- |
| 含同中心叶子对的分类 | `formalization-tree-cherry-canonical.lean` |
| 至多一个分叉点的分类 | `finite_at_most_one_branch_tree_classification` |
| 最长分叉路径与外侧分支 | `formalization-tree-branch-diameter.lean` |
| 原图双中心分解及指定长度 | `formalization-tree-two-center-realization.lean` |
| 严格时间差、等长且中心不相邻 | `formalization-tree-two-center-obstruction.lean` |
| 排序与极值分支穷尽 | `formalization-tree-terminal-sort.lean`、`formalization-tree-terminal-exhaustion.lean` |
| 相邻中心的二顶点核心 | `formalization-tree-adjacent-core.lean` |
| 相邻等长反例 | `formalization-adjacent-equal.lean` |
| 分类合并 | `formalization-full-tree-classification.lean` |

## 已有反例的复核

长分支反例在至少三条分支、每条长度至少为 2 的蜘蛛树上构造点数最少的致败集合 H，大小为 2。只在 H 内失效一次时，最坏时间为最长分支长度 M；允许全部初始点失效一次时，最坏时间为 M+1。入口为 `pathStar_all_long_not_everyMinimumSupport`。

单短分支反例允许恰有一条分支长度为 1。入口为 `pathStar_one_short_deadline_gap` 和 `pathStar_one_short_not_everyMinimumSupport`。实验报告中的精确时间不作为额外一般定理声明。

## 核验与归属

`verification/expected-axioms.json` 列出全部 511 个具名声明的预期公理依赖。完整源码构建和公理审计的状态记录在 `verification` 中。图论分解工具与排序复用标准方法，数学原创性和优先权尚未确认。相关模型、静态 fort 分类与既有实现见 `REFERENCES.md`。
