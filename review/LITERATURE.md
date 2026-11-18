# 期刊全文比较

F. Kheyridoost、E. Vatandoost，《Zero forcing number and propagation time discrepancy of some graphs》，[期刊页面](https://toc.ui.ac.ir/article_29916.html)、[原文 PDF](https://toc.ui.ac.ir/article_29916_b1eab7c1830353945107c6d0aa8251d0.pdf)。DOI：10.22108/toc.2025.142214.2195。PDF 卷期为 15(3), 2026, 215–230；网页引文年份与 PDF 有差异。

2026 年 11 月 17 日已取得并通读 16 页全文，重点对读定义、主定理和相关证明，没有逐式重证原文。此前“全文比较缺口”的状态在本版本更新。原文 PDF 与全文文本未纳入源码包。

原文在点数最少的零强制集之间定义最小传播时间 Pt、最大传播时间 PT，以及差值 pd，见印刷页 216～217。定理 4.1 位于第 222 页，给出等长 star-like trees 的 pd=0。该优化对象与本项目的失效预算性质不同。

## 复核例子

取 St(2,2,2)，边集为 {(0,1),(1,2),(0,3),(3,4),(0,5),(5,6)}。枚举得到 9 个点数最少的零强制集，大小为 2，传播时间均为 4，所以 pd=0。

取 B={1,3,4,5,6}、H={4,6}。H 是点数最少的致败集合，大小为 2。预算为 1 时，全局最坏时间为 3，限制在 H 内的最坏时间为 2。截止轮数取 2 就能区分二者，因此 EveryMinimumSupport 不成立。

可在源码根目录运行 `python scripts/compare_discrepancy_predicate.py`，结果写入 build/paper-comparison.json。脚本复用本项目的传播模拟器，独立于 Lean 证明计算集合和时间。

这个例子说明 pd=0 不能推出 EveryMinimumSupport。它没有排除其他旧定理的推论，也不确认数学优先权。其他文献和开源实现的比较范围见 REFERENCES.md。
