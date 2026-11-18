# 相关文献与开源实现

## 直接相关文献

- Asher Brown、Mark Hunnell、Za'Kiyah Toomer-Sanders、Via Weber，[Fault Tolerant Zero Forcing](https://arxiv.org/abs/2509.07854)。初始蓝色信息失效模型属于已有定义。特别保留 [v1](https://arxiv.org/html/2509.07854v1) 第 5 节的失效传播时间定义与结果，避免只引用修订版而漏引旧结果。
- Daniela Ferrero、H. Tracy Hall、Leslie Hogben、Mark Hunnell、Ben Small，[Zero forcing propagation time intervals and graphs with fixed propagation time](https://arxiv.org/abs/2511.16335)。局部两白点的时间比较应与引理 5.1 对照；本项目不把叶子与父点的这一计时事实作为新贡献。
- Thomas R. Cameron、Kelvin Li，[On the minimal forts of trees](https://arxiv.org/abs/2512.12874)。树中极小 fort 的结构属于相关静态理论。
- Bonnie Jacob，[Well-failed graphs](https://arxiv.org/abs/2501.19357)。研究所有极小 fort 都是点数最少的 fort 的性质，并给出相应树分类。本项目的预算化时间性质需要单独比较。

## 公开实现

- [hunnellm/fault-tolerant](https://github.com/hunnellm/fault-tolerant)：已有失效零强制与一次失效传播时间计算。
- [trcameron/ZFIPModels](https://github.com/trcameron/ZFIPModels)：零强制、fort、传播时间与 throttling 的整数规划模型。
- [JakeMitton/PropTimeZF](https://github.com/JakeMitton/PropTimeZF)：零强制传播时间算法。

上述项目用于相关工作比较，本仓库的有限实验没有复制这些项目的代码。

## 查重范围

2026 年 11 月 17 日的查重包括以上文献，以及部分 GitHub 仓库的 README 和选定源码。所查范围内尚未找到完整解决当前时间性质树分类的结果。检索没有穷尽所有推论、所有代码分支或未公开工作，不能据此认定原创性。

期刊论文 [Zero forcing number and propagation time discrepancy of some graphs](https://toc.ui.ac.ir/article_29916_b1eab7c1830353945107c6d0aa8251d0.pdf) 的全文比较现已补齐。其传播时间差值在点数最少的零强制集之间取极值，见印刷页 216～217；与本项目遍历所有 B、H 和失效预算的性质不同。

原文定理 4.1 对等长 star-like trees 给出差值为 0。St(2,2,2) 上，本项目的 EveryMinimumSupport 却不成立：B={1,3,4,5,6}、H={4,6}，预算为 1 时全局最坏时间为 3、限制于 H 时为 2。顶点与边编号、独立复核命令和比较边界见 [review/LITERATURE.md](review/LITERATURE.md)。这个例子区分两种性质，不确认数学优先权。

## 完整分类后的复核

2026 年 11 月 17 日再次核对了 [Fault Tolerant Zero Forcing 的 v1](https://arxiv.org/html/2509.07854v1) 和 [同一记录的 v4](https://arxiv.org/html/2509.07854v4)。v1 第 5 节已定义失效后的最坏一次失效传播时间；v4 给出失效零强制数的树理论。初始信息失效模型及最坏一次失效计时保留为已有工作。

[Well-failed graphs](https://arxiv.org/html/2501.19357) 研究所有极小 fort 是否都是点数最少的 fort，并在定理 3.15 分类相应的树。其路径名单不含 P₅，而本项目时间性质包含所有非空路径。这个比较说明两种性质不相同；不据此推断本项目结论没有已有推论。

再次读取了 [hunnellm/fault-tolerant 的 ft_propagation.py](https://github.com/hunnellm/fault-tolerant/blob/main/ft_propagation.py)。该模块实现传播时间及逐个移除初始点后的最坏时间。本次读取范围没有给出本项目量化所有 B、最小致败 H、预算 k 和截止轮数 T 的树分类。没有复制其源码。

完整 Lean 分类证明与数学优先权分开记录。上述有限比较及关键词检索没有排除所有已有推论、其他分支和未公开结果，原创性仍未确认。
