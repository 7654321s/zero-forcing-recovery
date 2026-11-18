# 模型与定理语义自查

执行者为 Codex，尚无真实第三方人工审阅结论。本文核对公开陈述与 Lean 定义的对应关系，独立人工审阅记录另行收集。

| 陈述 | 定义与结论 |
| --- | --- |
| 同步传播 | synchronousStep 中的所有强制条件读取同一个轮初 blue，colorAfter 每轮调用一次该步骤。 |
| 标准零强制 | source 必须是蓝点，其所有白邻点都等于 target；白色 target 因而是唯一白邻点。结果与 blue 取并集。 |
| 失效只改变初始颜色 | 过程使用同一个 adj，初始集变为 blue∖loss，图中顶点、边保留，失效点可重新染蓝。 |
| 点数最少的致败集合 | IsMinimumKilling 要求 H⊆B、B∖H 失败，且 B 中每个更小失效集都成功。IsMinimumKilling_iff_card_minimum 明确给出全局点数最少的等价式。 |
| 所有量词 | EveryMinimumSupport 遍历所有强制 B、所有点数最少致败 H、所有 budget 与 deadline，不要求 B 本身点数最少。 |
| 至多给定次数的失效 | allowedLosses 过滤 loss.card≤budget，包含空失效集。 |
| 无穷传播时间 | completionTime 在不能完成时等于 ℕ∞ 的 ⊤，worstTime 对全部允许失效取上确界。 |
| 截止表述与时间表述一致 | everyMinimumSupport_iff_worstTime 证明二者等价，保留全部 B、H 和预算。 |
| 任意有限树 | 最终分类定理使用 Fintype、DecidableEq 和 G.IsTree，没有额外分叉假设。Mathlib 的 Connected 要求非空。 |
| 小图边界 | InTreeCandidateClass 包含 n≥1 的路径、a≥2 的星形和 a,b≥2 的双星。P₁、P₂ 归入路径。 |

最终入口为 finite_tree_everyMinimumSupport_classification，以及证明全称目标的 full_tree_classification_statement。SpecificationReadback.lean 打印实际定义、定理类型及最终定理公理，不增加证明。统一检查命令执行该文件，输出保存在 specification.log。

511 个具名声明的公理允许范围是 propext、Classical.choice、Quot.sound。scripts/audit_axioms.py 对读源码摘要、声明清单和实际 Lean 输出。71 个证明模块与 v1.0.0 相同。

部分模块头保留早期“unproved target”注释，目标定义本身确实不是证明。最终模块已证明该目标，当前入口和核验范围见 README.md 与 verification 中的记录。语义自查、内核检查、人工审阅和数学优先权分别记录。
