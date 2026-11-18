# 初始信息失效下的零强制传播

本项目给出 EveryMinimumSupport 性质的完整有限树分类，并提供 Lean 证明与独立有限实验。满足该性质的树恰为非空路径、星形，以及两个中心各至少带两片叶子的双星。数学原创性尚未确认。

## 模型与定理

初始蓝点集合记为 B。失效使 B 中选定的点变白，图的顶点和边保留。这些点以后仍可染蓝。每轮同时执行轮初满足条件的标准零强制：蓝点有且只有一个白色邻点时，将该邻点染蓝。不能完成的传播时间为无穷。

致败集合 H 满足 H⊆B，且 B∖H 不能完成传播。“最小”指点数最少。EveryMinimumSupport 要求：任取可完成传播的 B、任取最小致败 H、任取预算 k 和截止轮数 T，以下两个条件等价：

- B 中任意至多 k 个点失效后，都能在 T 轮内完成。
- H 中任意至多 k 个点失效后，都能在 T 轮内完成。

对任意有限树 G，上述性质成立，当且仅当 G 属于以下类别之一：

- 非空路径，包含单顶点和单边。
- 至少有两片叶子的星形。
- 两个中心各至少带两片叶子的双星。

Lean 入口为 [formalization-full-tree-classification.lean](formalization-full-tree-classification.lean) 中的 `finite_tree_everyMinimumSupport_classification`。全称陈述为 `full_tree_classification_statement`。定义见 [formalization-targets.lean](formalization-targets.lean)，候选类定义见 [formalization-tree-target.lean](formalization-tree-target.lean)。证明结构与反例入口见 [THEOREMS.md](THEOREMS.md)。

## 构建与检查

依赖为 Lean 4.35.0、Python 3.10 以上版本，以及固定提交的 Mathlib。Mathlib 提交为 `56a005855ea17e0b0958f73ec801ae140b0a1679`，所有依赖提交保存在 `lake-manifest.json`。

安装 [Elan](https://github.com/leanprover/elan) 后，在仓库根目录运行：

```text
lake update
lake exe cache get
python scripts/run_checks.py
```

Windows 可将 `python` 换为 `py -3`。统一命令检查发布文件摘要，执行 `lake --wfail build`、公理审计、三个独立实验、文献指标反例检查及定理类型读回。每次运行的日志和汇总保存在 `build/checks`；任一步失败都返回非零退出码。各脚本仍可单独运行。

依赖缓存由 `lake exe cache get` 获取。源码清单包含 71 个证明模块，审计清单包含 511 个具名定理和辅助引理。引理数量不代表独立研究成果数量。已有项目编译产物时会记录复用情况；全新源码构建请使用全新解压目录。

审计脚本检查源码摘要、声明清单和公理依赖。允许的公理为 `propext`、`Classical.choice` 和 `Quot.sound`。输出保存在 `build/audit`。当前核验环境、源码摘要和结果见 [verification/verified-snapshot.json](verification/verified-snapshot.json)。其他操作系统的实际构建状态需分别确认。

源码采用 Lean 的 module 格式。逐文件的模块头转换记录见 `verification/module-header-migration.json`；转换保留定理和定义正文。部分源码保留早期阶段的注释，当前核验状态由 `verification` 中的记录给出。

v1.0.1 合入已完成的文献补核和模型自查，并增加统一命令与 GitHub Actions 配置，见 [CHANGELOG.md](CHANGELOG.md) 和 [CI.md](CI.md)。71 个证明模块与 v1.0.0 逐字节相同。固定的 verification 快照记录公开发布前的本地核验；对应提交的 Linux、Windows 实际运行结果见 [GitHub Actions](https://github.com/7654321s/zero-forcing-recovery/actions)。

## 独立实验

三个 Python 脚本只使用标准库。`experiment.py` 复现三个长分支反例，`one_short_experiment.py` 检查 124 组单短分支构造。`classification_experiment.py` 检查 1～9 个顶点的 95 棵非同构树，结果全部符合分类，其中 21 棵满足该性质。

分类实验按定义计算同步传播，正例检查全部初始强制集、最小致败集合及相关预算，反例在找到具体见证后停止。最小致败集合的点数为 m 时，预算至少为 m 的两种最坏时间都为无穷，因此只需另查小于 m 的预算。有限实验用于复核构造和定义；完整分类由一般 Lean 证明给出。

## 引用与许可证

初始信息失效模型、最坏一次失效传播时间、fort 静态理论和多种计算实现已有前人工作。[REFERENCES.md](REFERENCES.md) 列出相关文献、公开实现与比较范围。当前没有原创性或优先权声明。

项目源码与说明采用 [MIT 许可证](LICENSE)。Lean、Mathlib 及其依赖保留各自许可证，见 [THIRD_PARTY.md](THIRD_PARTY.md)。发布包不包含编译器、依赖缓存、浏览器数据或研究历史。
