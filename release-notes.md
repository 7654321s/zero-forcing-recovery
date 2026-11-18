EveryMinimumSupport 的完整有限树分类，以及可编译的 Lean 证明、独立实验和量词比较补充。

- 主源码包含 71 个证明模块、511 个具名声明。模型使用标准同步零强制；失效只改变初始颜色，顶点和边继续保留。
- 分类覆盖所有初始强制集、最小致败集合、失效预算和截止轮数。结论为非空路径、星及两侧各至少有两个叶子的双星。
- 工具链固定为 Lean 4.35.0，Mathlib 固定提交为 56a005855ea17e0b0958f73ec801ae140b0a1679。公理审计只允许 propext、Classical.choice 和 Quot.sound。
- 独立实验包含 3 个长分支样例、124 组单短分支构造、95 棵小树，其中 21 棵满足分类性质。
- 量词比较补充包含另外 5 个已编译引理和 9 点树反例。5 个补充引理与主源码的 511 个声明分开计数。

下载与复现：

1. 日常阅读和构建使用 zero-forcing-recovery-v1.0.1-published-source.zip，或 GitHub 自动提供的 Source code。解压后运行 `python scripts/run_checks.py`。
2. 20261117-zero-forcing-recovery-v1.0.1-source.zip 是原样保留的本地核验快照，SHA-256 为 7b439d83ec3efdca5dd4a0a5a2455cf18e75e6117fbca3112d7ef91a22b61514。量词补充的引导程序使用这个固定基包。
3. 20261117-zero-forcing-quantifier-comparison.zip 包含量词比较源码和复现入口。
4. 20261117-quantifier-bootstrap-recovery.zip 保存同机新基库的成功恢复回执及先前失败记录。
5. ci-verification-v1.0.1.zip 和 ci-verification.json 保存本次发布提交在 GitHub Linux、Windows 上的真实核验结果；SHA256SUMS 校验全部下载附件。

公开源码相对原本地快照更新了发布状态说明和 Windows CI 的 Elan 原生路径传递。71 个证明模块保持逐字节一致。仓库 verification 中的本地快照记录保留核验当时的状态，云端结果以本次提交的 Actions 和发布附件为准。

已完成形式化证明和所列实验。数学优先权仍未确认；真实第三方人工审阅尚未完成。已有结论的归属和比较范围见 REFERENCES.md 与 review/LITERATURE.md。源码采用 MIT 许可证，第三方依赖沿用各自许可证。
