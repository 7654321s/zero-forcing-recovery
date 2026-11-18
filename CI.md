# 自动核验

统一入口为 `python scripts/run_checks.py`。该命令检查发布文件和证明源码摘要，执行 Lean 构建、公理审计、有限实验、文献指标区别检查及实际定理类型读回。汇总与逐步日志保存在 build/checks 的独立时间目录。

## GitHub Actions

[verify.yml](.github/workflows/verify.yml) 在 push、pull_request 或手动触发时运行。矩阵包含 ubuntu-latest 和 windows-latest。两个系统的实际远端运行状态按提交记录在 [Actions 页面](https://github.com/7654321s/zero-forcing-recovery/actions)，本地核验快照单独保留。

工作流使用固定提交的 checkout、setup-python、[lean-action](https://github.com/leanprover/lean-action/tree/ba3fdfe5c4476c925da13bf11a005ddb47e47aee) 和 upload-artifact。Lean 与 Mathlib 的版本由 lean-toolchain、lakefile.lean 和 lake-manifest.json 指定。lean-action 使用其自身的 Elan 安装流程；固定外层 action 不代表其联网安装的全部工具也固定为同一提交。

工作流关闭 GitHub 的整个 .lake 缓存复用，保留 Mathlib 官方依赖缓存。新的 runner 上，项目证明应从源码构建。统一命令记录运行前已有项目 .olean 的数量；复用旧产物时不会将其标成全新源码构建。结果保存为每个系统独立的 verification 构件，保留 14 天。

## 文件摘要与 Git

.gitattributes 保留文件原始字节，避免 Windows 自动转换换行符后改变证明与发布清单中的 SHA-256。verification/release-files.json 覆盖发布文件，清单自身除外。该清单用于核对这个固定版本；修改文件后，应重新审核并生成新版本清单。

71 个证明模块的摘要和 511 项公理依赖清单来自已经核验的证明快照。文档、工作流和包装脚本的修改不会改变该快照中的证明正文。证明修改需要重新构建、审计并更新快照。
