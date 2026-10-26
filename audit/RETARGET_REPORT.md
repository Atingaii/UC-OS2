# 历史目标基础重建报告

本文描述原有基础重建成果；2026-10-26 的实际检查以 [当前基线核对报告](BASELINE_REPORT.md) 为准。

## 已记录的重建结果

- 活动内核专用证明树仅保留 `certiucos/v293/`。
- 复用版本无关的 `framework/` 与通用 tactic 模块。
- 用 `csrc/UPSTREAM.lock.json` 固定上游提交与逐文件哈希。
- 用 `csrc/config/v29301-profile.json` 固定配置。
- 用 `csrc/repairs/REPAIR_TARGET.json` 限定两类修复。
- 函数覆盖清单从空表重新开始，不计入历史局部证明。

## 原有审计工具的作用与限制

`scripts/project-audit.py` 扫描旧目标文字、检查活动新版 Coq 树中的证明逃逸关键词，并确认源码锁存在。

这一文字扫描不等价于完整依赖审计；加入历史参考资料和提示词后，当前扫描会失败。不得把历史报告或脚本退出成功当作实际源码对应和最终程序证明的证据。

原重建记录称当时环境没有 `coqc`，没有声称完成 Coq 8.18 构建。当前机器已有其他版本的 Coq，但仍需在目标环境完成 `make fetch-source` 与 `make build` 等验收。
