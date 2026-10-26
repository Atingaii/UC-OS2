# 中文交接基线核对报告

核对日期：2026-10-26。整理前的 Git 基线为 `deed527`，原标签为 `v29301-clean-retarget`。本报告记录可观察的当前状态，不继承历史提示词中的完成声明。

## 本次整理范围

- 中文化活动说明文档，新增学习与交接入口。
- 保留原始参考资料与根目录两份提示词，不改写历史实质内容；仅规范化导入提示词和交接说明的行尾空白及文件尾多余空行。
- 将随项目提供的外部 Markdown 交接说明按原始内容复制到 `references/项目交接说明.md`；副本仅清理空白，外部原文件不变。
- 恢复原 Git 记录中六个脚本的执行权限。
- 不修改 C／Coq 源码、审计脚本内容、源码锁、配置、覆盖清单或授权修复范围。
- 不上传父目录中其他工程、原始项目 ZIP、凭据或临时构建产物。

这是一版可追溯的 Git 交接快照，**不是构建通过的里程碑，也不是整核验证成果**。

## 目标与覆盖

| 项目 | 当前事实 |
| --- | --- |
| 上游版本 | V2.93.01 |
| 上游提交 | `0c4a48e6fbc6e915714e816196619a5481accf0c` |
| 修复范围 | 当前约束仅授权嵌套互斥锁优先级恢复、调度锁定自删除两类 |
| 主线源码 checkout | 尚不存在；参考目录中的源码包不等于已校验的主线 |
| 配置后函数总数 | 尚未生成，不能采纳历史记录中的其他数字 |
| 函数覆盖行数 | 0 |
| 六阶段覆盖 | `0 / 0 / 0 / 0 / 0 / 0` |
| 源码修复集成与冻结 | 尚未完成 |
| 最终源码级 GOOD_OS | 尚未完成 |

## 交接材料错位

`work-prompt.md` 记载七项修复、95 个配置函数及后期有界内存证明，但当前 `PROJECT_SCOPE.md` 只授权两类修复，覆盖清单为空，以下关键文件也不存在：

```text
framework/proof/memory_bound.v
certiucos/v293/proofs/V293Program.v
csrc/repairs/K5_FROZEN_SOURCE.json
audit/MEMORY_MODEL_TRUST.md
```

这些缺失说明不能直接照该提示词续做；它们不能反向证明更后期的工程不存在。正式推进前，应核对是否有配套的更新仓库。在获得实物前，以当前约束与锁文件为准。

## 实际检查结果

| 检查 | 结果 | 范围与限制 |
| --- | --- | --- |
| `coqc --version` | 8.20.1 | 不是项目指定的 8.18.0 |
| `make audit` | FAIL，退出码 2 | 子脚本 `project-audit.py` 因历史资料中的旧目标文字退出 1，后续覆盖子命令未运行 |
| `python3 scripts/coverage-audit.py` | PASS，退出码 0 | 单独执行；空清单格式通过，不表示函数已验证 |
| JSON 解析、`scripts/*.py` AST 解析 | PASS | 仅语法检查，不证明运行逻辑 |
| `bash -n coqc-wrapper.sh` | PASS | Shell 语法检查 |
| `bash -n scripts/fetch-v293-source.sh` | PASS | 未实际获取源码 |
| `git diff --check` | PASS | 文本空白检查 |
| `git fsck --full` | PASS | 本地 Git 对象完整性检查 |
| 所选文本文件常见凭据签名扫描 | 未命中 | 非完整秘密检测；未将本机 GitHub 凭据加入项目 |
| Coq 8.18.0 全量构建、最终假设闭包、最终 `coqchk` | NOT RUN | 目标环境尚未准备，最终根定理也未完成 |

### 项目审计失败的原始位置

导入外部交接说明后，原脚本报告五处旧目标文字：

```text
work-prompt.md
start-prompt.md
references/ucos293-证明.md
references/uCOS2发现的4类bug.md
references/项目交接说明.md
```

这是全文扫描失败，不等价于活动证明已依赖旧内核。后续应核对审计范围与真实依赖，并保留拒绝旧模型依赖的检查能力。本次未删除历史材料、修改扫描脚本或将失败改写为通过。

### 本机版本下的局部 Coq 编译

将六个活动文件复制到一次性目录，在该目录逐个执行：

```sh
coqc -q -R . CertiOS <相对文件路径>
```

未复制参考资料，也未更改任何 Coq 源码。结果如下：

| 文件 | 退出码 |
| --- | --- |
| `certiucos/v293/code/V293Config.v` | 0 |
| `certiucos/v293/model/V293MutexPriorityModel.v` | 0 |
| `certiucos/v293/model/V293PendModel.v` | 0 |
| `certiucos/v293/model/V293TaskDeleteModel.v` | 0 |
| `certiucos/v293/spec/V293SafetySpec.v` | 0 |
| `certiucos/v293/proofs/V293SafetyProof.v` | 1 |

失败位置为 `V293SafetyProof.v` 第 7 行，输出：

```text
Error: The variable V293_timeout_suspend_resume_ready was not found
in the current environment.
```

该结果只针对本机 Coq 8.20.1，不替代 Coq 8.18 验收。本次不修改证明导入或证明正文，避免把文档归档混成未经目标环境确认的证明修复。

## 后续工作顺序

1. 确认是否存在与后期提示词配套的更新工程。
2. 准备 Coq 8.18.0，复核并处理实际基础构建失败。
3. 明确历史资料与活动依赖的审计边界，保留正反检查证据。
4. 获取并核验固定源码，生成配置后函数清单。
5. 完成两项授权修复的实际集成、对照回归与源码冻结。
6. 再推进函数级证明、初始化与整体程序连接。

## 清理记录

本次局部编译只使用任务专用的一次性目录。已确认其中仅有复制的六个文件及派生 Coq 产物，随后整体删除。未删除源文件、参考资料、现有依赖与凭据，也未执行删除原始压缩包的操作；交付目录没有留下此次局部编译产物。

## 原始归档位置说明

本轮重新检查时，父目录中的原始项目 ZIP 已不在原路径，未能再次对该 ZIP 做逐字节比较；本轮没有执行删除它的操作。C／Coq／脚本／配置与锁文件未变的结论，来自与原 Git `HEAD` 的差异检查，不依赖缺失的 ZIP。外部 Markdown 说明仍在父目录原路径。
