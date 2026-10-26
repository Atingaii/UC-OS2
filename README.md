# uC/OS-II V2.93.01 的 Coq 形式化验证

使用 CoqImp 通用框架，在 **Coq 8.18** 环境中验证一个固定配置的 uC/OS-II V2.93.01 程序的源码级功能正确性与 safety 性质。

**当前是验证基础工程，不是已完成的内核证明。** 配置后的函数清单尚未生成，真实源码函数的六阶段覆盖均为 0，最终 `GOOD_OS` 定理尚未完成。Git 工作区整洁只表示改动已归档，不表示构建或证明验收通过。

## 第一次阅读

1. [入门与接手指南](docs/入门与接手指南.md)：项目来由、你的工作和学习顺序。
2. [验证范围](PROJECT_SCOPE.md)：唯一目标、固定配置、授权修复及边界。
3. [验证进度](VERIFICATION_STATUS.md)：已经具备什么、尚未完成什么。
4. [第一阶段教学](docs/阶段/01-Coq818与基础检查.md)：Coq 环境、编译、导入与审计的逐步讲解。
5. [第一阶段检查记录](audit/STAGE01_BASELINE.md)：实际执行结果与局限。
6. [初始基线核对报告](audit/BASELINE_REPORT.md)：保留整理前的问题与交接材料错位。
7. [开发路线图](ROADMAP.md)：后续各阶段及验收条件。

## 唯一验证目标

- 内核：uC/OS-II V2.93.01。
- 固定上游提交：`0c4a48e6fbc6e915714e816196619a5481accf0c`。
- 源码身份：[csrc/UPSTREAM.lock.json](csrc/UPSTREAM.lock.json)。
- 固定配置：[csrc/config/v29301-profile.json](csrc/config/v29301-profile.json)。
- 当前仅授权两类修复：嵌套互斥锁优先级恢复、调度锁定期间的当前任务自删除。
- 证明验收版本：Coq 8.18.0。不能用其他版本的小模型检查代替该环境中的完整验收。

本项目不覆盖所有配置组合，也不验证编译器、最终二进制或具体硬件。源码中的独立等待结果字段与 TCB 指针所有权判断属于上游原生行为，不是项目补丁。

## 目录说明

| 位置 | 用途 |
| --- | --- |
| `certiucos/v293/` | 当前唯一的内核专用 Coq 模型、规格与证明 |
| `framework/`、`tactics/` | 复用的通用验证框架与辅助证明工具 |
| `csrc/` | 源码身份、固定配置与尚待集成的修复材料 |
| `scripts/` | 源码获取、哈希校验、配置生成与审计脚本 |
| `audit/` | 覆盖清单、反例证据与核对报告 |
| `docs/` | 中文学习与交接说明 |
| `references/` | 随交接保存的参考资料，不属于构建依赖 |

## 环境与常用命令

准备好 Coq 8.18.0、Git、Python 3、GNU Make、Bash 与 tar 后，在仓库根目录执行：

```sh
coqc --version
make test
make audit
make check-models
make check-build
make fetch-source
make source-audit
make config-audit
make build
```

本机已降为 Coq 8.18.0。第一阶段已修复小模型的导入与参数引入问题，审计回归测试、静态审计、六文件隔离编译、三个小模型根定理的假设与 `coqchk` 检查均已通过。完整构建结果与源码校验见第一阶段检查记录；这些检查不能替代最终整核证明。

`make build` 在当前目录增量构建；`make check-build` 仅复制活动 Coq 源码和构建入口，在没有参考资料与旧 `.vo` 的一次性目录中完整构建，结束后清理该目录。

`make fetch-source` 会获取锁定提交并验证哈希，也会重建目标 `checkout/` 目录；已有本地源码工作时，应先检查并保留现场。

## 参考资料与历史提示词

`start-prompt.md`、`work-prompt.md` 保留交接原始内容，仅清理导入时发现的行尾空白。后者提到的七项修复、95 个函数等状态缺少当前代码支持，**不能直接当作本仓库的当前任务或完成证据**。约束以 `AGENTS.md`、`PROJECT_SCOPE.md` 和实际源码锁为准。

`references/` 中的论文、源码包和工作记录仅供查阅。最终验证工程不得依赖这些可移除材料；本次没有为第三方材料新增统一许可证或改变其原有权利标识。
