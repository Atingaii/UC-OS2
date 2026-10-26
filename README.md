# uC/OS-II V2.93.01 的 Coq 形式化验证

使用 CoqImp 通用框架，在 **Coq 8.18** 环境中验证一个固定配置的 uC/OS-II V2.93.01 程序的源码级功能正确性与 safety 性质。

**当前是验证基础工程，不是已完成的内核证明。** 修复后固定配置已冻结并清点出 94 个 C 定义与 16 个声明级边界；六阶段覆盖为 `94 / 0 / 0 / 0 / 0 / 0`，只完成位置证据，最终 `GOOD_OS` 定理尚未完成。Git 工作区整洁只表示改动已归档，不表示构建或证明验收通过。

**当前框架信任门禁明确失败：原 `MemoryNotFull` 公理可推出 `False`。** 已保留可重放反例和单因素消融，新增不依赖该公理的有界分配接口；旧框架迁移尚未完成。详见 [信任基础](TRUSTED_BASE.md) 与 [第五阶段报告](audit/STAGE05_MEMORY_TRUST.md)，不能以编译通过掩盖此失败。

## 第一次阅读

1. [入门与接手指南](docs/入门与接手指南.md)：项目来由、你的工作和学习顺序。
2. [验证范围](PROJECT_SCOPE.md)：唯一目标、固定配置、授权修复及边界。
3. [验证进度](VERIFICATION_STATUS.md)：已经具备什么、尚未完成什么。
4. [第一阶段教学](docs/阶段/01-Coq818与基础检查.md)：Coq 环境、编译、导入与审计的逐步讲解。
5. [第一阶段检查记录](audit/STAGE01_BASELINE.md)：实际执行结果与局限。
6. [初始基线核对报告](audit/BASELINE_REPORT.md)：保留整理前的问题与交接材料错位。
7. [第二阶段教学](docs/阶段/02-源码配置与函数清单.md)：实际 C 源码、配置、函数清单和 CPU 边界。
8. [第二阶段检查记录](audit/STAGE02_SOURCE_INVENTORY.md)：92 个上游函数的身份与交叉检查。
9. [开发路线图](ROADMAP.md)：后续各阶段及验收条件。
10. [第三阶段教学](docs/阶段/03-真实C回归与授权修复.md)：从任务／优先级入门，理解真实反例、两项补丁及单因素消融。
11. [第三阶段检查记录](audit/STAGE03_C_REPAIRS.md)：四种补丁组合的实际 C 执行结果和边界。
12. [第四阶段教学](docs/阶段/04-源码冻结与真实函数定位.md)：理解源码身份、修复后 94 个函数及“定位不等于证明”。
13. [第四阶段检查记录](audit/STAGE04_SOURCE_FREEZE.md)：只读重放、完整位置覆盖与反向检查。
14. [第五阶段教学](docs/阶段/05-内存假设审计与有界分配接口.md)：公理、矛盾、显式内存边界和信任门禁。
15. [第五阶段检查记录](audit/STAGE05_MEMORY_TRUST.md)：真实反例、单因素消融、新接口检查及尚未迁移的旧证明链。

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
| `csrc/` | 源码身份、固定配置与已冻结并接入 C 回归的两项补丁 |
| `scripts/` | 源码获取、哈希校验、配置生成与审计脚本 |
| `audit/` | 覆盖清单、反例证据与核对报告 |
| `docs/` | 中文学习与交接说明 |
| `references/` | 随交接保存的参考资料，不属于构建依赖 |

## 环境与常用命令

准备好 Coq 8.18.0、Git、Python 3、GNU Make、Bash、tar、Clang、GCC 与支持 JSON 的 Universal Ctags 后，在仓库根目录执行：

```sh
coqc --version
# 仅在 checkout 不存在时获取；已有修改时不要重建。
make fetch-source
make source-audit
make config-audit
make source-inventory-check
make source-freeze-check
make check-c
make check-c-evidence
make test
make audit
make check-models
make check-build
make build
# 新有界接口的正向检查：
make check-memory-bound
# 当前明确失败的全框架信任门禁，单独运行并查看原因：
make check-framework-trust
```

本机已降为 Coq 8.18.0。第一阶段已修复小模型的导入与参数引入问题，审计回归测试、静态审计、六文件隔离编译、三个小模型根定理的假设与 `coqchk` 检查均已通过。完整构建结果与源码校验见第一阶段检查记录；这些检查不能替代最终整核证明。

第二阶段新增真实源码清单及 12 项集成测试，`make test` 合计 26 项且要求已获取锁定源码；具体前后对照和结果见第二阶段检查记录。`make source-inventory-check` 只核对，不改写已提交清单。

第三阶段将两项授权补丁应用到临时源码副本，23 个真实 C 场景在四种补丁组合、GCC／Clang、两种优化下共执行 368 次对照；另有 11 项逐机制／故障注入检查和 2 项输入边界检查。第三阶段 `make test` 合计 40 项。C 回归需要 Linux i386 可执行支持，不依赖 32 位 libc；模拟 CPU 边界及未完成义务见第三阶段教学。

第四阶段固定与第三阶段相同的修复后源码身份，清点 94 个定义并建立完整位置证据；新增 22 项正反测试，该阶段全套 62 项。`make source-freeze-check` 实际重放和清点，`make audit` 检查记录身份与覆盖。Coq 源码对应、所有函数证明和整体连接仍未完成。

第五阶段发现原全局内存公理与任意函数式内存表示相冲突；隔离诊断实际复现矛盾，信任门禁保持失败。新增 11 个有界内存接口和 3 项假设输出解析测试，当前全套 65 项。正向接口检查不含错误公理，不代表旧框架已迁移，详见本阶段报告及 [ADR-0002](docs/adr/0002-内存新鲜块必须来自显式边界.md)。

`make build` 在当前目录增量构建；`make check-build` 仅复制活动 Coq 源码和构建入口，在没有参考资料与旧 `.vo` 的一次性目录中完整构建，结束后清理该目录。

`make fetch-source` 会获取锁定提交并验证哈希，也会重建目标 `checkout/` 目录；已有本地源码工作时，应先检查并保留现场。

## 参考资料与历史提示词

`start-prompt.md`、`work-prompt.md` 保留交接原始内容，仅清理导入时发现的行尾空白。后者提到的七项修复、95 个函数等状态缺少当前代码支持，**不能直接当作本仓库的当前任务或完成证据**。约束以 `AGENTS.md`、`PROJECT_SCOPE.md` 和实际源码锁为准。

`references/` 中的论文、源码包和工作记录仅供查阅。最终验证工程不得依赖这些可移除材料；本次没有为第三方材料新增统一许可证或改变其原有权利标识。
