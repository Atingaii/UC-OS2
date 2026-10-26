# 第六阶段：框架内存修复验收记录

日期：2026-10-26。状态：**框架内存修复完整验收通过，保留列明的逻辑假设**。这是通用验证基础的修复，不是具体 V2.93.01 内核的 `GOOD_OS` 证明。

## 已实现

- `HalfPermMap.Map` 携带已占用块标识有界证明，数据函数和权限算法保持原样。
- 从合法表示推导 `memory_has_fresh_block` 和 `memory_not_full`，删除原 `MemoryNotFull` 公理。
- 两份旧 `fresh_exist` 复用稳定接口；修正 record 投影引起的旧证明脚本问题，不削弱规则规格。
- 保留原 11 个显式边界接口；新增 20 个表示／原语对应、反例和非空可满足根。
- 检查器覆盖实际坏构造器、边界中和单因素对照、三个分别指定拒绝位置的算法故障，以及完整框架根依赖闭包。
- 第五阶段失败 JSON 保持原字节与 SHA-256，不回写成成功。

## 已实际执行的阶段检查

- 隔离 `memory.v` 全部原有引理编译通过，正式表示对应模块与 20 个根编译通过。
- 中途 70 项 Python 回归通过，包含原有真实 C 矩阵与 11 项机制故障注入，以及新增的假设解析／拒绝回归。后续对抗性复核又补充回归，最终为 73 项，见下。
- 静态／覆盖审计通过：103 个框架／工具 Coq 源码、6 个目标文件；覆盖仍为 `94 / 0 / 0 / 0 / 0 / 0`。
- 初期投影展开、类型推断和门禁失败日志保留，不计作通过；最终源码重新干净构建并执行完整门禁，结果见下。

## 迁移中实际发现的问题

保留失败日志，不把中间失败删掉或改成成功：

- record 投影不再能依靠旧函数展开直接归约：`symbolic_lemmas.v` 和 `lmachLib.v` 的同名读取引理增加投影化简。
- `step_prop.v` 中 `storebytes_minus` 的旧 `auto` 不再关闭真分支；先规范化 `offset` 并使用已经取得的地址不等式，直接证明数据读取相等，不改引理规格。
- 完整构建第 7 次在 `invariant_prop.v:mem_set_get_neq` 停止，原因是没有类型标注的 `m a'` 被推断成普通函数，找不到 `PermMap` 实例。隔离同一声明及原证明，未标注版本退出 1，仅给 `m` 标注 `mem` 的版本退出 0。早期探针漏导入 `join_lib` 的无关失败另行保留，不计为此对照的结果。
- 原语与规则引理的逻辑结论未削弱；模块内原来用于函数的三个 `extensionality*` 辅助引理改为 record 的外延引理，属于明确的内部接口调整，不声称所有辅助签名逐字不变。

## 检查器的对抗性复核

- 第一次故障注入把 raw 更新结果直接改为 `None`，导致参数 `v` 失去可推断类型，提前在定义处失败；门禁按预先规定的 `erase_set` 位置拒绝计作成功。后续用恒真条件的不可达分支保留原参数类型，实际错误行为仍是将目标地址置空，指定拒绝定理不变。
- 原假设解析模式只接受 ASCII 首字母。真实隔离 Coq 模块打印 `α : False` 时被漏掉；新增两个反向测试先观察到失败，再修复解析，Unicode 与带 universe 标注的未知名字均必须被拒绝。
- 实际框架根闭包暴露 `auxdef.TMSpecMod.extensionality` 与 `auxdef.TOSpecMod.extensionality`。没有把它们补进允许列表；先用完全相同命题做最小证明，再把 `Map.v` 和公共 `Coqlib.v` 的两处重复公理改为标准函数外延性推导的引理。生成的两个模块名字和公共库名字不再作为独立假设接受。
- 额外原则允许列表收紧为经典逻辑、标准依赖函数外延性和标准相等运输原则；新增回归明确拒绝三个旧映射公理名字。最终实际列表已经由根检查确认。

## 最终验收

### 环境与正向检查

实际环境：Coq 8.18.0、OCaml 4.14.2、Python 3.11；C 回归使用 GCC 12.3.1 与 Clang 17。以下 Coq 命令均使用 `COQBIN=/data/home/lucentzhou/.opam/default/bin/`；构建使用 `JOBS=2`。

| 实际命令／检查 | 退出码 | 可观察结果 |
| --- | --- | --- |
| `make check-build` | 0 | 最后版本的 109 个不同活动 `.v` 全部从源码编译；不复制旧 `.vo` 或参考资料 |
| `python3 scripts/check-memory-trust.py --report audit/framework-memory-repair.json` | 0 | `PASS_MEMORY_REPAIR_WITH_RECORDED_ASSUMPTIONS`；先构建当前源码，再检查 11／20／13 个根、全部反向对照和依赖闭包 |
| 门禁内 `coqchk -silent …` | 0 | 边界、表示及真实框架根的依赖闭包检查成功；不导入故意含矛盾的历史测试夹具 |
| `make check-memory-bound` | 0 | 11 个边界根和 20 个表示根通过；明确输出 `NOT_ASSESSED_BOUNDS_ONLY`，不代替完整门禁 |
| `make test` | 0 | 73 项测试通过，包括实际 C 回归、已有 11 项机制消融与新增解析／拒绝检查 |
| `make audit` | 0 | 103 个框架／工具文件、6 个目标文件；覆盖仍为 `94 / 0 / 0 / 0 / 0 / 0` |
| `make source-freeze-check check-c-evidence` | 0 | 冻结源码只读重放一致，368 次 C 对照执行符合原报告 |
| `make check-models` | 0 | 六文件隔离检查通过；三个小模型根均 `Closed under the global context`，相关模块内核检查通过 |

本机最终干净构建日志为 `audit/logs/stage06-clean-build-final-03.log`；早一次全量成功不替代最后两处重复外延性公理改为证明后的重新构建。其余最后执行日志为 `stage06-framework-gate-final.log`、`stage06-bound-target-final.log`、`stage06-python-tests-final-02.log`、`stage06-static-audit-final-02.log`、`stage06-frozen-c-evidence-final-02.log` 和 `stage06-small-models-final-02.log`。`audit/logs/` 是本机忽略目录，不作为下载仓库后必然存在的材料；正式交付证据是[修复 JSON](framework-memory-repair.json)、源码和可重放脚本。

新 JSON 记录每项 Coq 检查的实际退出码、输出、Coq 版本、根列表及 113 项源码／检查入口／历史证据的 SHA-256。检查开始、结束及交付复核时输入均一致。报告只允许写入新路径，不覆盖既有证据。第五阶段 JSON 的固定哈希仍为 `45ba9ca37bc7d3226c2227e3433e4a689712dcd348535effa8c751aea2fad819`。

### 真实框架根，而非只有新增辅助引理

| 路径 | 检查的根 |
| --- | --- |
| 合法内存与旧接口 | `memory.memory_has_fresh_block`、`memory.memory_not_full`、`memory_prop.fresh_exist`、`rulesoundlib.fresh_exist` |
| 内存扩展 | `rulesoundlib.cstep_safe_mono`、`cstepLib.cstep_safe_mono` |
| 环境／连续分配 | `rulesoundlib.env_domain_eq_imply_alloc_exist`、`rulesoundlib.alloc_star_exist'`、`rulesoundlib.alloc_star_exist` |
| 任务步进 | `step_prop.tstep_alloc_nabt` |
| 上层 soundness | `soundness.RuleSound`、`toptheorem.verified_os'`、`toptheorem.Soundness` |

11 个边界根和 20 个表示根的实际假设并集均为：

```text
Classical_Prop.classic
FunctionalExtensionality.functional_extensionality_dep
```

13 个框架根的并集另有 `Eqdep.Eq_rect_eq.eq_rect_eq`，没有 `MemoryNotFull`，也不再有公共库／映射模块自行声明的外延性公理。各组并集不是说每条定理都依赖所有项；这些是保留的信任原则，不声称完全无公理、三者逻辑独立或 Coq 已证明自身一致。含义见[信任基础](../TRUSTED_BASE.md)。活动树还有其它声明；本阶段没有逐个消除，也不把选定根的结果泛化到未来具体内核根。

### 预先指定的反向检查

| 对照 | 实际退出码 | 实际拒绝位置／结果 |
| --- | --- | --- |
| `InvalidTypedMemory`：全满函数、实际 `mkMap`、证明 `I` | 1 | 要求 `raw_bounded`，`I : True` 不匹配 |
| `BoundEnforced`：保留边界谓词的隔离 record | 1 | 同一候选和 `I` 不满足 `invariant` |
| `BoundNeutralized`：只将谓词改为 `True` | 0 | 同一候选和证明接受；不声称其整个框架 soundness 已验证 |
| `FaultSet`：raw 设置目标变为空 | 1 | 到达 `erase_set`，数据擦除等式不能统一 |
| `FaultMergePermission`：raw 合并改错权限 | 1 | 到达 `erase_merge`，算法对应等式不能统一 |
| `FaultReleasePermission`：raw 释放改为另一权限 | 1 | 到达 `erase_freeb`，返回结果不匹配 |
| `HistoricalLogicalPath`：最小旧矛盾路径 | 0 | 从故意保留的旧式公理和满函数推出 `False`；仅在隔离夹具中 |
| `HistoricalPathWithoutAxiom`：只删该公理 | 1 | 同一证明在 `global_not_full` 引用处被拒绝 |

三项算法故障各自独立运行，检查器要求失败行位于预定定理的声明到 `Qed` 之间；较早的语法／类型错误不算通过。raw 权限算法独立写出，不回调被测 `rjoin/rminus`，避免两边共享错误实现的循环对照。历史最小路径不冒充重新构建整个旧框架，旧完整失败报告原样保留。

对抗性源码复核还比较了原有命题声明：原语、规则及客户端逻辑结论不变；声明文本差异限于明确记录的三个内部外延辅助接口，以及 `mem_set_get_neq` 的显式 `m : mem` 类型标注。两处外延性 `Axiom → Lemma` 的命题保持相同，新增表示模块无公理或证明洞。

## 边界

本阶段不修改冻结 C 源码、两项授权补丁、配置或函数位置清单。修复后 C 身份仍为 `74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da`，94 个定义只完成 `located`。不补记模型／函数证明覆盖。

合法内存域显式收窄为块标识有界函数；这是语义前提，不是任意旧 raw 状态全集的等价，也不是有限物理 RAM 或分配耗尽模型。空内存、继续分配和具体读写释放提供可满足见证，但没有连接具体 V2.93.01 的初始化。

最终具体程序的 `GOOD_OS` 仍未完成。下一步按路线图回到新版公共状态／共享不变量，完成真实函数纵向连接、具体初始化与程序级证明；通用 `Soundness` 通过不自动提供该程序的 `TopRule` 前提。

## 清理与交付复核

清理前逐项核对专用实验目录中的 51 个文件，确认仅有本任务的 Coq 探针源码及派生产物，没有子目录、符号链接或用户数据，随后删除该目录。最终干净构建及门禁的临时目录已由各自退出清理逻辑移除。保留活动源码、既有可复用构建缓存、依赖、本机失败／成功日志及正式证据；没有清理上游 checkout 或原始参考材料。

交付前重新确认：113 项证据输入哈希全部匹配，正／反向退出码与表格一致，中文文档本地链接有效，静态与覆盖审计通过，增量构建无待重编项，文本差异无空白错误。冻结 C／配置、既有源码清单、覆盖与原失败证据均未修改。

设计见 [ADR-0003](../docs/adr/0003-以内存类型封装块上界.md)，入门见[第六阶段教学](../docs/阶段/06-修复框架内存表示与证明链.md)。
