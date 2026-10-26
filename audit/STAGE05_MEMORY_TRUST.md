# 第五阶段：内存假设审计与有界新鲜块接口

日期：2026-10-26。起点：`3a8b64e`。本阶段不改 C 源码、补丁、冻结身份与函数覆盖；建立实际信任失败证据和不依赖错误公理的新鲜块接口，不宣称整个框架已修复。

## 实际发现

`HalfPermMap.Map := addr -> option (bool * memval)` 允许 `fun _ => Some (true, Undef)`。该映射满足 `FullMemory`；原 `MemoryNotFull` 对所有任意映射声明不满，因此可以推出 `False`。

诊断在独占临时模块中从原 `memory.v` 源码实际重编；只删除该公理声明的对照仍接受满内存见证，同一矛盾证明在公理名引用处失败。没有向活动证明树或 `_CoqProject` 添加矛盾模块，没有用 False 为任何 C 函数取得证明覆盖。

## 最小替代接口

新增通用 `framework/proof/memory_bound.v`，以显式块标识边界推导 fresh；共 11 个接口，包含空内存可满足性、边界增长、set／del／allocb／storebytes／freeb 保持。全满函数无任何这类边界的反例独立检查，不依赖 MemoryNotFull。

所有新增根的假设检查不含 MemoryNotFull，实际仍含经典逻辑与依赖函数外延性；coqchk 仅表明对象在这些前提下检查通过，不证明前提自身一致。

## 未完成的真实义务

原公理与 `memory_prop.v`、`rulesoundlib.v` 的两份无条件 fresh_exist 仍存在。必须在初始化、全局与分片内存、操作语义和 soundness 中传递可满足的块边界，迁移旧证明后移除公理。当前专门信任门禁应失败，不因小模型或构建通过而关闭。

已按实际活动源码定位直接调用点，不使用历史提示词推断迁移完成度：

| 位置／引理 | 当前使用与后续义务 |
| --- | --- |
| `memory_prop.v:fresh_exist`、`rulesoundlib.v:fresh_exist` | 两个无条件存在性引理直接引用错误公理；不能保持原假命题规格只换 tactic |
| 两文件各自的 `cstep_safe_mono`（`rulesoundlib.v`、`cstepLib.v`） | 从小内存扩展到大内存时为大内存选择新块；必须携带大内存边界，不能只知道小碎片有界 |
| `rulesoundlib.v:env_domain_eq_imply_alloc_exist` | 环境定义域相同不保证任意目标内存可分配；还需目标内存的可分配前提 |
| `rulesoundlib.v:alloc_star_exist'` | 两处分配递归都须保持可增长边界；不能只在第一步选择 fresh |
| `step_prop.v:tstep_alloc_nabt` | 排除分配卡住依赖新块存在，需从实际任务状态不变量取得边界 |

这张表只清点直接使用位置，不声称列尽它们的所有间接调用者。下一条可验证纵向路径是：分离／合并内存的边界 → 原 `alloc` 关系的可执行见证及结果边界 → 分配步骤／步骤闭包 → 旧 soundness 调用者；每一层都检查假设闭包和前提可满足性。

长期决策见 [ADR-0002](../docs/adr/0002-内存新鲜块必须来自显式边界.md)，入门解释见 [第五阶段教学](../docs/阶段/05-内存假设审计与有界分配接口.md)。

## 调试与不利证据

首次短探针以隐式方式传入 MemoryNotFull 的内存参数，Coq 报类型错误；显式 `@` 应用后才成功复现矛盾。新边界模块初次使用未导入 assertion 中的 empmem 记号、map 决定过程展开、偏移 scope 及 Maps.get 的 simpl-never 展开遇到编译失败；只修正证明和导入／展开方法，没有改规格前提使之变弱，也没有增加公理。

诊断脚本初版把 Print Assumptions 的 Axioms 标题误当假设名称，随后对照错误的预选文案用了 reference，而本机实际为 variable；两者均先退出工具错误 2，不当成预期信任失败。修正解析和精确文案，原始失败日志保留在本地忽略目录。部分早期 shell 探针只显示管道最后命令的状态；是否编译成功以 coqc 原始错误和后续 pipefail 验收为准，未把这些初次失败记为成功。

## 验收

| 实际检查 | 结果与退出码 |
| --- | --- |
| 完整隔离内存诊断 | Python 退出 1，明确 `BLOCKED_GLOBAL_MEMORY_AXIOM_DERIVES_FALSE`；不是工具错误 |
| 原框架满内存见证、矛盾证明 | 各退出 0；矛盾根的假设含 `MemoryNotFull` |
| 只删公理的对照 | 内存模块与满见证各退出 0；同一矛盾证明退出 1，精确报 `The variable MemoryNotFull was not found` |
| `make check-framework-trust` | 退出 2，子命令退出 1；门禁真实失败，未转写为 PASS |
| `make check-memory-bound` | 退出 0；11 根不含错误公理，边界必要性反例和新对象 coqchk 均通过 |
| `make test` | 65 项通过，包含真实 C 矩阵及逐机制反向检查 |
| `make audit` | 通过；102 个通用框架／tactic 文件及 6 个目标文件；覆盖仍为 `94 / 0 / 0 / 0 / 0 / 0` |
| `make source-freeze-check` | 通过，冻结源码身份仍为 `74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da` |
| `make check-c-evidence` | 368 次执行符合矩阵预期，既有报告无改写 |
| `make check-models` | 六文件隔离检查、三个根无全局假设、对应对象 coqchk 通过；不是框架信任证明 |
| `make build` | 增量构建退出 0；不替代干净构建或一致性审计 |

`make check-build` 已退出 0：108 个活动 `.v` 在无旧 `.vo`、无参考目录的一次性目录中从源码完成全量构建；该构建仍包含原公理，因此不是框架信任通过。临时目录 `/tmp/ucos-clean-build.47dnQJ` 已由退出清理回收。

首次完整诊断从本地 `audit/logs/stage05-memory-trust-final.json` 原样发布为 [audit/memory-trust.json](memory-trust.json)，没有覆盖旧记录。已核对其中四个输入哈希与活动源码一致。其余本地日志为 `stage05-memory-trust-final.log`、`stage05-framework-gate.log`、`stage05-bound-positive.log`、`stage05-regression-checks.log` 与 `stage05-clean-build.log`。日志目录被 Git 忽略；可交付的诊断 JSON 和本报告随提交保存。

## 清理

确认 `/tmp/ucos-stage05-probe-create.py` 仅为本任务生成的最小反例驱动后，已删除该一次性脚本；正式可重放探针保留在诊断工具中。各内存诊断工作目录由 `TemporaryDirectory` 回收。没有发现本阶段遗留 Python 字节码缓存；本地失败／成功日志、源码、冻结证据、依赖和仍用于验证的 Coq 构建产物全部保留。干净构建目录由构建入口在进程结束后回收。
