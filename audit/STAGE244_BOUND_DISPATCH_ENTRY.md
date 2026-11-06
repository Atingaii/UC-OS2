# changed 和 same 强入口满足实际中断前置

本步补上第243步的入口连接：**对每条路径，同一个 typed 状态既满足原强入口，又满足同一 bound LocalInv 下的实际 `BuildintPre`。** 原 EOI → Enter → dynamic Exit → exint 连续证明仍用原 `BDspec`；不是换一套程序或只另造一个非空 builder。

## 证明连接

生产接口位于 `certiucos/v293/proofs/V293InterruptBoundEntry.v`：

- `V293_changed_entry_BuildintPre`：changed snapshot 的抽象入口为 `sched;;aop`。
- `V293_same_entry_BuildintPre`：same snapshot 的抽象入口为 `aop`。

二者都要求向量0、外层入口元数据 `isrupd ir 0 true` 与 `0::si`；显式保留 ready relation、table pointer types、current/nesting 字节界限、high/output 类型条件。它们不新增 heap、globals 或中间 Hoare 前提。

原 inputs/table/task records 用 `V293_retained_arrays_ready` 关闭 ready payload；原 lookup/high/current/counter 保留为 storage，原目标指针关闭 dispatch cell。running/nesting/lock 原有完整字节权限关闭同一 ready/TCB/storage Inv。只有冗余零足迹环境观测可以遗忘；堆资源没有被丢弃。bound `p_local` 由原有 globals 与 shared local 打包得到，不跨 LocalInv 搬运 Hoare 结论。

`V293_outer_active_isr_inv` 仅对向量0构造框架 `isr_inv`：栈顶0时，不存在更小的非负中断号。无需增加 ISR all-clear 前提，但**本步不扩大原连续返回证明的 all-clear 边界**。

## 同状态检查与单因素对照

独立 probe `audit/probes/V293InterruptBoundEntryProbe.v` 包含：

| 路径 | 同一状态检查 | 只改抽象入口的负对照 |
| --- | --- | --- |
| changed | `BEchanged_same_state`：原 `CCentry`、实际 `BCpre` 和原连续 wrapper | `BEchanged_operation_control`：固定 M/O 等全部状态，done builder 不成立 |
| same | `BEsame_same_state`：原 `SCentry`、实际 `BSpre` 和原连续 wrapper | `BEsame_operation_control`：固定 M/O 等全部状态，sched;;done builder 不成立 |

每条路径分别复用原 typed byte heap 的分离见证；不是说 changed 与 same 在同一状态同时成立。两个负对照只换 builder 要求的 abstract operation，保留堆、权限、环境、ISR 元数据、LI、Inv 和当前任务。**不是两次完整执行，也不是运行时性能实验。** 它们证明现有两种抽象入口不能靠直接替换标签统一，而不是证明所有下游机制。

生产导入消融中，7个候选删除导致 entry12 缺 prefix、entry13 缺 prefix output；恢复对应2个导入后，entry14 与 entry11 的证明正文逐字相同且均编译通过，净移除5个导入。所有失败快照保留。

## 验证与边界

四个配置后函数源码、AST、框架、旧 runtime/Inv/规格及连续证明均未修改。独立假设与递归 `coqchk`、全量构建、测试及冻结核对的实际结果记录在 `audit/logs/stage244-bound-dispatch-entry/verification.json`；结构测试不替代 Coq 语义检查。旧423失败、1错误以及旧审计／空白失败保留，不降低门槛。

这是 strong snapshot 到 builder 的单向蕴含，**不是所有 BuildintPre 的分类或反向恢复强条件；不是 `WFInt`，不是 `GOOD_OS`，不是初始化可达，也未闭合同程序 K1–K4。** 连续 wrapper 仍要求原外层 nesting=0 等有效性条件和 all-clear 返回；本步没有独立重证 Ready 返回侧的非空。uCOS3 未开始，未提交／推送。

下一步应处理统一 ISR 抽象规格与实际 builder 到动态分支条件的连接，而不能把这里的单向蕴含反过来使用。

## 本步实测结果

| 检查 | 结果 |
| --- | --- |
| 生产接口与独立 probe | 7 + 7 个定理，Coq 8.18 编译、假设打印及两入口模块递归 coqchk 全通过 |
| 新增结构回归 | 5/5 通过，不替代语义证明 |
| 完整回归 | 2384 项；423 失败、1 错误，旧失败／错误顺序与身份逐项不变 |
| 全量构建与项目审计 | 均通过 |
| make audit 与 git diff --check | 保留原 stale function evidence 身份失败和框架6行历史空白失败 |
| 整核结果 | GOOD_OS、WFInt 与同程序 K1–K4 尚未闭合；uCOS3 尚未开始 |

清理清单在 `cleanup-inventory.json`：只清理本步一次性 Trust 驱动及产物、恢复既有缓存后的备份；源文件、失败快照、冻结日志与可复用 Coq 依赖／产物保留。最终冻结核对以本目录的 manifest 与 verification 为准。
