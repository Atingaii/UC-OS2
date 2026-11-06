# 第113步：把任务创建的 NULL 分支从预留连续接到失败返回

## 本步究竟解决什么

第112步已经有“预留并调用栈 Hook”和“调用 TCB 并失败回滚”两个局部组件，但它们之间尚未连接。本步将它们在**原始、右结合的 AST** 上纵向连接，并把原中断上下文判断、NULL 判断和占用分支接回。

通俗地说：先把空槽标记为本次正在创建；跨调用保留自己的一半权限；发现没有空闲 TCB 时，拿回另一半权限，只清理自己预留的槽，最后返回错误码66。不是假设这些操作执行过，而是证明每个真实语句和资源交接。

**已连接合法 NULL 槽、TCB 空池返回66这一路径的完整分支及其临界区内原始尾部；未覆盖所有 NULL 分支分配结果，不是完整开启中断的 `OSTaskCreateExt` 函数契约，更不是整核完成。** 总目标仍为固定 uCOS2 的源码级 `GOOD_OS` 和同程序 K1–K4，完成后才进入老师附件要求的 uCOS3。

## 对应哪些文件和接口

- 生产证明：`certiucos/v293/proofs/V293TaskCreateOwnedEmpty.v`（274行，5个 Lemma／Theorem）。
- 独立物理实例：`audit/probes/V293TaskCreateOwnedEmptyProbe.v`（500行，28个 Lemma／Theorem）。
- 结构回归：`tests/test_taskcreate_owned_empty.py`（8项；语义正确性由 Coq 承担）。
- 证据目录：`audit/logs/stage113-taskcreate-owned-null-branch/`。

上层应使用的稳定接口为 **`V293_OSTaskCreateExt_owned_empty_critical_tail`**。入口已在临界区内、合法优先级、嵌套计数0、槽位NULL；中间有标准 Hook／TCB 契约和同一个 Inv 的 Open／Close 资源转换；结论证明从原临界区尾部执行到返回66。

`V293_create_owned_empty_tail_source` 由 `reflexivity` 检查原完整函数体恰好等于：`cpu_sr=0; 优先级检查; encrit; 本步tail`。没有重关联 AST、改 C 或换成删分支的程序。IRQ60、占用40、成功／调度分支都保留；本入口由真实类型化字节决定两个 guard，原占用尾部只在已返回后以 `Afalse` 处理。它不是已证明其他入口的证据。

## 资源怎样一路传递

| 位置 | 实际语句／交接 | 槽位权限及仍保留的资源 |
| --- | --- | --- |
| 临界区入口 | 实际 nesting 与 NULL guard | 创建者有完整 NULL 槽；counter、参数、局部变量及外层 frame 均有资源 |
| 预留 | 实际 RESERVED 写入、`excrit1` | 创建者保留半权限，共享池归还另一半 |
| 栈初始化 | 实际栈 Hook 调用及 psp 赋值 | owner、参数及局部 frame 保持；Hook 外部资源由 Rbefore 交给 Rafter |
| 连接处 | `V293_create_owned_empty_seam` | prio／cpu 的 env 和字节合成标准 LV；全部12个局部与 globals 重新排列，无丢弃或复制 |
| 分配 | 真实七实参 `OS_TCBInit` 调用及 err 赋值 | 同一个有限 Spec 的空池 callee 返回66；free-head 字节不偷渡给 caller |
| 失败 | 实际 `encrit1`、合并两半、NULL store、`excrit1`、return66 | owner 被消费；原入口临界栈恢复，外层资源和全部保留局部归还 |

临界区入口 IE=false、栈为 `true::ci`；第一次退出后开启中断；最后回滚再进出临界区。不要把“本定理入口在临界区内”误读成已接通从 IE=true 的整函数入口。

## 不是空前提：一个字面的实例

独立探针只有一个 `OEInv` 和一个两项有限 `OESpec`：500对应 TCB，600对应栈 Hook。相同 Inv／Spec 分别检查完整 TCB 空头函数体及本步连续 tail；TCB 使用标准 `BuildPreI / BuildRetI` 和原七参数／两局部声明域。

`OEEntryLiteral` 给出完整入口可满足性：12个局部的实际字节、表槽403偏移44的完整NULL字节、404的counter0、401的半权限NULL头、current-thread／LINV及sentinel资源在同一物理内存中共存。`OEEntryMemory` 不是一个带假设的未知内存。共享池另有NULL／RESERVED／其他指针的字面可满足性证明；这些实例不是初始化可达性证明。

这里的 Hook 仍为**标准外部资源契约**。探针 `OEProgram` 未提供其函数体，因此不构成完整函数环境的 `WFIFun`。TCB 完整空头 body 在同一 Inv／Spec 下检查，但本步未新增同一 Inv 下完整 TCB 内部入口的字面实例，不能扩大为生产初始化或非空分配结论。

## 单因素消融：只删实际清槽 store

事先记录协议，固定 RESERVED 输入内存、地址、类型、编码与最终 NULL-load 要求；仅把 Action 从真实 `store NULL` 换成 `Some Input`。

| 对照 | 共同输入及真实store引理检查 | 最终 NULL-load 要求 |
| --- | --- | --- |
| StorePresent02 | 通过，日志有 `COMMON_INPUT_CHECKED` | Coq通过，exit0 |
| StoreRemoved02 | 同样通过 | exit1；另有正向定理证明输入读出RESERVED而非NULL |

`OERollbackStoreRemovedKeepsReserved` 才是删除 store 后性质不成立的语义证据；不能把 tactic 失败本身当反例。最初 StorePresent／StoreRemoved 都卡在不透明地址判等的计算，未完成共同输入检查；两份技术失败完整保留，不计负例。第二次仅修正证明方法，不改变输入、Action因素或目标。

这个消融只针对一个物理写操作，**不是整段变异 API 执行、并发中断执行或所有权协议全局保持的证明**。

## 身份、实测与未过的检查

固定上游提交 `0c4a48e6fbc6e915714e816196619a5481accf0c`；配置身份仍为 `74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da`。实际上游 `os_task.c` 第347–407行、`os_core.c` 第2022–2151行及模型输入哈希重核；本步没有重放逻辑 repaired checkout，也没有增加源码修复。

- 稳定生产编译 proof02、探针 probe07 均 exit0；build02 才是将新模块列入 `_CoqProject` 后的集成构建，build01 不取得新模块集成信用。
- 279个活动模块＋独立探针的 `coqchk`、33个声明的 `Print Assumptions` 以本步 `trust.json` 为准；仅接受框架既有 `classic`／`functional_extensionality_dep`。
- 全量1582项，423失败、1错误，与第112步失败／错误 ID 集合相同；新增8项通过。不能表述为全量回归全绿。
- `make audit` 仍 exit2：函数证据输入身份陈旧；`git diff --check` 仍 exit2：既存 `inferules.v` 六行空白。未改阈值或旧证据制造通过。
- 六门仍为 **94／1／1／1／1／0**。本步是局部连接，不增加整函数／整核覆盖信用。
- probe03 的展开合并内存造成计算膨胀，手动终止（记录exit -15）；后改用逐层 merge 空域引理。所有失败源码快照／日志保留，性能失败不作性质消融。其他迭代失败同样保留。

本步终态、清理和冻结情况以 `checkpoint-report.json`、`cleanup.json`、`checkpoint-evidence-manifest.json` 为准。保留旧1390份生产产物、新生产产物、源码及失败证据；只清理本步一次性 Coq 对照／打印器和探针编译产物，恢复原 lia／nia 缓存；未提交或推送。

## 下一步按什么顺序做

1. 从 IE=true 的真实函数入口接入 `cpu_sr=0`、优先级检查、第一次 `encrit1` 借池，动态分派 nesting／槽位，连接本步 NULL 分支及原拒绝路径；再建立标准函数 builder。不能只给本步加一个“前缀已执行”的前提。
2. 将非空 TCB 分配、成功建链／调度路径和预留所有权放入同一个生产共享协议；证明所有相关 API 保持它，处理 RESERVED 地址与真实TCB域不碰撞条件。
3. 连接生产全局 Inv、函数环境 `WFIFun`、初始化、源码级 `GOOD_OS` 和同程序 K1–K4。
4. 只有上述 uCOS2 目标完成，才开始 uCOS3 阶段。
