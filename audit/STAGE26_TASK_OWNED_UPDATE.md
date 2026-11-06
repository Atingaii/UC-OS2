# 阶段26：真实五次 TCB 写入后的空间资源归还

## 本轮差量与边界

不是新增另一套模型，而是在既有 `V293TaskRecordOwnership.v` 的227行逐字前缀后追加195行，现422行。源码SHA256：`a576182aefb5da1b35475c51cc1453dd66db71368329ce6a5a378333b0a1053d`。其余166个活动源不变，包括7773行 `V293CriticalReturn.v`；仍167源，64目标源＋103框架／tactics源。12个受保护输入（含 `_CoqProject`）、8426个既有 audit/scripts/tests 文件与 HEAD 保持，未提交。不修改旧测试、门禁或冻结报告来接纳新身份。

两授权修复后的 C 身份只读重验仍为 `74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da`，94个配置后函数。五条赋值的源级对应沿用既有配置后 `os_task.c:162—166` 与既有 AST；不授验证 C 前端／ABI 信用，不新增 C 修复。

## 证明的纵向连接

- `V293_owned_record_cell_update` 在真实完整权限 `Amapsto` 与真实 `join` 上构造 `store`，使用标准 `store_mapstoval_frame1` 在该次 `store` 的返回内存上取得新所有权。同一 frame 的物理片段、抽象片段、环境和任务状态保持；不是再假设一个满足出口的内存。
- `V293_owned_byte_update` 从该 `store` 的成功反解入口 full-permission byte，并证明返回内存等于现有 `V293_put_byte`。
- `V293_owned_cells_byte_update` 处理列表中间的字段，借助分离合取重排保留前缀、后缀与 `R`；`V293_owned_cells_byte_writable` 从入口所有权推导可写权限。
- `V293_owned_task_record_update` 顺序更新50／52／51／54／53五个偏移，保留同一状态、消息与 `pend`；范围沿用当前优先级 `<13`。
- 稳定入口 `V293_task_prio_tcb_owned_execution` **只调用一次**既有真实五赋值执行根，删去了独立可写前提（由空间入口推出），保留旧根的全部执行、五字段读数、TCB指针、locals、可写权限、逐地址 frame 输出，再追加**同一个明确 `M'`** 上的新 TCB 所有权与原 `R`。

没有证明完整 `OSTaskChangePrio` 调用／返回都保持该空间断言；没有建立抽象任务表重键与物理资源的联合共享不变量，也没有纳入全部位图、优先级表、ECB／链表、分配器、栈、初始化或正常无锁调度。不晋级正式函数覆盖。源码级 GOOD_OS 与同程序 K1—K4仍开放，uC/OS-III未开始。

## 独立输入与可观察结果

新 probe 183行，SHA256 `541015058874a909807500c1d09feb2ec35f39f63ad52482538f8f09bb383db1`。复用旧 probe 的一般编码／分离列表构造引理，不修改它，不复用旧已完成 trace。

字面入口重新构造目标 `(41,8)` 的旧优先级8、SEM等待 `(72,5)`／delay1／message `(120,7)`／pend0，以及另一个 `(60,0)` 的优先级4、ready、NULL。frame 非空：还包含完整 TCB 指针局部变量与新优先级／行列／掩码操作数。`UpdateEntrySpatial`、`UpdateEntryPointer`、`UpdateEntryLocals` 独立建立入口；`UpdateLiteralExecution` 逐字列出五条 AST 赋值后调用一般接口。

同一次出口中目标优先级为6，另一任务字段仍为4，操作数局部变量仍为6，状态与其余已拥有字段保持。`UpdateRejectsStaleOwnership` 从实际最终优先级读数排除“仍拥有优先级8的目标记录”。字面实例的抽象域为空，不能据此声称有非空 ECB 相容关系、完整共享Inv或初始化可达性；一般 frame 定理不限制抽象域为空。

## 前瞻消融与对抗性复核

修改前 `protocol.json` 已固定两项单因素：

| 因素 | 唯一改变 | 固定项 | 实际结果 |
| --- | --- | --- | --- |
| StaleCellValue | 单字段出口仍保留 old 而不是 replacement | 入口与整个目标 Proof 后缀逐字保持 | Proof从240行开始，254行拒绝 |
| StaleTaskPriority | 任务出口仍保留旧 priority 而不是 new | 入口与整个目标 Proof 后缀逐字保持 | Proof从322行开始，384行拒绝 |

两项 `downstream_credit=false`。拒绝只授固定证明敏感性，不能由早拒绝推断五个下游写入、全函数或 GOOD_OS 都已覆盖。正控是重新定义／重新证明整份源的隔离模块，不导入候选所有权模块；另有独立字面五赋值、非空 frame 与同一次终态的语义反例。

针对“是否是假定出口”“是否忽略权限”“是否丢掉其他任务”“是否把旧构建套在新身份”四项质疑，分别检查了真实 store 返回值、入口推导权限、非空 frame 最终读数、当前源编译与历史构建身份区别。不将 `R` 保持解释为任何全局相容性质自动成立。

## 检查与完整性记录

日志位于 `audit/logs/stage26-task-owned-update/`。生产编译13成功；此前语法、未显式导入、投影推断、有限列表成员实例化失败的源快照和日志原样保留。probe06成功，probe01—05失败记录保持。未修改假设白名单。gate01实际退出0：9项检查符合预期，4次coqc、两项预期拒绝、3次独立coqchk（207.49／214.66／204.29秒）；184个不同冻结输入保持。4个正控根和7个probe根实际打印的假设并集仅 `Classical_Prop.classic` 与 `FunctionalExtensionality.functional_extensionality_dep`。门禁临时树12文件逐项确认后清理，全部源快照保留。

增量 `make build JOBS=2` 退出0，仅COQDEP和nothing-to-be-done，没有新增当前身份的 source-only 全量干净构建。上一轮167源的成功干净构建只属于旧所有权模块SHA `651b1d1c...`，不能代替本轮新身份；本轮编译受影响源并独立检查其依赖闭包。

范围审计与冻结源码重验通过；默认 `make audit` 仍退出2：`stale function evidence input identity`。正式六门仍94／1／1／1／1／0。

本轮追加后运行旧934项：321失败1错误，共322个诊断。前轮320个诊断全部按重数保留，新增两项逐条trace核实为旧 ownership gate 的源SHA与生产快照过期；不重绑旧证据，也不把其他历史失败统称快照问题。新增6项协议测试通过；全量940项／321失败1错误，与同轮旧934项的322个诊断按重数完全相同。

修改前已明确将新 CriticalReturn／所有权模块的编译缓存列为后续可复用依赖保留，避免下一轮重复重建重型依赖；不冒充一次性缓存清理对象。其余11个一次性文件（509,797字节：10个probe Coq产物和1个未用临时查看副本）已在第一次删除前确认整个集合，并在全部独立检查和测试完成后重新核对再清理。903个既有缓存路径保留，10个新可复用依赖产物保留；所有源码、失败与成功证据保留。见cleanup-plan.json／cleanup-result.json。

中文已填表格和学习入口：[写入TCB后如何归还资源](../docs/开发中/写入TCB后如何归还资源.md)。
