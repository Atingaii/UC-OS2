# 第141步：临界区、两道限制与实际调度的连续全局轨迹

## 本步做了什么

固定目标仍是 uC/OS-II V2.93.01，提交 `0c4a48e6fbc6e915714e816196619a5481accf0c`。不改 C、配置、既有 AST、framework、tactics 或冻结旧证据。沿用 `Source/os_core.c` 第1702行起的原 `OS_Sched` 手工 AST：保存变量初始化、进入临界区、中断嵌套与调度锁检查、原选择尾段、退出临界区、返回。

与第140步相比，本步不是再造一种执行语义，而是将原 `loststep` 的临界区操作接到原 `lpstep` 的连续闭包；真实 ir／aux 随每一步同步。原 `encrit` 压入当前 IE 并关中断，原 `excrit` 弹栈恢复，二者不是空操作。入口从 cpu_sr 初始化后的规范化位置开始，**不是完整 `OS_Sched` 调用**，没有证明外层参数／局部分配、初始化赋值及最终返回／释放的整个调用过程。

## 稳定生产接口

`V293LocalGlobalTrace.v` 的2个根把既有 `V293_local_steps` 提升为原全局执行。`V293_local_steps_global` 输入实际局部轨迹、同一外层 OS 绑定和初始 `goodks`，由原 `loststep_cont_locality`、绑定与 continuation 条件推导每步 InOS，经 `inapi_step / pt_step` 更新实际全局任务代码、局部环境及辅助状态映射；其余任务与 clientst 不变。没有逐步分类 oracle，也没有新增迁移关系。

`V293ReadyCriticalGlobal.v` 有5个根：

- `V293_sched_control_exact`：控制包装与既有完整调度 AST 去掉首个初始化赋值后的定义相等。
- `V293_sched_control_enter`：实际两个 Tint8 load 和变量绑定导出原两道判断，执行进入临界区；任意原中断栈、critical stack 和两种 IE 均保留相应真实结果。
- `V293_sched_control_exit`：从尾段 SKIP 执行真实退出临界区，恢复保存的 IE 和原 critical stack；止于原 sret，不伪造返回。
- `V293_missing_enter_control`：省略进入操作后，退出会弹掉已有外层栈；空栈时原 excrit 无局部下一步。
- `V293_ready_critical_stack`：只运输 ready SWINV 的 critical stack，IE=false、ISR 映射、内存、抽象状态和 interrupt stack 不变。frame 必须满足 `GoodInvAsrt`，不是任意私有资源跨恢复稳定性。

## 同一非空实例，而非分开的假设

探针 `V293ReadyCriticalGlobalProbe.v` 有20个根。它在第140步同一非空 ready＋waiting、实际 TCB、位图、优先级表和只读 lookup 内存上增加两个独立 guard 字节及 cpu_sr 局部单元。保存变量值确为零；入口不把 guard 或 ready 执行结果当成调用者提供的 oracle。

1. `CGglobal_independent_guards`：中断嵌套计数非零或调度锁非零时，真实控制流跳过尾段，恢复原 IE／critical stack、内存不变。覆盖任意合法非零字节组合。`CGinterrupt_only_byte` 和 `CGlock_only_byte` 分别证明仅改变指定一个 guard 字节，所有其他地址不变；不是同一个字节冒充两道检查。
2. `CGglobal_ready`：两字节为零时，从进入临界区连续执行原 `OS_SchedNew` 调用／分配／首次赋值／返回／释放、目标赋值、优先级字节比较和计数器操作，到确切待执行 switch 或 SKIP。使用实际保存的 `enabled::ci` 建立同一 ready SWINV，而非换成虚构空辅助状态。
3. `CGglobal_no_switch_restore`：Ready4／cache=4 分支实际执行退出临界区，恢复两种初始 IE 和任意原 critical stack；计数器仍为 UINT32_MAX。止于 sret。
4. `CGglobal_switch_pending_exit`：Waiting6／cache=6 分支把计数器从 UINT32_MAX 回绕为零，再执行原 `pswitch_step`，实际 current 指针及语义 current 变为 Ready4。**旧任务保留待执行 excrit**，其保存栈仍为 `enabled::ci`；新任务原辅助状态没有被替换成旧任务状态，尚未证明旧任务恢复并执行出口。

编号113绑定完整既有函数体，而不是第140步仅尾段绑定；但本步仍从该函数中途的规范化入口开始，程序含 fixture 绑定，不是生产程序的完整链接／初始化可达性证明。不据此增加整函数信用。

## 事先约定的单因素消融

`CGonly_enter_ablation` 在完全相同程序、内存、guard、尾段和入口辅助状态下**仅删除 encrit**，并给出正反两条真实局部轨迹。令旧栈顶为 `negb enabled`：正例结束仍是原 IE 与原栈；负例结束实际恢复为 `negb enabled`，且丢失一个外层栈帧，两个终点明确不等。两种 IE 都成立。这不是共同提前拒绝，确实执行到原 excrit 并测量结果。

另有 `CGdeleted_empty_stack_boundary` 先证明负例能实际运行到空栈 excrit，再证明此确切端点没有原 loststep。它不是所有全局交错的 stuckness 声明，也不把这个局部负结果当成调度尾段、ISR 或所有下游机制通过。

## 未闭合的义务

实际 switch 后 cache 仍6，但 current 为 Ready4；探针继续证明 `V293_current_task ... Ready 6` 不成立。原 `pswitch_step` 不写 OSPrioCur，本步没有改源或弱化一致性来掩盖它。后置空间断言仍使用原调用者环境，**不是新 current 的完整 CurLINV**。

本步是存在性、无交错轨迹，不是所有交错、所有分配选择或初始化可达性。完整函数入口／返回、旧任务恢复、实际端口同步、完整 API／ISR、Hook／栈、生产全局语义 Inv、WFIFun、GOOD_OS 和同程序 K1–K4 仍开放。uCOS3 未开始，总目标 active；六门仍为 `94/1/1/1/1/0`。

联合实例的 ISR 映射和 interrupt stack 为空；guard 字节虽为实际 load，但没有把非零 OSIntNesting 与活动 ISR 栈建立可达性关系。因此这些实例验证源码检查本身，不是一次真实 ISR 进入／退出的全局执行。通用临界区接口量化 interrupt stack，也不能替代该关系的建立。

## 验证、旧失败与清理

证据目录为 `audit/logs/stage141-ready-critical-global/`。最终状态以独立重算的 `checkpoint-report.json`、`verification.json` 和清单为准，未跑完或失败不算通过。

- 保留所有编译尝试的原日志与快照；稳定版本由 `stable-compiles.json` 指定。新2个生产模块＋探针共27个证明根，逐项 `Print Assumptions`，并对308个活动模块和27个额外探针执行 `coqchk`，不得扩大既有假设集合。
- 新增8项结构／证据身份检查，不把文本匹配当语义证明。全量1821项需与第140步逐项比较失败 ID 集合和错误 ID，旧423失败／1错误不隐藏。旧共同身份提前拒绝不证明下游机制通过；语义信用来自 Coq 独立检查。
- 保留旧 `make audit` 的证据身份过期失败与 `framework/logic/inferules.v` 581–586 空白失败。旧冻结目录与 C／配置／既有 AST／framework／tactics 逐文件身份不改。
- 清理前核对全部一次性 Trust 文件和缓存备份，恢复旧 lia／nia 缓存。只删除本步一次性文件；保留可复用证明产品、源文件、失败日志和快照。

下一步应接入外层完整函数入口／返回并处理 OSPrioCur 同步边界；在无新增源码修复授权时，不自行修改原调度判断或抽象 switch 的行为。未提交／推送。
