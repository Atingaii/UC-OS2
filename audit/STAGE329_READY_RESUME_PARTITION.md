# 第329步：完整就绪资源的运行时分割与恢复后缀

## 要解决的具体连接

第328步已经从同一原始客户端调用到达真实全局切换，交付新任务视图下的 `ready_full next ** frame`。但原框架要求区分共享 `INV`、每任务 `RDYINV` 与外部 frame，不能把完整堆同时交给共享区和任务区。新活动任务实际 `IE=true`，更不能沿用旧任务关闭中断时的资源分配。

本步只补这个连接，并将既有不变量无关的恢复后缀 `TaskSim` 专门化到**同一个完整 `ready_inv`**。没有新造弱不变量，没有修改 C、AST、框架或旧证据。

## 新生产接口

文件：`certiucos/v293/proofs/V293ReadyResumePartition.v`。

| 接口 | 已证明的内容 |
| --- | --- |
| `V293_ready_full_core_halves` | 完整就绪所有权恰好等价于完整 core 加任务当前指针半权限；反向重组须由实际共享字段证明 current 一致 |
| `V293_ready_full_runtime_partition` | 在同一总堆/抽象图中得到 `(INV ready_inv ** RDYINV ready_inv t) ** R`，外部 `R` 原样保留 |
| `V293_ready_enabled_empty_rejected` | 选中任务保持 `IE=true` 时，空共享内存和空抽象图不满足原 `INV` |
| `V293_ready_full_pending_TaskSim` | 从真实函数绑定、CPU槽、完整就绪资源和有限客户端后继，构造退出临界区、返回、释放局部CPU槽至客户端的原 `TaskSim`，不把执行或仿真结论当输入 |
| `V293_ready_full_resume_callback` | 保留已保存的CPU局部，但对任意合法恢复共享堆 `Mc`、抽象图 `Oc` 及其 join 提供后缀仿真，不冻结旧共享状态 |

启用中断时 core 放共享区、当前指针半权限放任务区；关闭中断时共享区可为空，完整 core 与任务半权限一起放任务区。两边是可分离子资源，不是两个完整副本。无ISR标志、关闭中断时的栈顶界等前提保持显式。

## 同堆实例与事前单因素对照

文件：`audit/probes/V293ReadyResumePartitionProbe.v`。

- `DRglobal_partition` 直接使用第328步的真实全局执行末端，而非重新拼一条不同堆的轨迹；保留全部 `DOcells` 读取以及两块CPU槽的4字节写权限。
- `DRglobal_partition_pieces` 给出共享、任务、frame 三份内存/抽象图及精确 join。共享和任务不变量满足 `satp`，不是只对某个抽象操作成立的快照；共享区不能同时是空堆和空图。
- `DRboth_IE` 覆盖原始调用的两种IE。无论原任务如何开始，新选任务仍用真实 `IE=true`。
- `DRenabled_placement_ablation` 按 `protocol.json` 的事前协议只中和**共享资源放置**：保持同一实际执行、总堆、记录、位图、表、计数器、canary、两CPU槽与新任务IE，把完整core全留任务侧、共享侧置空。正例资源门均已成立，晚期 `INV` 门拒绝这个空共享候选。它不是突变程序执行，也不检验所有下游机制。
- `DRrestored_suffix` 从真实调度前缀末端的非空联合资源拆出任务后缀与外部frame，支持两种保存IE；使用实际调度函数绑定。但返回上下文专门取 `kstop`，**不是实际嵌套返回**，不把该上下文替换伪装成原 `DAcontinuation` 的执行。

## 信任检查与回归

最终结果以 `logs/stage329-ready-resume-partition/verification.json` 为准；成功编译、递归信任检查和全量回归分别记录，不能互相替代。

实测：生产与探针各两轮稳定编译通过，全部14根递归 `coqchk` 通过，883项Coq输入在检查期间保持不变。构建、项目审计和新增8项测试通过。两轮全量均为2884项、439失败、1错误；与第328步的旧失败/错误身份及顺序完全一致，无新增失败。总体 `make audit` 仍因旧的函数证据输入身份过期退出2，`git diff --check` 仍为原6处空白错误，未改写为通过。

原始失败快照与日志保留。新增Python测试核对接口、身份和范围，不作为Coq语义证明的替代。`Print Assumptions` 和递归 `coqchk` 另外检查生产及探针的全部14个根。

## 边界与下一步

这是完整就绪资源到运行时分割及通用恢复后缀的局部桥接，**不是完整 API，不是全局 ProgSim，不是 GOOD_OS**。

`ready_full` 是资源关系，不自动证明旧阻塞任务已经唤醒或具有再次运行资格；prefixcut后缀实例也不提供这个事实。恢复后缀以原任务已获得自身完整资源及CPU槽为前提，**不是旧任务恢复可达性**。选中新任务不等于旧任务恢复；不能将前者的资源直接交给旧任务。`kstop` 有限后继也不等于真实 `OSTimeDly -> OS_Sched -> 客户端` 的嵌套 continuation。下一步应处理真实嵌套 continuation，并证明旧任务恢复后如何获得所需资源，而不是把它们当作已完成。

完整记录/位图/表已保留，但全局记录不变量、优先级缓存同步、任意API/中断干扰、统一 `WFInt`、初始化、源码级顶层 `GOOD_OS` 及同程序 K1–K4 仍开放。缓存仍可能是4而选中high为6；本步不改写该事实。原helper释放只在早先 `Mh` 边界，不能升级为最终整块fresh。

三函数六阶段保守覆盖不升级，函数级 `local_hoare/component_linked/full_target_linked` 尚未闭合。清理前逐项审查并移除本步10项一次性信任驱动/对象和缓存备份，原4缓存字节恢复，306个既有pyc保留；复用证明对象、失败快照和交付证据保留。生成Makefile的mtime恢复为早于 `_CoqProject`，后续构建会重新生成它。

第一阶段整核目标未完成，uCOS3 尚未开始；总目标保持 active，未提交或推送。
