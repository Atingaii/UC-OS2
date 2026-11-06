# 第217步：将就绪/TCB/存储不变量接入真实退出尾段

## 为什么继续做这一步

第215步的完整退出 builders 和统一函数规格使用旧 storage Inv。第216步建立的候选 Inv 同时持有 ready/TCB 语义资源与 dispatch/control 存储，但断言资源等价不能自动更换 `InfRules` 的 Inv 索引。因此本步直接在新 Inv 下重建真实语句证明，而不是宣称旧证明已全部迁移。

固定目标仍为 uC/OS-II V2.93.01、锁定配置及原授权两修复。没有修改 C、配置、AST、框架、tactics 或既有证明。源码身份从实际预处理后的 `OSIntEnter`、`OSIntExit`、`OS_SchedNew`、`OS_Sched` 重建，证据在本步 `source-check.json` 与 `source-recheck.json`。

## 本步纵向连接

1. `V293OSIntExitReadyHandoff.v`：在同一 `V293_ready_storage_inv` 下证明计数器递增、skip、缓存复制和原始 switch 的 `InfRules`。切换前把 ready 位图、优先级指针表、TCB 记录、目标指针和控制存储关闭到 Inv。
2. switch 的可保留 frame 由环境绑定和调用者提供的 `px` 组成，不把本次使用的 ready/TCB 所有权留在切换后。恢复后后置只有同一 Inv、原线程身份、临界栈/中断栈、frame 与剩余抽象动作，不冻结本次消耗的共享值。这里的“私有”仅指规则可保留的 frame；通用接口只要求 `GoodFrm px` 与局部不变量义务，不等于已完成全程序 C 访问权限分类。
3. `V293OSIntExitReadyDispatch.v`：连接实际 `OS_SchedNew` 调用、目标赋值、不同优先级 guard 和上述尾段。完整输入数组重组成 ready payload，lookup 数组转成带类型存储，最后一起关闭到新 Inv。
4. 调用边界仍要求环境中实际 callee 规格的 lookup 等式；没有把完整退出或调度本体的 Hoare 结论当作前提。本步没有建立新的完整函数环境闭包。

主要上层接口：`V293_OSIntExit_ready_dispatch`。它仍是已打开资源和不同优先级分支上的局部接口，不是完整 `OSIntExit` 的生产 builders 接口。

## 独立非空入口

`JHtail_nonempty` 使用既有独立字节内存和真实 call/guard/counter 执行前缀得到具体堆；从实际内存及固定抽象任务表构造新尾段的前置。目标指针命名信息必须在分离子状态中显式保留；探针原有自动化会过早拆掉该信息，本步用真实全局环境构造具名目标再重组。

见证把可变抽象动作从 `spec_done None` 改成 `sched;;aop`，只证明逻辑断言可满足，不声称这个 token 变更是一条程序执行。实际调度命令和切换执行证据另由下面消融给出。

## 前瞻单因素消融：仅删除缓存复制

固定同一 `M`、环境、任务映射、目标、原 switch、调用栈与控制状态：

| 变体 | 实际尾段 | 原 switch | 切换后缓存 | 新共享 Inv |
| --- | --- | --- | --- | --- |
| 保留复制 | `OSPrioCur := OSPrioHighRdy; switch target` | 实际 `lpstep` | 4 | 保持 |
| 删除复制 | 直接 `switch target` | 实际 `lpstep` | 6 | 保持 |

`JHcopy_ablation` 同时给出实际 `cstepstar`、真实 byte store、复制不改变其他字节，以及两侧原始 `lpstep` 和新 Inv 后置。两者的初始堆是同一个 `M`，不是两个入口编码拒绝实验。`JHswitch_result` 中共享资源均在 Inv，frame 明确为 saved 单元与既有 `RCframe`（canary 单元及 lookup 只读字节）；这些是本次不写的分离资源，不等于应用层线程私有数据。具体 handoff 夹具的 `JHcells` 不包含该 lookup 数组；生产 dispatch 接口则将其完整拥有的 lookup 数组转成存储关闭到 Inv，不能把局部后缀夹具误报成完整生产 dispatch 的非空入口。

这里的 `M` 已执行现有 counter 前缀，counter 为 0。因此只比较 handoff 局部后缀，不再把 `changed_tail` 的 increment 应用于同一完整调用，也不声称执行了两份完整 `OSIntExit`。缓存 4/6 差异证明复制改变可观察值，同时明确新 Inv 仅保证这些控制单元的类型/所有权，尚不包含 cache/current 值关系。

## 验收与旧失败

实际结果和逐根假设以 `audit/logs/stage217-ready-exit-handoff/verification.json`、`trust.json`、`assumptions-by-root.json` 为准。全部失败编译快照和诊断输出保留；不会把失败试验覆盖为成功。源码重检期间一次包装器 label 与子命令 JSON 同名的记录错误单列于 `evidence-recording-incident.json`：保留包装器输出，使用独立 label 重新重建并与初始报告逐项比较，没有改写旧冻结证据。

本步新增五个结构回归，它们核对接口、来源、实验结构和稳定编译身份，不冒充语义 TDD。语义证据是 Coq 定理和内核检查。全量 tests 保留原有 423 failures、1 error 的身份与顺序；`make audit` 和空白检查中的既有失败也保留，不为制造通过而弱化门禁。

## 尚未完成

- 新 Inv 尚未接入完整退出本体、真实 builders、三路径统一 Spec 和生产函数环境。
- lookup 内容语义、控制值语义及 cache/current 关系未成为此 Inv 的通用保证。
- 本步不建立所有 ISR、生产 LocalInv、WFInt、全初始化、任意交错或硬件/ABI 正确性。
- 归一化 handoff 按 ADR-0010 处理，不把它误写成原端口外部函数体实现。
- 六阶段覆盖仍为 `94 / 1 / 1 / 1 / 1 / 0`；`GOOD_OS`、同程序 K1–K4 仍开放，uCOS3 未开始，总目标保持 active。

下一条主线是把新 Inv 的 dispatch 接到完整退出本体与 builders，而不是再增加无上层用途的旁支文件。
