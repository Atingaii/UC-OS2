# 第87步：两个真实 Hook 之间的优先级表写入 Hoare

## 本次推进了哪一段

固定 V2.93.01 的 `OS_TCBInit` 在18个字段初始化后依次执行：

```text
OSTCBInitHook(ptcb)                         ← 尚未兑现的 CPU Hook
进入临界区
OSTCBPrioTbl[prio] = ptcb                   ← 本次直接证明
退出临界区
OSTaskCreateHook(ptcb)                      ← 尚未兑现的 CPU Hook
发布到任务链表、设置 ready 位、计数、返回0    ← 尚无该段框架 Hoare
```

原 C 的这段位于 `os_core.c` 约2117行起；完整函数的锁定范围仍是2022–2151行，实际哈希见本步 `source-identity.json`。没有修改源码、模型函数体、固定配置或两类授权修复。哈希核对不是已验证 C 翻译器。

## 可供上层调用的接口

新增活动模块 `certiucos/v293/proofs/V293TCBPriorityHoare.v`：

- `V293_OS_TCBInit_priority_store_hoare`：真实数组赋值的 `InfRules`。从参数内存读 `prio`，计算 `4*prio`，从局部内存读 `ptcb`，用框架 `assign_rule` 的既有通用包装完成写入；没有把 evaluator 或执行轨迹当作前提。
- `V293_OS_TCBInit_priority_bracket_hoare`：无 Hook／后续段前提的 `encrit; store; excrit` Hoare。
- `V293_OS_TCBInit_priority_bracket_semantics`：通过框架 `RuleSound` 得到同段 `RuleSem`，不是另一个独立终止证明。
- `V293_OS_TCBInit_suffix_split_hoare`：保留原始真实 suffix；只开放两个独立 `scall` 和发布／返回段三个 Hoare 义务，优先级表写入不再是开放前提。
- `V293_OS_TCBInit_nonempty_body_split_hoare`：利用第86步已证的实际非空前缀，把上述拆分连接到既有完整 `V293_TCBInit_function_body`。入口两局部和18字段均可为 `Vundef`。

`priority_then_hoare` 仅用于保留既有 suffix 的右结合 `sseq` 形状；没有改模型语法来简化证明。

## 资源和临界区边界

新增资源只有被访问的一个优先级表槽（4字节）、全局表绑定，以及不存在局部遮蔽的事实。用一个等价资源视图把该槽搬进第86步的 frame，不复制权限。

- 泛型优先级满足 `p < 13`；旧槽值任意，允许 `Vundef`。
- 入口中断明确关闭；临界区栈 `cs` 任意，退出后恢复同一 `cs`。
- 泛型 frame 必须 `GoodFrm` 并提供 `CurLINV`。
- 两个 Hook 义务要求在所选断言下返回并保留其拥有的资源；这是真实开放的调用级义务，不是已经实例化的 `call_rule`／端口函数实现。它们并未假定整个内存恒等，但所拥有的精确资源仍必须满足后置断言。
- 仍不是调用分配／free 的 Hoare，也不是整函数 `WFIFun`。

## 独立可满足实例和控制

`audit/probes/V293TCBPriorityHoareProbe.v` 不导入任何历史探针；其字面布局独立构造：

- 30个核心单元85字节，包含18字段、7参数、`ptcb`、`cpu_sr`、free-head、`OSTCBNext` 和优先级11的槽；
- 加只读当前任务指针4字节与哨兵1字节，共32个单元90字节；
- 联合证明原非空入口（18字段、两个局部、表槽全 `Vundef`）和第一 Hook 返回后的具体入口（字段已初始化、表槽 `Vundef`）；
- 无条件实例化 bracket；完整函数实例明确保留三个后续义务；
- `PrioritySlotRead` 给出 post 槽的真实 load，`PriorityWrongSlotRead` 排除 NULL；`PriorityFreeHeadPreserved` 独立检查 free-head 不被该段改写。

前瞻负控只将同一后置槽值 `ptcb` 改为 `NULL`，其他入口、语法、所有 post 单元、frame、证明体和 imports 保持不变。它只检查接口是否拒绝错误槽规格，不给后续 Hook／发布授信；真实 post 读取另有定理。

## 验证和仍然开放的工作

编译尝试（含失败）、快照、控制计划、构建、测试、内核检查及清理记录均保存于 `audit/logs/stage87-tcb-priority-hoare/`；以最终 `final-report.json` 和冻结 manifest 为复核入口。新增6项 Python 检查是结构回归，不能替代 `coqc`／`coqchk`。

正式六门仍为 `94/1/1/1/1/0`。本步不升级函数覆盖，不声称测试全绿或默认审计通过。下一段应直接证明真实 `V293_TCB_publish` 的链表／ready 位／计数／返回，再处理实际 CPU Hook 的规格和实现连接；随后才是整函数 `WFIFun` 和全局初始化连接。

整个源码级 `GOOD_OS`、同程序 K1–K4 和 uCOS3 均未完成，目标保持 active。
