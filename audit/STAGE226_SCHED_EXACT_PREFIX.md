# 第226步：精确局部资源穿过真实调度前缀并归还存储

## 本步解决什么

第225步的真实 `OS_SchedNew` 契约保留了 `p_local li tid nil`，但旧的上层前缀仍使用较弱的 `CurLINV`。后者包含存在量化和 `Atrue`，不能反向恢复精确资源。本步不改旧证明，从第225步的实际调用继续证明原来的下一条赋值：

```c
OS_SchedNew();
OSTCBHighRdy = OSTCBPrioTbl[OSPrioHighRdy];
```

这段源码前缀由 `OS_Sched` 和 `OSIntExit` 使用。仍以固定配置 V2.93.01 和原 AST 为对象，不增加 C 修复。

## 可供下一层使用的接口

生产文件：`certiucos/v293/proofs/V293OSSchedExactPrefix.v`。

| 接口 | 保证 |
| --- | --- |
| `V293_OSSched_exact_target_assign` | 原 `assign_rule` 执行真实数组读和指针写；精确 scheduler 后置保持不变 |
| `V293_OSSched_exact_critical_prefix` | 直接组合第225步真实 call 与上述 assign，选出任务表中的最高就绪任务 |
| `V293_exact_storage_prefix_lend` | 从既有 closed storage entry 借出数组半权限；从独立 `CurTid` 半权限和空局部不变量直接构造精确局部资源 |
| `V293_OSSched_exact_storage_closed_prefix` | 从既有 closed entry 运行这两条语句，返回完整输入/指针数组、更新的目标指针、共享抽象槽、两栈、名称绑定、`px` 和精确 `p_local` |

最终 `V293_exact_storage_prefix_returned` 不含额外的 `Atrue`，不会用它吸收未知剩余资源。`kept`、`px` 可以由调用者自行包含更弱断言，本步不声称它们必然精确。借出的两份只读权限通过既有 reunite 定理重新合成完整写权限。

`CurLINV` 的单向弱化只用于表达式求值/规则局部侧条件；真实赋值和调用的前后断言仍是精确版本。没有从旧弱后置反推新强后置，也没有要求调用者提供 callee 的 `InfRules` 证明。唯一外部条目要求是 `Spec` 中确实登记新契约。

## 非空与单因素对照

独立 probe：`audit/probes/V293OSSchedExactPrefixProbe.v`。

- 复用既有 closed storage 物理堆见证，不另造一个与前缀无关的空堆。`SPnonempty` 证明同一状态同时满足 closed entry 和本步借出后的 exact entry。
- `SPenvironment` 把原单函数程序接到新规格的 `WFFunEnv`；`SPactual_prefix` 在同一规格中证明原两语句前缀，后置接口按字面给出，包含已选择的字节12。
- 覆盖既有 `different=false/true` 两种任务模式；模式变化同时涉及任务表和指针数组，**不是单因素消融**，也不是两次函数执行。
- 单因素控制直接复核第224步固定状态、只换局部断言的 `RLlocal_exactness_control`：弱断言成立，精确断言不成立。此控制与 storage fixture 是不同 fixture，不能拼接为一条执行。它仅是 local-only 逻辑反例，不是完整前置反例。
- 不声称语义 TDD；Python 测试检查源码结构、身份和核验证据，语义由 Coq 内核检查。

## 边界与未完成事项

callee 的 `V293_opened_inv` 是既有共享 Inv 的空尾：共享内核已由调用者借出，不能再放第二份到 callee。ambient `RI` 保持任意。这不是完整生产 ISR 联合实例。

物理 fixture 使用 `Tptr Tvoid`，具有真实指针字节、完整数组与唯一共享槽，但未增加生产 typed TCB 记录所有权，也不是初始化可达性证明。返回的是 opened storage 及完整物理资源，不声称已关闭完整 ready/TCB ISR 不变量。

**尚未替换原三函数 Spec，尚未贯穿 OSIntExit 的比较、切换和返回。** 完整 ISR、WFInt、生产控制值/lookup、不变量初始化、源码级 GOOD_OS 与同程序 K1–K4 仍开放；uCOS3 未开始。总目标保持 active，不提交或推送继承的脏工作区。

## 实测结果

- 新增5项回归全部通过；全量2294项保留历史423失败、1错误，旧失败/错误 ID 和顺序完全一致，不称全绿。
- 12个根（含复用的局部断言对照）逐根假设与递归 `coqchk` 通过；672份 Coq 输入在检查过程中保持原字节。实际依赖限经典排中律和依赖函数外延性。
- 两次增量构建、两次 project audit 通过；配置后四函数重建一致。原 `make audit` 的 stale function evidence 失败及 `inferules.v` 原空白失败保留。
- 5次生产编译失败与1次 probe 编译失败的快照、错误日志完整保留；最终两个模块编译通过。未新增逃逸证明或项目公理。

## 复核与清理

机器结果以本步 `audit/logs/stage226-sched-exact-prefix/verification.json` 为准。复核包括两次构建、逐根假设/递归 `coqchk`、配置后四函数源码重建、完整回归的旧失败 ID 与顺序。历史 audit 和 whitespace 失败原样保留，不称全绿。

先列明本步一次性信任驱动及产物，再删除；恢复原 `.lia.cache/.nia.cache`。保留新源码、失败编译快照/日志、可复用依赖与 Coq 构建产物。
