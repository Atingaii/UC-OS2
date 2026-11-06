# 第315步：非空 ISR 栈上的 pending 返回与原 TaskSim

## 本步补什么

第314步证明实际分配的 CPU 单元跨切换保持可写，并有合法 `free` 能力；没有执行切出任务的返回。旧 pending-return 证明硬编码空 ISR 栈，不能用于仍保存 `kint` 的中断上下文。

本步增加 `certiucos/v293/proofs/V293InterruptResumedTaskSim.v`，不改固定 C、配置、旧框架规则或冻结证据。核心接口 `V293_interrupt_pending_return_TaskSim` 从已恢复 current 的 pending 状态及 CPU/Core/CurTid 所有权，构造原框架 `TaskSim`。输入没有后继 TaskSim 或 successful-free 假设。

## 实际链路

入口：`SKIP; excrit; sret` 的 continuation 中带函数调用帧、`exint` 和非空 `kint`；低层 IE=false、ISR 栈为 `i::si`、临界栈为 `false::ci`。

实际执行八步：

1. `SKIP` 转到 `excrit`。
2. `excrit` 恢复保存的 IE=false，并弹出一个临界栈元素。
3. 转到 `sret`。
4. `sret` 从实际局部环境取得待释放的 CPU 单元。
5. 原 `sfree_step` 释放单元。
6. 原 `sfreeend_step` 恢复函数 caller 环境。
7. 转到 `exint`。
8. 原 `exint_step` 弹出 ISR 栈顶，恢复中断前环境、表达式和语句 continuation，IE=true。

`V293_interrupt_pending_return_execution` 对任意兼容外部内存 frame 构造这八个原 `loststep`，明确分出释放后的私有堆与原外部 frame；不是只报告释放能力。后续保留 Core/CurTid，CPU 的四个字节被移除。

## 原 TaskSim 的资源连接

- 普通 C 小步接口推广到任意 ISR 栈，不再要求 `si=nil`。
- 关闭中断时，所用不变式正索引槽均为空；单独证明非空 ISR 栈上的共享 `INV` 不占资源，不能靠错误套用只适用于 low=0 的旧引理。
- `exint` 后，Core 从原私有资源重新分到共享 `INV`，CurTid 留给任务；后继受限 scalar 的原 TaskSim 从资源构造，不作为输入。
- 跨 `exint` 改变 ISR 栈不能只用 `good_inv_prop`：它不允许改变该栈。此处使用 `V293_current_core_aux`，再单独处理局部环境变化。

## 非空实例和严格边界

`audit/probes/V293InterruptResumedTaskSimProbe.v` 使用原 builder/切换实例生成的非空堆，分出 CPU/Core/CurTid 与外部 SCframe，绑定同一个 `RDprogram 300`，实例化新 TaskSim 和实际返回轨迹。保存的 caller 是已有非空 shadow 环境，表达式 continuation 也是非空。

**资源重设上下文不等于执行可达性。** `RSrecontext` 仅证明这份资源可满足给定 pending 上下文；没有证明存储的 Ready continuation 或被挂起的 Waiting continuation 能执行到此入口。Waiting 仍阻塞，必须收到等待结果、更新就绪状态并合法重新调度，不能直接改成 ready。

此外，主 TaskSim 限保存 IE=false、所有 IRQ 请求位为 false、受限纯 scalar continuation；入口是已经恢复的 current。实际八步执行接口本身允许任意外部 frame、ISR 尾栈和 IRQ 位，但不自动推出这些更一般状态的 TaskSim。

这是局部任务模拟和实际返回后缀，**不是全局 `ProgSim`，不是统一 WFInt，也不是 GOOD_OS**。初始化、全部交错资源保持、真实 Waiting schedule-back、同程序 K1–K4 与整核纵向连接仍开放；uCOS3 尚未开始。总目标保持 active。

## 下一步：真实唤醒与合法回切

固定非空实例中，`OwnershipReady=(60,0)` 的优先级是4；`OwnershipWaiting=(41,8)` 的优先级是6，正等待信号量 `(72,5)`。定义见 `audit/probes/V293TaskRecordOwnershipProbe.v`。数字较小者优先，因此 Waiting 即使真实收到等待结果并变为就绪，只要 Ready 仍就绪且保持优先级4，就不能据此切回 Waiting。

下一条纵向链必须连接：实际唤醒及等待结果更新 → 高优先级任务经合法 API 阻塞或退出等，使 Waiting 满足调度选择条件 → 原调度器实际回切并恢复保存的 continuation → 本步已证明的返回后缀。仅在满足合法 API 前提时才能选取相应路径；不能直接改优先级、置 ready/current，或把资源上下文重设当作全局回切执行。

当前被选任务的受限 scalar 三步只执行到 `SKIP/kstop`；这本身不是阻塞、任务删除或回切的证明。仍需统一 controls、INV/WFInt 及全局 ProgSim，并证明该入口在同一程序中的可达性，不能再用一个孤立有限见证替代这些开放义务。

## 单因素消融

前瞻协议和结果保存在 `audit/logs/stage315-interrupt-resumed-task-sim/`：只把末端 `sprim exint` 换成 `sskip None`。保留 CPU/Core/CurTid、外部 frame、`kint` 中全部保存内容，以及之前七步的同一证明脚本。

基线通过；变体在七步前缀、实际 free、caller 恢复均建立之后，于原 `exint_step` 返回门拒绝通过。不是 lookup 早拒绝，不把这一个结果泛化为每个前缀机制都已单独检验。最初两组 harness 的导入/数值 scope 错误均保留，只有第三组进入预定晚门并形成有效对照。

## 复现与证据

```sh
D=audit/logs/stage315-interrupt-resumed-task-sim
PYTHONDONTWRITEBYTECODE=1 python3 -B -m unittest discover -s tests -p test_interrupt_resumed_task_sim.py -v
PYTHONDONTWRITEBYTECODE=1 python3 -B "$D/verify.py"
```

最终实测以同目录 `verification.json`、`trust.json`、`full-tests.json`、`cleanup.json` 为准。13 个根包含原 TaskSim 与实际返回轨迹；递归信任边界只允许既有经典逻辑与函数外延，不新增项目公理。旧失败不能通过改门槛、删证据或改旧测试消除；源码与探针的两次稳定编译均记录实际 SHA。

清理仅针对本步生成且已有快照的一次性 Coq harness/信任包装与缓存备份；逐项审阅后共删除17项。保留正式源码和可复用对象、失败日志、源码快照、用户原缓存与全部 306 个原字节码。未提交或推送。

## 已实测的信任复核

13 个根的 `Print Assumptions` 与两个入口模块的递归 `coqchk` 均退出 0；递归复核耗时约438秒。只发现既有 `Classical_Prop.classic` 和 `FunctionalExtensionality.functional_extensionality_dep`。新生产文件和探针各两次稳定编译通过，`make build JOBS=1` 与项目边界审计通过。

新增8项回归通过；完整2776项回归保留原437失败和1错误，失败/错误 ID 及顺序与第314步完全相同，无新增失败。`make audit` 仍因旧函数证据身份过期退出2；`git diff --check` 仍报告原六处空白，日志字节与第314步相同。未改旧证据或降低门槛。
