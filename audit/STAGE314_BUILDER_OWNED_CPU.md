# 第314步：真实 builder 分配的 CPU 单元写权限保持

## 这一处缺口是什么

第312–313步已连接真实中断入口、builder 前缀、低／高层任务切换和被选任务的三步标量执行。但旧前缀接口将新分配的 CPU 局部单元弱化进 `Atrue`：值能读出来，不等于还持有释放它所需的写权限。因此不能从旧接口直接得到返回时的合法释放。

本步保持固定 C、配置、AST 和执行规则不变，只加强资源结论。实际分配产生的
`Amapsto (bs,0) Tint32 true (Vint32 Int.zero)` 从 Exit 入口一直保留到同堆物理切换，再保留到被选任务三步执行之后。**得到的是释放能力，不是执行了释放，更不是使等待任务立即就绪。**

生产接口：[`V293InterruptBuilderOwnedCPU.v`](../certiucos/v293/proofs/V293InterruptBuilderOwnedCPU.v)。
同程序连接实例：[`V293InterruptBuilderOwnedCPUProbe.v`](probes/V293InterruptBuilderOwnedCPUProbe.v)。
前瞻协议和原始结果：[本步记录目录](logs/stage314-builder-owned-cpu/)。

## 接口与真实执行链

| 根定理 | 可检查结论 | 保留的边界 |
| --- | --- | --- |
| `V293_builder_dispatch_owned_cpu_prefix` | 从原 `BuildintPre`，复用真实 Enter、Exit 局部变量分配和缓存拷贝，输出调度切点与可写 CPU 单元 | 未过滤原 builder 入口；函数绑定、缓存／lookup 一致性等仍是输入 |
| `V293_pending_exit_owned_progsim` | 从 CPU 所有权构造原 `free` 的成功结果与精确剩余断言，交给已有 pending-exit `ProgSim` 接口 | 必须已真实恢复到该任务／代码／环境／aux，且提供 caller 后继 `ProgSim`；不证明自动恢复 |
| `V293_cpu_first_permission` | 只改首字节 permission 时，所有字节值和其他地址不变；`load Tint32` 不变，`free Tint32` 返回 `None` | 原内存模型的事实，不是任意外部干扰保持定理 |
| `OCprepare` | 非空原始见证经实际 `pint` 和局部到全局提升，到达同一强资源切点 | 原 `BGglobal`、非空 caller、EOI／Enter／normalized Exit，不是重造的步关系 |
| `OCafter_core` | 原切换后同堆资源重新分成 current core、当前任务与 CPU 外部帧 | 使用被选任务真实空 local env 和 aux，而不是旧任务的 CPU local env |
| `OCpartition` | 原 `INV`／`RDYINV`／`LINV`／外部资源分区及原框架受限 `TaskSim` | CPU 所有权在外部帧中，没有伪装成被选任务的 `LINV` |
| `OCcompleted_owned` | 同一真实全局前缀、低层物理切换与高层调度连接上述分区 | 切出任务仍保留 pending exit、`kint` 和非空 caller |
| `OCrelease_capability` | 原 `free` 确实成功；四个字节删除，范围外地址不变，剩余堆满足精确断言 | 能力见证，不是低层执行 `free` 的一步 |
| `OCcompleted_client_cpu` | 同一 `Mf` 上连接三个原低／高层标量步，之后仍有上述释放能力 | 全局轨迹末端仍是 `Mf`，不是释放后的 `Mr`；`TaskSim` 是切换切点的 `CSready` 模拟 |

具体实例保持：旧任务 `OwnershipWaiting` 仍阻塞，不改为就绪；新任务为最高就绪 `OwnershipReady`，优先级4；程序为原 `BGglobal`。被选任务执行常量求值、位取反、语句 continuation 消去三步，OS 堆不变。这里不能泛化为任意被选任务、任意 API 或任意中断交错都保持外部 CPU 单元。

## 为什么读取成功不能代替所有权：单因素对照

协议在运行前冻结于 `ablation-protocol.json`。正常版和破坏版都先构造完整真实轨迹、同堆分区、原 `TaskSim` 和三个原低／高层步骤；地址 `bs`、首字节的 byte 值、其余地址和全部证明脚本保持不变。

唯一差异是最后释放能力检查所使用物理堆的首字节 permission：

```coq
(* 正常：重设成原 true 权限，物理堆与 Mf 相同。 *)
free Tint32 bs (set Mf (bs,0%Z) (true,byte)) = Some Mr
(* 破坏：同值但撤掉首字节写权限。 *)
free Tint32 bs (set Mf (bs,0%Z) (false,byte)) = Some Mr
```

正常版通过，破坏版在 `exact Free` 晚拒绝。错误上下文保留 `Full`、`Low`、`High`、`Task`、共享／外部资源、`L1`／`H1` 以及 `BaseRead`、`ReadOnly`、`Denied`。不是用早期 builder 失败冒充所有下游门都有效。

`V293_cpu_first_permission` 直接按原 `loadbytes`／`freeb` 规则证明：同值只读堆仍可读出32位零，但不能释放。这个对照说明本实例的释放依赖写权限，**不是删除程序语句的消融，不证明任意写入或中断都保持资源，也不证明修改后的完整程序可达。**

## 对抗性复核与未完成项

| 可能的错误推论 | 本步如何处理 |
| --- | --- |
| “读到零，所以可释放” | 用真实分配的 `Amapsto ... true`，并以同值只读反例排除该推论 |
| “另外找一块可释放堆即可” | 所有权、三步执行和释放能力共用同一 `Mf`、同一分配块 `bs`；不是另造 witness 堆 |
| “已释放旧任务 CPU 局部变量” | 没有把 `Mr` 接到全局执行轨迹；旧任务仍暂停，释放只是能力结论 |
| “因此旧任务会恢复” | 不假设公平性；没有收到等待消息／真实唤醒和调度，就没有恢复结论 |
| “所有权 wrapper 已闭合后继模拟” | `V293_pending_exit_owned_progsim` 显式保留 current、真实 pending 上下文和 caller `ProgSim` 输入 |
| “原 TaskSim 说明所有中断交错正确” | 它只覆盖原受限标量形状，不是全局 `ProgSim`；中断全交错仍开放 |

优先继续的义务是：在真实可恢复路径中保存／恢复切出任务资源，并证明被选任务及中断干扰下的资源保持；用实际 caller 后继模拟调用条件返回接口。不能为了套用返回定理直接改 Waiting 为 ready 或假设 current 已恢复。

统一 handler、精确 controls 与 unfiltered `WFInt`、缓存／lookup 一致性的初始化与全程序保持、初始化及全函数纵向连接、最终源码级 `GOOD_OS` 和同程序 K1–K4 仍开放。uCOS3 尚未开始；两阶段依次完成才是最终目标。normalized port／IRQ 是接受的源码证明边界，硬件／raw port 不阻塞当前目标。

## 验证与历史保留

生产与 probe 各稳定编译两次；9个根执行 `Print Assumptions` 和递归 `coqchk`，只接受既有 `classic`／`functional_extensionality_dep`，不新增证明公理。具体退出码、源码 SHA 和命令见 `trust.json`、`*-stable-*.json`；回归实测见 `full-tests.json` 和 `verification.json`。

新增8项回归两次独立运行均通过；完整测试实测2768项，原有437失败、1错误的 ID 和顺序与上一步完全一致，没有新增失败，不删除旧失败来制造通过。旧 `make audit` 的 stale function evidence 身份错误、`inferules.v` 六处旧空白问题继续如实记录，不能将局部检查通过称为全仓健康。

本步前4274项基线、上一步130项清单中不允许变动的127项、306个既有 pyc 均按原字节核对；根 `.lia.cache`／`.nia.cache` 复原。仅 README／状态页前置本步说明、`_CoqProject` 追加生产模块及生成依赖允许变动；旧测试、冻结源码／证据不改写。17项临时门文件、信任入口／产物和缓存备份在逐项核对后清理，保留快照、失败日志、runner、正式源码、probe 和可复用验证对象。

复核命令（在仓库根目录执行）：

```bash
PYTHONDONTWRITEBYTECODE=1 python3 -B audit/logs/stage314-builder-owned-cpu/verify.py
```

没有执行 Git 提交或推送；目标保持 active。本步完成不等于整个 `GOOD_OS` 已完成。
