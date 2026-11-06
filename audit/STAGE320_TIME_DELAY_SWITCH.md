# 第320步：延时阻塞后执行比较、计数器和原框架切换

## 前因后果

第319步已从 `OSTimeDly` 实际阻塞接到 `OS_Sched()` 调用、helper 分配释放及目标指针发布，但 current 尚未切换。本步消费这个生产接口，不将输入任务重新设为 ready，也不把已发布的目标指针等同于切换完成。

本步新增生产文件 `certiucos/v293/proofs/V293TimeDlySwitch.v`，暴露三个接口：

| 接口 | 已构造的事实 | 不作为输入的结果 |
| --- | --- | --- |
| `V293_sched_change_raw` | 实际字节优先级比较、分支、自增存储和读回；模2³²加一 | 已完成的执行、给定后继堆或成功存储 |
| `V293_sched_call_to_switch` | 从真实 `scall` 接到比较／计数器完成、停在 `switch`；CPU可写、helper释放及frame | callee执行、后继模拟、当前任务仍就绪 |
| `V293_sched_switch_commit` | 从当前指针四字节写权限构造存储，再应用原 `pswitch_step` 得到 `lpstep` | 预选最终堆、给定存储成功、SWINV或ProgSim |

没有修改任何旧生产接口、测试或冻结证据。新生产文件不导入审计实例。

## 源码身份

目标仍为固定 V2.93.01 提交 `0c4a48e6fbc6e915714e816196619a5481accf0c`、原配置和两类授权修复。独立重新物化源码并执行 clang 预处理，三函数身份与旧库存逐项核对。

| 函数 | 源码位置 | 配置后定义 SHA-256 |
| --- | --- | --- |
| OSTimeDly | os_time.c:53–81 | c8626621a399e6f622e6d311d943d098e182b4cdcd5aaa5ccf21d7215be08519 |
| OS_Sched | os_core.c:1702–1732 | 59d34e6ebeb338b71ea2e2969fb66a28c413acc71835430b35334bc15ab8a61d |
| OS_SchedNew | os_core.c:1751–1776 | 6d156edfff0548ed63fdff59a400e8d0ca0e69813ef6bf0142d0ce1902443d71 |

证据位于 `audit/logs/stage320-time-delay-switch/source-identities.json` 及源码快照。人工规范化 AST 的身份核对不是自动 C 翻译正确性证明；`function-boundary.json` 不将局部连接登记为完整函数覆盖。

## 非空实例究竟证明了什么

`DWblocked_run` 从同一块完整所有权堆实际执行延时函数体、原 `spec_step`、调度调用、比较及自增。当前任务优先级4，ticks=3；另一任务优先级6且已经ready是输入事实。末端同堆保留全部任务记录、位图关系、CPU保存单元可写、helper已释放以及值99的canary。

`DWblocked_switch` 随后消费同一末端堆，在**原框架 `lpstep`** 中由4切到6，写回 current TCB 指针，保存切出任务的 `SKIP` 与原 `DScontinuation`。被选任务具有非空表达式代码，其代码、环境和辅助状态均保留；没有声称其表达式已经继续执行。切出任务的CPU写权限、任务记录、计数器和canary跨切换保持。

`DWselected` 证明6是阻塞后任务表中的最高就绪；`DWhigh_switch` 应用原 `hswi_step`，在同一阻塞后抽象任务表上更新抽象 current，并保留旧高层 continuation。低高层实例共享所选任务和任务表，但**不是完整前向模拟证明**。

`DWboth_IE` 对同一 `DSprogram`／`DWprog` 检查初始IE=true及false；`DWwrap_run` 另实际执行初值 `0xffffffff` 的计数器，读回0，不把无符号自增当作无界自然数加法。

## 优先级缓存是一个明确的未闭合边界

原框架 `pswitch_step` 仅写 current TCB 指针，不写 `OSPrioCur`。本实例保留优先级缓存4，同时 current指针已经变成6对应任务。**不能将其称为完整源码／port缓存同步或完整调度器返回。** 现有接口和协议均保留该限制，未私自修改框架规则、源码或授权修复集。

源码级目标接受任务切换原语边界，不因此扩展为ABI、汇编、二进制或硬件证明；但后续共享不变量／恢复接口必须如实处理缓存字段，不得假设它已同步。

## 前瞻、单因素的片段级消融

执行前冻结 `ablation-protocol.json`：只将 wrapper 的 `DSWcount := true` 改为false，删除已进入比较／尾部片段中的计数器自增，比较条件、目标、切换规则及资源门均不改。

`DWablation_run` 的量词顺序先取得同一输入堆 `Mr`、CPU块和helper块以及实际延时／调度前缀，然后才对任意count构造尾部和物理切换。因而不是分别选择两份不同前置堆。两者都先完成尾部执行、原 `lpstep`、current指针读回、全部任务记录、canary、CPU写权限及helper释放，最后才检查“计数器恰好加一”。基线通过；变体在 `exact Counter` 被拒绝，计数器保持0而非1。

这是**片段级消融**：原始前缀和输入堆相同，变体尾部不再是原函数的原始函数体，因此不声称证明了完整变异函数调用。两组有效重放为 `gate-*-03` 和 `gate-*-final`；首两组分别因缺少 `V293_cpu_lenv`、`V293_task_records` 的直接导入而提前失败，不计作机制验证。失败源码快照和日志全部保留。

## 仍未证明的内容

- 不是完整 API：`OSTimeDly` 入口仍在cpu_sr初始化之后，未证明其外层调用分配；没有旧任务恢复、调度器返回或原调用返回。
- 不是全局记录不变量：有限无交错执行，未证明任意中断交错保持全部资源。
- 不是 raw port：沿用规范化原语与接受的切换抽象，不声称method3实现或优先级缓存同步已验证。
- 低优先级任务已ready是输入条件，不是从此前真实Waiting状态唤醒。
- 局部前缀仍为 `V293_local_steps`，末端才接原全局一步；没有将整段称为全局轨迹或全局 ProgSim。
- 统一WFInt／全局ProgSim、初始化、最终GOOD_OS和同程序K1–K4仍开放。uCOS3尚未开始，总目标保持active。

## 复核与交付

机器可读结果见 `audit/logs/stage320-time-delay-switch/verification.json`；它仅验收本步局部检查点。递归复核和Python证据核对的职责不同；Python通过不替代Coq内核检查。

| 实际检查 | 结果 | 解释 |
| --- | --- | --- |
| 生产接口、审计实例重复编译 | 各两轮通过 | 输入源码哈希在每次编译前后不变 |
| 18个证明根及递归 `coqchk` | 通过；递归检查254.337秒 | 仅沿用已有classic／funext_dep假设边界 |
| `make build JOBS=1` | 通过 | 增量构建，不是独立净目录重建 |
| 新增回归 | 两轮均8项通过 | 覆盖接口边界、非空实例、回绕及消融证据 |
| 全量回归 | 2812项，438失败、1错误 | 相比第319步增加8项；失败／错误ID及其顺序逐项相同，不是全量通过 |
| 项目注册审计 | 395个活动V293文件＋103个framework／tactics文件 | 文件注册数量，不是函数正确性覆盖率 |
| `make audit` | 旧身份错误仍失败 | `stale function evidence input identity`，未改旧证据制造通过 |
| `git diff --check` | 旧六处空白问题仍失败 | 输出与第319步逐字节相同；新增交付另查行尾空白 |
| 一次性产物清理 | 逐项核对后删除17项 | 恢复原lia／nia缓存；保留306份原pyc及全部失败快照 |

旧失败不删除、不改测试期待来制造通过。`make audit` 的旧覆盖身份失败以及 `git diff --check` 的六处旧空白问题原样保留。新增交付文件另查换行／行尾空白；旧文档仅前置新说明，`_CoqProject`仅尾加生产文件。清理目标逐项核对后仅移除本轮一次性wrapper／Trust及其产物，恢复旧缓存，保留306份原pyc、可复用证明依赖和全部失败证据。未提交／推送。

下一步应连接被选任务的后继执行、切出任务的恢复及缓存／资源契约，再整合统一TaskSim／WFInt／ProgSim；不能将当前有限切换实例升级为整核结论。

在项目根目录核对：

```bash
PYTHONDONTWRITEBYTECODE=1 python3 -B audit/logs/stage320-time-delay-switch/verify.py
PYTHONDONTWRITEBYTECODE=1 python3 -B -m unittest discover -s tests -p test_time_delay_switch.py -v
```
