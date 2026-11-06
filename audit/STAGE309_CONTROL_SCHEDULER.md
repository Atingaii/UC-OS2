# 第309步：固定控制前端连接原高层调度规则

## 这一步解决什么

旧 `spec_step` 保持 `curtid`；只证明 Exit 进入 `sched`，并没有证明任务发生切换。第308步完成不调度路径的实际中断返回，本步补齐高层调度接口，不改旧框架及其已冻结证据。

生产模块：`certiucos/v293/proofs/V293InterruptControlScheduler.v`。
非空实例：`audit/probes/V293InterruptControlSchedulerProbe.v`。
前瞻协议及实测：`audit/logs/stage309-control-scheduler/`。

## 最小接口与不变量

- `None` 事件恰为旧 `V293_control_step`，空事件轨迹与旧多步双向等价；不是重新实现一套任意 Core 操作。
- `Some(old,next)` 必须满足同一旧 `O` 的实际 `curtid=old` 与原 `sd O next`。不提供任选目标规则；V293 实例复用原最高就绪任务关系。
- `V293_control_switch_hpstep` 把 Core 调度事件映射到框架原 `hswi_step`。更新旧任务的后继代码、把 `curtid` 设为目标，保持 `clientst`、三个控制字节、其他抽象键及其他任务项。
- `V293_control_handler_switch`、`...quiet`、`...self` 为同一固定 handler 提供有限轨迹。当前已最高时可用原局部调度规则而不发生切换。
- `...target_exact` 给出目标与同一抽象任务表最高就绪关系的双向刻画；唯一性另外要求原优先级表不变量。

## 实际执行与非空任务图

`CScompleted_coupling` 不把执行轨迹作为输入。它先调用已证明的 `SXcomplete_prefix`，取得原程序 `SXprogram` 的真实 Exit 调用轨迹、后继堆 `Mf`、目标指针 `OwnershipReady`、计数器20和保持的资源，再捕获后继控制字节 `(1,0,0)`。随后在同一 `RIabstract OwnershipWaiting` 上取得上述高层调度步骤。

高层任务表同时含等待任务和就绪任务；表达式 continuation 为 `keop1 negation ...`，语句 continuation 为 `kseq ...`，均非空。调度后旧任务代码只消费 `sched`，就绪任务代码项保持，当前任务从 `OwnershipWaiting` 变为 `OwnershipReady`；两个 tid 确实不同。初始 IE 开/关及任意保存临界栈均可实例化。

这里物理实例从 Exit 入口深度1开始，**不声称它已执行 Enter**。另一个完整高层 handler 结论从深度0执行 Enter/Exit；两个切点的联系不能替代尚缺的整体模拟证明。已完成的第308步实际 quiet 返回通过空事件轨迹的精确嵌入继续可用，未换成另一份 C 程序。

## 前瞻消融与反向检查

1. **规则移除的数学对照**：`spec_step_tidsame` 推出所有空事件轨迹保持 `curtid`；因此同一等待任务实例删去切换事件后不可能得到当前就绪任务的终态。这隔离了新增全局切换规则的必要性，不声称任何下游机制因此自动正确。
2. **错误目标**：当前等待任务不是最高就绪任务，不能作为本例目标，已由 `CSwrong_target_rejected` 证明。
3. **完成后的单因素观察**：运行前冻结 `ablation-protocol.json`。先取得实际源码前缀、目标、后继捕获、事件轨迹、原 `hpstep` 及其他任务项；仅把最终期望 `curtid` 从 Ready 改为 Waiting。基线编译成功，变体在最后使用 `Observed` 时失败，日志中前述证据均已存在。未修改程序、输入堆、任务表、scheduler 或执行证明。

该编译拒绝只是后置观察的隔离对照，不是“执行了错误版内核”，也不替代独立的目标选择与帧保持证明。

## 明确未完成

- 物理源码路径仍停在 `sfexec 112` 之前，旧 `SXprogram 112=None` 及无步结论不变；未执行 raw port。本项目接受的 normalized port 抽象边界也不能被表述为 raw 实现完成。
- 新扩展尚未装入原 `osintspec`、`WFInt`、`TaskSim` 或 `toptheorem`，未证明扩展框架的健全性。证明的是有限轨迹及 Core 单步投影，不是所有扩展步的完整模拟或所有交错 safety。
- 调度事件可以选回同一个 tid；事件非空本身不保证 tid 改变。本例用两个不同 tid 检查真正改变，当前已最高的分支另给空事件见证；不宣称三分支轨迹全局互斥或确定。
- 一般桥接定理只沿用原 `hswi_step` 的前提，不额外证明被选任务一定存在于任意高层任务表。非空实例显式给出并保持其任务项；完整程序仍须建立对应不变量。
- 未完成初始化可达性、全部函数表纵向连接、同程序 K1–K4、源码级 `GOOD_OS`；uCOS3尚未开始。两个阶段最终目标仍为 active。

## 本轮实测（不是继承的完成声明）

| 检查 | 结果 |
| --- | --- |
| 生产模块稳定重编译，两次 | 通过，1.292 / 1.300秒，源哈希一致 |
| 非空实例稳定重编译，两次 | 通过，1.912 / 1.909秒，源哈希一致 |
| 19个新根的 `Print Assumptions` | 通过，仅原 classical / functional extensionality 允许假设 |
| 两个入口的递归 `coqchk` | 通过，421.084秒；运行期间843个Coq输入/项目文件身份不变 |
| 新增7项回归 | 全部通过 |
| 完整回归 | 2731项，437失败、1错误，92.685秒；与308步旧失败/错误编号及顺序完全相同 |
| `make build JOBS=1` | 增量构建通过，不等于从空目录全量重建 |
| `project-audit.py` | 通过，383个活动Coq文件、103个框架/策略文件 |
| `make audit` | 仍以退出码2失败：旧 `stale function evidence input identity` |
| `git diff --check` | 仍以退出码2失败：旧 inferules 六处空白，输出与308步逐字相同 |
| 基线/清理 | 核查3692项基线；306个既有pyc与根lia/nia缓存原字节保持；逐项确认后删除17个本轮一次性文件 |

早期6次生产证明、2次实例编译失败及其源码快照全部保留。新增Python测试第一次将后置帧条件内部的 `->` 误判为执行前提；改为检查完整外层 `forall ... exists ... CSsource_run` 形状，保留失败日志及原测试快照，再次7项全过。未更改任何旧测试、Coq结论或冻结证据来制造通过。

最终实测汇总见 `verification.json`，重复核查见 `checkpoint-*.json`。证据清单冻结哈希；HEAD保持 `1f57743c638c7e1ccdcc594e51dc90c0c7406789`，未提交或推送。

## 下一步应连接什么

沿已经接受的 normalized port 抽象边界，连接低层后继任务状态与本步高层事件，而不是编写汇编或把事件存在当成模拟完成。优先建立需调度分支的统一低/高层关系，核对被切出任务和被选任务的代码/环境/保存上下文，再推进旧 `WFInt` / `TaskSim` 的状态接口与健全性义务。若三控制字节仍在原逻辑接口外，就必须显式处理该不匹配；不能换回两份可任选的中断规格。
