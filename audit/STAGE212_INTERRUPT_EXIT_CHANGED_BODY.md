# 第212步：不同优先级退出的完整归一化本体

## 本步连接什么

稳定接口是 `V293OSIntExitChangedBody.V293_OSIntExit_changed_body`。它只有一个 `InfRules` 结论，不假设完整退出本体、中段 Hoare 或表达式求值 oracle。证明顺序：

```text
saved = 0 → running guard → encrit
→ nesting 条件递减 → nesting/lock guards
→ 实际 OS_SchedNew 调用、目标赋值、优先级 guard
→ counter increment / skip / cache copy / switch
→ 原线程将来恢复 → excrit → return None
```

内部 dispatch 复用第211步接口；callee 的实际函数契约仍是前提，尚未通过完整统一函数环境消除。源码、配置、AST、框架、旧证明与旧回归不变，沿用 ADR0010 的切换抽象，不开展硬件或编译器精化。

## 所有权与约束

| 项目 | 实际证明 | 尚未证明 |
| --- | --- | --- |
| 外层入口 | running=1、nesting≤1、lock=0，从实际完整字节导出 guard | 不是全部路径合一的 OSIntExit 规格 |
| 局部变量 | 已分配 saved 单元实际赋0，保持局部环境及私有值 | 尚未接入不同任务真实 BuildPreI/BuildRetI |
| 共享控制字节 | running/nesting/lock 纳入同一 storage Inv；不放在 switch frame | 不提供生产 Inv 打开的真实资源来源 |
| 切换恢复 | 共享值存在化；仅布局、环境与私有资源保留 | 不证明 switch 必然返回或初始化可达 |
| 临界现场 | 任意 si/ci；原 IE=false、ISR 全清；真实 excrit 弹出进入时保存的 false | 任意 IE/ISR 与第206–209步契约的统一仍开放 |
| guard 和任务 | 使用真实就绪输入、指针表与优先级字节 | 通用前置未建立缓存—当前任务关系；不能仅凭 guard 推出不同任务 |

`V293_full_current_local` 从当前任务指针完整所有权导出现有 LocalInv；`V293_storage_resumed_excrit` 从恢复的不变量取出共享旗标及资源，执行真实退出临界区后归还同一不变量。没有把共享运行状态当作 `GoodFrm` 私有快照。接口参数 `px` 仍须满足框架约束，不能由 GoodFrm 推出生产私有性。

## 独立实例与单因素对照

`audit/probes/V293OSIntExitChangedBodyProbe.v` 使用实际编码字节、不同块上的控制单元和独立任务表构造入口，不从主定理结论倒推非空。当前任务 priority=4 且等待，最高就绪目标 priority=12，两任务确实不同；就绪输入 lo=0、hi=16。入口旧 high=0，实际 callee 将其更新为12。

`CXentry_nonempty` 给 nesting=1 非空入口；`CXzero_max_entry` 给 nesting=0 与 UINT32 最大计数器入口；`CXactual_body` 对任意计数器和 nesting≤1 实例化完整归一化本体。计数沿用 UINT32 模加，不宣称无溢出。这些是资源/适用性证明，不是初始化可达性或完整执行轨迹。

事前协议保存在本步 `protocol.json` 和 `protocol-identity.json`。`CXexcrit_control` 只中和最后的 excrit：实际 primitive 从 false::ci 弹回 ci，而不执行它时原状态不满足 Acs ci。其余现场相同。这仅是尾段单因素对照，不把前置或 guard 拒绝当作下游执行证据，不声称完整函数变体执行。

## 核验与保留的失败

本步 `audit/logs/stage212-interrupt-exit-changed-body/verification.json` 汇总实际结果；逐次编译快照、失败日志、递归 coqchk、逐根假设、两次构建、精确配置后源码重建和完整回归均保留。新增5项 Python 回归只检查接口结构与证据身份，不能代替 Coq 语义证明，也不声称语义 TDD。

旧423失败/1错误必须保留原 ID/顺序；旧 make audit 的证据身份失配和 inferules.v 第581–586行空白问题不放宽、不删除。README/状态只前插，工程清单只追加，旧冻结证据和基线逐项核对。清理前清点本轮一次性 Trust 驱动和产物，恢复原缓存后删除备份，保留源码、失败证据、既有缓存及可复用 Coq 产物。

下一步应把不同任务路径接入真实 builders，与既有不调度/同优先级规格统一，并解决 ISR/IE 与生产 Inv 资源边界；之后闭合完整函数环境、生产 ISR/LocalInv/WFInt、初始化、GOOD_OS 与同程序 K1–K4。uCOS3 未启动。六门不变 `94 / 1 / 1 / 1 / 1 / 0`，总目标 active，阶段一未完成；本步未提交/推送。
