# 第276步：真实旧任务切出点的共享 SWPRE 资源

## 这一步解决什么

第275步已经有条件的 switch TaskSim，但条件使用强 current/cache 候选；其非空恢复实例针对已选目标，不能代替仍 blocked 的旧任务切出。真实活跃调用在 switch 前已经把优先级缓存复制为4，旧任务仍是优先级6的等待任务，因此强 current guard 在这里不成立。

本步不改 C、AST、框架或最终验收条件，先解决独立的空间义务：**从既有完整调用实际达到的旧任务状态，在同一个共享子堆同时交付弱 storage 的 SWINVt 和 SWPRE_NDEAD。** 不是将 weak storage 宣布为最终全局不变式。

## 一般生产接口

`certiucos/v293/proofs/V293StorageSwitchPre.v` 的唯一公开接口是 `V293_storage_switch_pre`。量化 ready/storage 地址、目标变量及类型、记录 cells、current/next、任务映射和全部状态，输入只有：

1. 目标全局绑定，以及同一共享堆中实际的 typed pointer load；
2. 同一抽象状态中的任务映射、旧任务仍在映射内；
3. next 是该映射中最高优先级 ready 任务；
4. 既有弱 storage `SWINVt`。

输出是同一状态上的 `SWINVt //\\ SWPRE_NDEAD`。`//\\` 是逻辑合取，不复制空间资源。没有把 TaskSim、ProgSim、执行轨迹或释放结果当成生产前提。

辅助引理 `V293_dispatch_read_frame` 仅在拥有完整目标单元时，把总堆的 typed load 与共享子堆中存在的实际值对齐；不是任意把总堆读取反推给子堆。没有借用外部 frame 的写权限。随后用原 current 两半组合及 `AHprio` 规则构造原框架 SWPRE。

## 完整入口上的独立见证

`audit/probes/V293OldSwitchPacketProbe.v`：

- `OPpartition` 将第267/270步原 `FTafter_copy` 达到状态重新分区；共享抽象状态完整，外部抽象 frame 为空。`SWPRE_NDEAD` 只在共享 Mc 上成立。
- `OPactual_entry` 复用原 `FTto_switch`，从真实函数进入、fresh saved 分配、活跃 OSIntExit 路径走到旧任务的 switch106。没有拿目标任务返回状态或第275步的选中目标快照代替入口。
- 资源顺序为：旧任务本次分配的 **saved(bs) 私有**；共享 `SWINVt(storage) //\\ SWPRE_NDEAD`；目标已有 saved98 与 `RCframe` 外部保留。saved98 不被转交旧任务，两个保存区不混淆。
- `OPnonvacuous` 用两次 fresh block 存在性构造非空前提，之后对任意 cs/ncs/ip 有实际达到堆。它不是 Init/启动可达性证明；目标 pending 仍是已存在的 fixture。
- 同一达到堆的 saved(bs) 仍能读零，cache94 实际为4；调用旧 `SPcopied_cache_gap` 证明强 current guard 拒绝。旧任务仍 blocked，并未被修改为 ready。

## 必要条件与消融边界

冻结协议在实现前要求检查目标读取、最高选择、旧任务成员三个条件。现在的机器证据是**逻辑必要性/拒绝控制，不是三组完整执行消融**：

| 检查 | 本步证据 | 不应外推 |
| --- | --- | --- |
| 实际物理目标不可忽略 | `OPnecessary` 从同一 SWPRE 取出 typed load 及同一个 next；`OPreject_waiting_target` 拒绝目标仍指向 waiting 的状态 | 没有构造修改目标后的完整入口执行 |
| 最高 ready 不可任意指定 | `OPnecessary` 从 AHprio 和同一抽象映射得到最高 ready；`OPreject_wrong_selection` 在实际 load 为非最高时拒绝 | 未构造“删除 highest 前提，其余均满足”的独立非空反模型 |
| 旧任务成员 | `OPnecessary` 从 NDEAD 分支得到 indom；`OPreject_dead_current` 拒绝不在映射内的 current | 不能据此说现有 storage SWINVt 不会自行蕴含某些成员条件；未证明该生产前提在全部模型中独立必要 |
| 强 cache/current 缺口 | `OPactual_entry` 的同一实际达到堆证明 guard 不成立 | 拒绝强 guard 不代表已闭合弱候选的返回/整核保持 |

因此协议中逐项“删除条件后其余相同”的反模型/执行实验没有全部完成，记录为未完成，而不是将必要性推论伪报为独立移除实验。协议保持原字节，不回写为事后通过。

## 验证与未完成目标

生产/probe 各两次稳定编译；逐根 `Print Assumptions` 与递归 `coqchk` 检查结果、全量测试、旧失败 ID/顺序及缓存恢复，以 `audit/logs/stage276-old-switch-packet/verification.json` 为准。新增 Python 检查是结构/证据回归，不是 Coq 语义 oracle。开发期失败的源码快照和日志原样保留。

这不是整核证明，也不是完整入口 TaskSim：弱 storage 的 pending 恢复桥尚未接通；第275步强 current 接口的真实入口前提仍不成立。不能把本步的弱 `SWPRE` 当成第275步强 `SWINVt`。仍须处理共享恢复、强缓存一致性条件与原 TaskSim 的连接，再完成完整源码级 GOOD_OS 和同程序 K1–K4。

ISR 全清、si=nil、原保存栈和 ADR-0010 边界保持；未证明任意中断交错、旧 blocked 任务完整切回或初始化。uCOS3 未开始。固定源码提交及两类授权修复不变。未提交、未推送，不更改旧冻结证据来制造通过。
