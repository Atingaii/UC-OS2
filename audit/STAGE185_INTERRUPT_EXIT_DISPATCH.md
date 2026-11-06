# 第185步：OSIntExit 的真实调度分支接入计数与守卫

## 本步解决什么

第184步已经证明实际递减和两个守卫，但启用分支还要求调用者证明**整个 dispatch**。本步在原有共同资源上消除这个大前提：

1. 实际 `OS_SchedNew()` 调用走原内部规格与调用规则。
2. 从同一 ready bitmap、TCB 抽象映射和优先级表得到最高就绪任务，并写入实际目标指针槽。
3. 实际 `!=` 从高优先级与当前优先级的物理字节求值；保留源码的 `sif` 和空 `else`，不用历史 `sifthen` 代替。
4. 不同优先级时实际32位计数加1，按模2^32回绕；随后实际空 trace 语句，再到 `scall int_switch nil`。
5. 相同优先级时保持资源和计数，不需要中断切换调用证明。

**剩余前提仅为实际 OSIntCtxSw 调用的 Hoare 义务，不是其已完成的实现证明。** 没有把它替换成普通 `sprim switch`、空函数或假 CPU hook。

## 稳定接口与共同所有权

新生产文件：`certiucos/v293/proofs/V293OSIntExitDispatch.v`。

- `V293_OSIntExit_dispatch_hoare`：真实调度前缀、比较、递增、空 trace 的接口。
- `V293_OSIntExit_ready_dispatch`：实际递减、嵌套守卫、锁守卫、上述真实 dispatch 的同一资源接口。
- `V293_OSIntExit_ready_dispatch_semantics`：经现有 `RuleSound` 连接同一片段的 `RuleSem`，保留相同实际调用残余。
- `V293_OSIntExit_ready_disabled`：嵌套至少2或锁大于0时，不要求调度器的 Spec lookup，也不要求 CPU 调用证明。

入口 `V293_exit_ready_pre` 同时持有原调度器资源、任务表／TCB映射、目标槽、当前优先级、计数和**全写权限**的嵌套／锁字节。递减不是从只读守卫断言写内存。重排只调整分离合取，不丢弃其他资源；CurLINV 来自同一内部调度器资源。环境查找由显式 frame 条件提供，调度调用运输 frame 仍须 `GoodFrm`。

启用条件仍是 `pred nest=0` 且锁为0；旧 nest=0 也可能调度，不能偷偷加强为旧 nest=1。只有启用且高／当前优先级不同才需要调用前提，其入口包含**已经加1的计数**及递减后的完整字节资源。

## 预先协议与对照

协议在新增证明前冻结，见 `audit/logs/stage185-interrupt-exit-dispatch/protocol.json`。

新独立探针：`audit/probes/V293OSIntExitDispatchProbe.v`，不导入旧 audit 探针。

| 对照 | 保持不变 | 唯一变化与观测 |
| --- | --- | --- |
| 优先级相同／不同 | ready、TCB映射、表、目标、嵌套、锁、计数 | 当前优先级12／0；真实物理比较为0／1 |
| 计数边界 | 不同优先级及所有其他槽 | 计数0／max_unsigned；实际加法为1／0 |
| 错误 post | 同一物理堆、环境domain、action及全部其他断言 | 正确计数1可满足；错误旧计数0被实际 `load Tint32` 排除 |
| 递增消融的快照对照 | 同一 ready/table/target/priority/nest/lock | 对比计数0／1的两个独立所有权快照及实际load；不是删改AST后运行至CPU返回的执行实验 |
| 不同优先级字节块外保持 | 其他所有物理字节 | 块13之外逐字节相同 |
| 不同计数字节块外保持 | 其他所有物理字节 | 块14之外逐字节相同 |

`JDnonempty` 给出完整入口；`JDtail_nonempty` 给出同一资源形状的最高任务已发布快照。两个都包含实际物理堆及同一抽象TCB表，不是各子断言各造一份不兼容状态。所有权快照本身不是从入口到CPU返回的一次执行。

注意：固定TCB表只含idle任务，改变当前优先级字节的单因素对照用于本片段的真实数值判断，**不声称同时满足完整 current-task/priority 一致性不变式，也不由此推导指针不相等或生产调度正确性**。这比同时改变TCB表和优先级更能隔离比较，但结论也必须限制在片段资源契约内。

## 对抗式复核与未完成范围

- 未用相关的前置domain拒绝冒充错误post检测；反例直接使用同一堆的counter load冲突。
- 消融快照验证的是计数字节差异；未据此声称已证明删去递增的AST端到端执行或实际CPU调用／返回。实际原递增的Hoare证明另在稳定接口中。
- 未从空 LocalInv fixture 推广到生产ISR不变式。
- 未把真实临界调用当成旧归一化 `encrit/excrit`；本步不证明 `V293_EnterCritical/ExitCritical` 的实现。
- 未给 OSIntCtxSw 添加无依据契约；完整调用前提与其精确资源均保留。
- 使用既有调度器模块契约并不自动证明全生产Spec环境；全符号表、原函数builder/saved局部、完整 OSIntExit、生产ISR、初始化、并发simulation仍开放。
- `RuleSem` 是此条件片段的语义连接，不是 GOOD_OS 或同程序 K1–K4。

## 检查与证据

目录：`audit/logs/stage185-interrupt-exit-dispatch/`。包含基线、所有成功／失败编译快照、真实源码检查、递归 coqchk、逐根假设、完整测试及清理清单。计算大物理堆的直接求值曾出现膨胀，保留中断日志，改为从实际所有权推导load再求值；没有改判断或弱化门槛。

旧 C、配置、AST、框架、tactics、证明、测试和冻结证据保持原样。文档只前置新段落，工程清单只追加。新增5项结构／证据测试；全套要求保持旧423失败、1错误的完整有序ID列表，不仅比较数量。审计仍有旧的 stale identity，旧 inferules 空白问题仍保留，不宣称全套全绿。

最终核验数据以 `verification.json` 和 `checkpoint-evidence-manifest.json` 为准。六门仍为 `94 / 1 / 1 / 1 / 1 / 0`。第一阶段尚未完成，uCOS3未启动，总目标保持 active；本步不提交／推送。

下一步：沿同一实际函数继续接 OSIntCtxSw 的框架中断调用资源与临界调用边界，随后才能建立真实builder及完整函数契约。
