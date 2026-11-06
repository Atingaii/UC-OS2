# 第136步：从同一就绪状态执行目标指针写入并建立切换前置条件

## 为什么需要这一步

第135步已经把同一抽象任务映射、真实 TCB 已选字段、就绪位图和优先级表接到原 `OS_SchedNew` 的两条赋值。但算出优先级、读出正确表指针，不意味着 `OSTCBHighRdy` 已被写入。框架切换前置条件还要求真实目标变量指向该最高就绪任务。

本步只连接这处缺口。源码仍为 V2.93.01、提交 `0c4a48e6fbc6e915714e816196619a5481accf0c` 的固定配置与已授权修复；对应 `Source/os_core.c` 1757～1758行的两条赋值，以及 `OS_Sched` 1714行的 `OSTCBHighRdy = OSTCBPrioTbl[OSPrioHighRdy]`。复用既有手工 AST，不声称自动 C 前端或完整函数覆盖。这里组合的是三条赋值，不是把 `OS_SchedNew` 的真实 call／return 也证明了。

实现前的六项检查见 `audit/logs/stage136-ready-target-handoff/protocol.json`，旧文件身份见 `baseline.json`。C、配置、手工 AST、framework、tactics 和既有冻结证据不改。编译失败、失败时源码快照和日志全部保留；被终止的计算也不记为通过。

## 稳定生产接口

`certiucos/v293/proofs/V293ReadyTargetHandoff.v` 暴露 `V293_ready_dispatch_updates`：

1. 输入第135步的有限 ready Inv、真实变量绑定、调用者拥有的两个输出字节、目标指针单元和256项 lookup loads。没有要求调用者先提供 `AHprio`、最高任务或 scheduler 判断。
2. 从该 Inv 推导同一 tasks 的最高 ready 任务；用原 `V293_OSSchedNew_updates` 执行两条选择赋值，得到实际中间内存 `Mselected`。
3. 在同一个 `cstepstar` 三赋值序列中执行既有 `V293_OSSched_target_update`，构造实际 typed 指针 store `Mselected -> Mf`，而不是假定写后内存存在。
4. 返回同一 tasks、Inv、caller frame，实际目标 load、scheduler 判断和 `SWPRE`。根据 current 是否属于同一 tasks，分别给出 `SWPRE_NDEAD` 和 `SWPRE_DEAD`。
5. 除两个输出字节与目标四字节 footprint 外，其他全部地址不变。空间分离约束保证写入区域与 Inv／frame 不重叠。

三个辅助引理把实际 owned cell 与真实 ge 绑定接成具名全局 mapsto，再把同一抽象任务槽转换为 `AHprio`。辅助引理的 scheduler 前提由主接口内部推出，不能把它单独当成选择正确性的证据。

目标单元仍在 ready Inv 之外，只在切换前由调用者拥有。**不把目标指针当作私有 frame 跨上下文切换保存**：其他任务可能改写这个共享变量。本步没有证明真实 switch 步，也没有闭合完整调度函数的通用 Hoare 契约。

## 同一内存的正例与单因素省略实验

独立探针 `audit/probes/V293ReadyTargetHandoffProbe.v` 复用已检查的非空联合字节实例：优先级4的 ready 任务 `(60,0)`，优先级6的 waiting 任务 `(41,8)`；位图、任务字段、优先级表和只读 lookup 都在同一实际内存。新增真实目标单元 `(93,0)`，旧值特意指向 waiting 任务，真实 ge/le 绑定保持有效。

`RHjoint_handoff_and_omission` 在一个定理中同时给出：

- 共同前缀：原两条选择赋值运行到同一个 `Mskip`，实际 high=4，ready Inv 仍成立，目标仍指向 waiting。
- 正例：追加原目标赋值到 `Mf`，真实 store 把 waiting 指针换为 ready 指针；`Mf` 满足 `SWPRE`，同一 ready Inv 仍成立。
- 两种 current：`live=true` 时 current 是 waiting 成员，得到 `SWPRE_NDEAD`；`live=false` 时 current 不在表中，得到 `SWPRE_DEAD`。
- 单因素：仅省略最后目标赋值，保留相同前缀、中间内存、抽象任务表、位图、TCB、优先级表、环境绑定和 high 字节，证明 `Mskip` 不满足 `SWPRE`。`Mf` 与 `Mskip` 在目标四字节之外逐地址相同。

`RHreject_waiting_target` 的拒绝不是缺失变量、错误类型或失效 Inv 导致：实际 typed 目标 load 锁定 waiting 指针，同一抽象任务槽要求目标 ready，二者冲突。不能把“位图已正确选择”当成目标写入机制已经工作。

## 验证与复现

最终实测以本目录 `checkpoint-report.json`、`verification.json`、冻结 manifest 与 `stable-compiles.json` 为准。新增8项 Python 回归检查结构、边界和证据身份；语义结论由 Coq 定理和 `coqchk` 检查，不由字符串测试替代。

```sh
make build COQBIN=/data/home/lucentzhou/.opam/default/bin/
PYTHONDONTWRITEBYTECODE=1 python3 -B -m unittest discover -s tests -p test_ready_target_handoff.py -v
PYTHONDONTWRITEBYTECODE=1 python3 -B audit/logs/stage136-ready-target-handoff/verify-checkpoint.py
```

实测10个证明根（生产4＋探针6）、302个活动模块和22个附加探针全部通过信任检查。实际假设只有框架原有的 `Classical_Prop.classic` 和 `FunctionalExtensionality.functional_extensionality_dep`，未扩大白名单。全量1781项回归的完整失败 ID 集合与第135步相同：仍为旧423失败／1错误。六门94/1/1/1/1/0及 `make audit` 的 `stale function evidence input identity` 继续保留，不改写旧证据制造通过。

## 未完成部分与下一连接点

- 本步是无交错的三赋值存在性执行，不是完整 `OS_SchedNew` call／return、完整 `OS_Sched`、ISR 或上下文切换执行证明。
- 第135步有限 Inv 的限制不变：空 LocalInv、只覆盖已选 TCB 字段、未使用槽及高位13..15未约束。不是生产全局语义 Inv，也未证明从真实初始化可达。
- 完整池／链／事件资源、创建／阻塞／唤醒等 API 保持、Hook／栈、运行初始化和 `WFIFun` 仍须连接。
- 最终 `GOOD_OS` 与同程序 K1–K4 未完成，uCOS3 未开始；总目标 active。本步不提交／推送。

下一步优先闭合真实 `OS_SchedNew` 调用返回与调用者局部输出的衔接，再处理框架切换消费共享目标的所有权边界；不得让该目标作为普通私有 frame 穿过切换。不能以继续增加独立 fixture 代替同一程序的纵向连接。
