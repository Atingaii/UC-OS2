# 第145步：旧任务切回后的实际退出、释放与返回

## 目标与实际新增

本步回答一个边界明确的问题：**如果原框架实际切回一个挂起在 OS_Sched 出口的任务，且其局部资源仍完整，能否继续原语义，退出临界区、释放 cpu_sr 并恢复调用者？**

答案由四个通用生产根及五个联合探针根给出。没有修改 C、配置、手工 AST、端口、框架或 tactics，没有新增执行规则；不增加整函数覆盖信用，六门仍为 `94/1/1/1/1/0`。

| 根 | 精确职责 |
| --- | --- |
| `V293_bound_continuation_inos` | 从真实函数绑定和调用 continuation 推导原 `InOS`，不由调用者提供分类成功 oracle |
| `V293_sched_resume_return` | 任意任务的原全局出口：从 CPU 局部完整所有权构造成功 free，恢复保存的 IE、外层 critical stack 和 caller；其他任务槽与非局部 block 保留 |
| `V293_sched_switch_resume_return` | 从原 `pswitch_step` 实际切回，连续接上述出口；actual current store 也由所有权构造 |
| `V293_sched_resume_stack_ablation` | 单因素删除保存栈顶；正负两侧都实际返回，同一 free 终态堆，但最终 IE 相反 |
| `RPentry` | 实际 sfexec 入口、分配、初始化、函数体与首次原切换的连续全局轨迹 |
| `RPtable_waiting` | 从同一实际抽象任务表与物理优先级表导出槽6的真实 load |
| `RPcells` | 从首次切换后同一所有权抽取 target、current 和挂起任务的 CPU 局部资源 |
| `RPprepare` | Ready 环境 fixture 实际读表、写 target，原语义执行到切回点 |
| `RProundtrip` | 同一实际内存连续连接入口、首次切换、环境读表、切回、退出、释放、caller 恢复 |

源文件：`certiucos/v293/proofs/V293ReadyResumption.v`。
联合探针：`audit/probes/V293ReadyResumptionProbe.v`。
稳定编译标签以 `audit/logs/stage145-ready-resumption/stable-compiles.json` 为准；全部试错快照和失败日志保留。

## 通用恢复契约不是什么

生产定理量化任意任务表、任务标识、内存、caller 和外层 continuation；不依赖固定两任务实例，不把成功 store/free 或最终堆作为前提。

它仍是**条件资源契约**：恢复时须存在完整 CPU 局部所有权，以及准确的挂起代码／环境／aux 槽。没有证明任意干扰下这些资源始终稳定，没有证明调度器确实选择该任务。`GoodInvAsrt R` 限定可运输的空间 frame，不包括随意依赖旧 IE 或旧局部环境的断言。

原 `pswitch_step` 写实际 current，后续出口执行原 `excrit`、`sret` 和行政性 free。这里没有把旧 local closure 包装成新的执行规则，也没有省略真实释放步骤。

## 联合实例与环境 fixture 的边界

初始非空任务表含 Ready4 和 Waiting6；Waiting6 在抽象任务表中**仍然 blocked**。Ready 的读表／切回代码和 `FCouter` 在**初始任务表**中明确安装为环境 fixture；不是第一次切换后偷偷更换任务代码槽。

轨迹为：

`Waiting 实际 sfexec → 分配／初始化 → 调度函数体 → 原 switch 到 Ready → 环境读槽6并写 target → 原 switch 回 Waiting → excrit → free／return → 原 caller`

所有连接点共用同一实际物理内存，不能任选新堆拼接。最终 CPU block98 的四字节全部移除；actual current 指回 Waiting；Ready 的 local／aux 不变；除 target93、current1 和 CPU98 外的 block 逐字节保留。

**这不是生产调度器选择或唤醒 Waiting 的证明**。优先级表包含等待任务并不意味着 ready bitmap 会选择它。环境 fixture 只用于检验框架物理上下文恢复行为，不是第二个真实 OS_Sched 源码调用。最终实际 current 的正确 load 也不等于已恢复 production Inv：原全局执行语义不自动更新这里用于空间断言的抽象 ghost current。

首次切到 Ready 后，cache 仍为6；切回 Waiting 后 cache 仍为6。这不表示同步已修复，只是最终 current 恰好重新对应该值。端口仅有 `OSCtxSw` 声明，cache 同步缺口保持开放，没有添加端口实现。

## 前瞻单因素消融

`protocol.json` 在实现前冻结检查目标。本步最终采用**删除保存栈顶**而不是翻转一个位：

| 项目 | 正例 | 负例 |
| --- | --- | --- |
| 初始 critical stack | `enabled :: negb enabled :: ci` | `negb enabled :: ci` |
| 单因素干预 | 无 | 仅删除第一个元素 |
| 实际出口 | 执行到 caller | 执行到同一 caller |
| 最终 IE | `enabled` | `negb enabled` |
| 最终 critical stack | `negb enabled :: ci` | `ci` |
| free 与最终内存 | 同一个实际 free 结果 | 与正例相同 |

保留一个非空外层栈是为了让负例也真正走到返回，避免空栈提前拒绝掩盖下游行为。IE 与剩余栈不同是删顶的执行结果，不是第二个独立干预。此通用定理和非空联合轨迹分别检查恢复机制与实例连续性，不冒充联合实例上的全路径消融。

早期草稿 `proof19` 使用翻转栈顶；最终 `proof20` 改为前瞻协议所要求的删除栈顶，早期成功／失败快照都保留，没有改写协议或冻结旧证据。

## 验证与尚未完成

新增8项结构／身份回归不代替 Coq 语义证明。独立打印9根全部假设，与上一检查点精确比较；重查312活动模块和31额外探针。实际运行结果须查本步 `trust.json`、`checkpoint-report.json` 和 `verification.json`，不能把计划检查当成已通过。

全量测试要求旧423失败／1错误的**失败 ID 集合及长度**完全不变；旧 `make audit` 的 `stale function evidence input identity` 和冻结框架空白失败继续保留。所有旧源码、配置、AST、框架与证据逐文件比较；README／状态只加前缀，不改历史正文。

本步仍是存在性、无交错的条件恢复连接，不是初始化可达性、任意交错、client scall 同内存连接、活动 ISR、完整 CurLINV／生产全局 Inv／WFIFun。源码级 GOOD_OS 和同程序 K1–K4 未完成；uCOS3 未开始，总目标 active。没有提交或推送。
