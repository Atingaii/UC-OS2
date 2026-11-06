# 第214步：三条退出路径使用同一调度规格

## 本步解决的问题

第209步的不调度/同优先级退出与第213步的不同任务退出，要求同一个调度函数标识符具有两套不同的精确规格。直接把两个 lookup 同时写进前提，可能得到不可满足的“统一”，不能作为成果。

本步新增共同 `OS_SchedNew` 契约，以纯逻辑 tag 选择 critical 或 ISR 资源。运行时函数、实参、C/AST、框架和已有证明均未改变。共同 callee 对真实 `BuildPreI/BuildRetI` 逐支证明；不是把 callee 的正确性当成前提。

## 核心结果

- `V293_InfRules_spec_embedding`：对不含赋值式调用 `scalle` 的语句，逐构造子归纳原 `InfRules`；每个调用的前、后断言在重标记后**完全相等**。`sd/li/Inv`、代码、所有前后断言保持不变。它不是一般的规格弱化规则。
- `V293_OSSchedNew_joint_contract`：同一真实 callee 支持两种资源契约，且包括非法 codec 的原有 `Afalse` 行为。
- `V293_OSIntExit_all_builder_contract`：实际退出 builders 和完整归一化本体，使用一个调度 lookup、同一 `V293_scheduler/V293_shared_li/storage Inv`，内部复用已核验的三条路径证明。
- `V293_all_exit_env_WFFunEnv/WFIFun`：在同一规格和同一环境不变量下，直接闭合 `OSIntExit/OSIntEnter/OS_SchedNew` 三函数环境。不存在“整个退出本体正确”的外部前提。

逻辑路径编码：退出外层 `true` 为 changed，`false` 再交给第209步 quiet/same 标签；调度 callee 的 `true/false` 分别为 critical/ISR。它们不是额外的 C 实参或运行时分支。

## 对照及反例边界

- 实际退出本体通过 `V293_void_calls`；任意 `scalle` 被排除。原因是值调用规则还要求全域 `retpost`，本步没有证明它可随联合规格传递，故不能无条件推广。
- `ACenvironment/ACactual_contract` 是具体三函数程序及完整本体实例；`ACchanged_nonempty` 从上一阶段独立字节内存接入真实联合入口。
- quiet/same 的非空性也接入联合入口；它们复用第209步的另一套物理地址夹具，不声称三种正控来自同一个初始化状态或同一个具体地址实例。通用生产定理的三条分支仍使用同一环境和 `Inv`。
- 固定 ISR 逻辑 payload、物理内存及状态，只翻转共同 callee 的 tag：两侧**外层标签**均有效解码，正确侧前置非空，错误侧因内层 codec 不兼容而为 `Afalse`。这是编码选择边界的单因素对照，**不是内层也有效的两个执行，也不证明错误分支执行安全**。
- critical 前后断言的逐项精确等式不要求合法 payload；ISR 非空性使用独立就绪表内存。

## 尚未完成

本步“all”指已证明的三类路径合并，不表示无条件覆盖任意运行状态。changed 分支仍限原 IE=false、ISR 全清、相应完整所有权和快照；quiet/same 保留原规格的范围。changed 快照仍是模块参数，尚未编码为统一的动态逻辑快照。

生产数据所有权如何从 `Inv` 获取、任意 ISR 下的 changed 路径、`WFInt`、初始化、最终源码级 `GOOD_OS` 与同程序 K1–K4 仍开放。uCOS3 尚未启动，六门覆盖不变。未提交或推送。

## 验证入口

本步全部编译尝试（含失败）、配置后源码重建、根定理假设、递归 `coqchk`、构建及测试结果保存在 `audit/logs/stage214-scheduler-spec-unification/`。机器可读结论以 `verification.json` 为准；新增 Python 测试仅为结构回归，不声称语义 TDD。
