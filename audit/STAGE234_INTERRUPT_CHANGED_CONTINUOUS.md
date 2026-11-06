# 第234步：连续连接会触发调度的 changed 中断路径

## 本步增加了什么

主接口 `V293_interrupt_changed_continuous` 在原 `V293_irq_source_wrapper` 上连续连接 **EOI → OSIntEnter → OSIntExit（changed）→ exint**：从 nesting=0、running=1、lock=0 的强入口出发，经实际 Enter 得到 nesting=1，再以原动态 changed codec 调用 Exit，返回后关闭同一 ready/TCB/storage Inv 并接真实中断返回规则。调度的抽象动作 `sched` 保留并由既有精确 changed 合同消耗，未将切换后共享字段冻结为入口值。

只增加一个生产证明文件和一个 audit probe；没有修改 C、配置、AST、旧证明、框架或 tactics。共同 Spec、原 Enter/Exit/SchedNew 三函数程序和原 ready/TCB/storage Inv 均复用第233步。`CCenvironment` 实例化同一程序／Spec 的 GoodI、WFFunEnv 和 WFIFun；没有加入任意中间资源蕴含、执行定理或从弱后置逆推强后置的假设。

## 关键资源如何接上

Exit 需要完整当前任务指针，而 Enter 的 p_local 需要其中一半读权限：

1. 用 `GV_separate_rw` 将当前指针完整权限拆为两半。一半交给 Enter；另一半保留在 caller frame，同时保留其**指针类型**与全局绑定。
2. Enter 的真实 body/builders/call 保留精确 running、nesting、lock 和 p_local，直接得到 0→1，而非假设中间控制值正确。
3. 返回的 `CurTid` 带存在量化的指针类型。`V293_changed_current_combine` 从同一全局环境查询证明两个指针类型相等，才通过 `GV_combine_ro_p1` 合成完整 typed 权限。不能将两个无类型约束的 CurTid 任意转换为所需 typed 指针。
4. 其余 ready、typed TCB、lookup/table、counter 与控制字节在同一资源框架中传递。Exit 通过真实 call_rule 调用原 all-exact changed 合同；精确 p_local 归还后才能关闭同一 Inv。只消去零堆占用的全局名称绑定，没有用 Atrue 丢弃交付资源。

`CCentry_nonempty` 从 `JBmemory 0 Int.zero Int.zero` 的实际字节堆构造入口子堆及抽象资源（包含 typed table 与 owned TCB），并由 `CCactual_wrapper` 实例化同一个连续定理；`CCreturn_builder_exists` 排除返回 builder 不存在导致的空洞。

## 严格边界

- 这是 changed 的**强入口**：running=1、lock=0、原 nesting=0、clear 外围 ISR、空 critical stack、给定 changed validity（含不同优先级、typed table/TCB 等）及返回 builder 条件。不是全部 BuildintPre 的入口闭包，不是 WFInt。
- fixture 使用**常 Aemp LocalInv**。这里的同一 ready/TCB/storage Inv 不代表已经建立完整生产 ISR LocalInv、所有控制值关系、lookup 语义与物理 ISR 栈深对应。
- 具体字节入口**不是初始化可达**；本 wrapper 也没有 tick 抽象动作，不能当成 tick ISR 或生产 ISR 抽象规格。
- 本步没有新增两次执行级单因素对照。类型相等与权限重组是实际连接的必要推导，不据此声称完整执行消融；固定状态断言即使失败，也不是两次完整执行。结构测试**不声称语义 TDD**。
- quiet 与 changed 现在各有条件连续证明；**same 连续路径**、全部中断入口闭包、初始化、最终 GOOD_OS 和同程序 K1–K4 仍开放；**uCOS3 未开始**。

## 验证与后续

实测由 `audit/logs/stage234-interrupt-changed-continuous/verification.json` 汇总。编译与失败版本快照全部保留；20个根（生产14、probe6）逐根检查假设，两个入口模块递归 coqchk，只接受既有 classic / functional_extensionality_dep 边界。随后两次构建、5项结构回归和全量回归，重新重建四个准确配置后 C 函数身份。

旧423个失败、1个错误、audit 的 stale function identity 及旧 whitespace 失败继续显式保留，不修改历史证据以制造通过。六阶段覆盖仍为94/1/1/1/1/0，最终 GOOD_OS 未完成。下一步连接 same 连续路径，再审查 WFInt 所要求的真实 BuildintPre 入口闭包和 ISR 抽象规格，不能仅把三条强入口的合取算作全输入覆盖。
