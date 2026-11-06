# 第235步：连续连接优先级未变化的 same 中断路径

## 本步解决的问题

主接口 `V293_interrupt_same_continuous` 在原 `V293_irq_source_wrapper` 上连接 **EOI → OSIntEnter → OSIntExit（same）→ exint**。running=1、lock=0、nesting=0 的强入口经过实际 Enter 得到 nesting=1；原 same 动态精确合同经原 codec/call 返回资源，关闭同一 ready/TCB/storage Inv 后中断返回。

没有修改 C/config/AST、旧证明、framework 或 tactics；仍是原 Enter/Exit/SchedNew 三函数程序、QCspec 和 RDinv。`SCenvironment` 实例化原共同 GoodI、WFFunEnv、WFIFun，`SCactual_wrapper` 连接同一具体入口。没有将任意中间蕴含或执行正确性当作新假设。

## 为什么不能只把两个函数的证明放一起

same Exit 的 lookup、rows/group、priority table、current priority、running 使用半读权限；中断返回的不变量却需要完整资源。本步显式完成以下连接：

1. `V293_same_irq_read_borrow` 将完整权限拆半，一份交给实际 callee，一份保存在 caller frame。
2. `V293_same_irq_read_reunite` 将返回的半权限和保留半权限重组；不能从一个半权限直接推出完整权限。
3. `p_local` 所用当前任务指针和 Inv 所用 `CurTid` 从入口起分别保存；不从两个无类型约束的 CurTid 捏造任意指针类型。fixture 从完整 typed 当前指针拆半，**指针类型**保持原样。
4. typed TCB、shared fields、storage、counter、ISR 与两栈均保留；high 与 target 接受实际 callee 更新，不冻结为入口的旧值。只消去零堆占用的全局名称绑定，生产证明没有 Atrue。
5. 原 same validity 保证最高就绪优先级等于当前优先级，所以无需虚构 changed 的抽象 sched 动作；不是省掉 changed 分支应执行的调度。

## 非空见证与限制

`SCentry_nonempty` 从 `SCmemory 0 Int.zero Int.zero` 的真实字节堆构造精确入口子堆及抽象资源。当前任务为 `OwnershipReady`，TCB/current priority=4，bitmap=16，三者一致，不能把 bitmap16 的结果误作优先级0。`SCreturn_builder_exists` 保证同一 fixture 有返回 builder。

- 这是 same 的**强入口**，不是所有 BuildintPre，也不是 WFInt；同一个 Inv 的闭合并不等于任意中断入口都能建立此强入口。
- fixture 使用**常 Aemp LocalInv**，不等于完整生产 ISR LocalInv 或生产 ISR 抽象规格；物理嵌套值与任意 ISR 栈的关系仍需建立。
- 具体堆**不是初始化可达**；这里没有 tick 抽象动作，不是 tick ISR 定理。
- 权限拆合是连接所需推导，本步没有新增两次完整执行的单因素权限消融。固定状态检查**不是两次完整执行**；Python 身份/结构回归**不声称语义 TDD**。
- quiet/changed/same 三条有条件连续路径不等于全输入覆盖。真正的 BuildintPre 入口闭包、生产 ISR 规格、初始化、GOOD_OS 与同程序 K1–K4 仍开放，**uCOS3 未开始**。

## 验证和下一步

实测见 `audit/logs/stage235-interrupt-same-continuous/verification.json`。编译失败快照不删除；31个根（生产16、probe15）逐根 Print Assumptions 和两个入口递归 coqchk 后，再做两次构建、5项结构回归、全量回归和四个准确配置后 C 函数身份重建。

旧423失败、1错误、audit stale function identity 和旧 whitespace 失败显式保留。六门仍94/1/1/1/1/0，不把本局部定理自动记成 full_target_linked。下一步审查真实 BuildintPre 对三条强入口的蕴含及未覆盖控制状态，建立生产 ISR 规格，再连接 WFInt；不通过增加任意正确性假设跳过缺口。
