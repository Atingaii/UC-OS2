# 第233步：连续连接不触发调度的中断路径

## 本步解决什么

此前 Enter 的部分合同关闭 Inv 后丢失了控制值，不能从弱返回反推出后续 Exit 所需的精确值。本步新增 open exact Enter 合同，从原更新与函数本体经真实 BuildPreI/BuildRetI、call_rule 保留 running、nesting、lock 和 p_local；没有修改 C、配置、AST、框架或旧证明。

主接口 `V293_interrupt_quiet_continuous` 连续证明原 `V293_irq_source_wrapper` 的 **EOI → OSIntEnter → OSIntExit（quiet）→ exint**。没有把中间执行或任意资源蕴含当作待调用者提供的前提。新 Spec 对原 Enter/Exit/SchedNew 程序给出 WFFunEnv/WFIFun；Exit 仍是第232步的原两级动态三路径合同。

## 资源如何跨调用

Enter 持有 running 的完整写权限；Exit quiet 只借用其中一半，另一半作为 caller frame 跨越真实调用，返回后重新组成完整权限。ready 核心、typed TCB、dispatch cell 和 storage 保留在同一资源框架中，控制字节归还 typed storage，关闭同一 Inv 后调用真实 iret_rule。没有用 Atrue 吞掉交付资源。

具体 probe 从既有实际字节堆 `JBmemory 1 Int.zero Int.zero` 构造 full ready/TCB/storage 强入口，证明它非空，并实例化共同函数环境和原 wrapper；不是仅靠一个不可能满足的前置得出结论。

## 必须保留的边界

- 这是 quiet 的**强入口**，不是 BuildintPre 的全部入口闭包，也不是 WFInt。running=1 时要求 nesting<255，且已有嵌套层或持有调度锁；clear ISR、空 critical stack、done None 抽象槽及返回 builder 等条件保留。
- nesting=255 时 Enter 不增，但 Exit 仍减到254；`V293_quiet_pair_saturation_counterexample` 证明不能删除未饱和条件。原 nesting=0/run=1/lock=0 经 Enter 后不属于 quiet；`QCdispatch_entry_not_quiet` 显式保留这个反例。
- 以上是边界算术反例，不是两次完整执行，也不声称完成 permission 或 wrapper 级执行消融；结构测试不代替语义证明，不声称语义 TDD。
- 具体 fixture 使用**常 Aemp LocalInv**；虽然包含完整既有 ready/TCB/storage 资源，这不表示生产 ISR LocalInv、全部控制值关系、lookup 语义与物理 ISR 栈深关系均已进入 Inv。
- fixture **不是初始化可达**。该 wrapper 没有 tick 的抽象动作，不能冒充 tick ISR。
- changed/same 的连续 wrapper、全部中断入口、初始化、最终 GOOD_OS、同程序 K1–K4 仍开放；**uCOS3 未开始**。

## 验证与下一步

机器实测位于 `audit/logs/stage233-interrupt-quiet-continuous/verification.json`：逐源编译与失败快照、28个根的假设闭包、三个入口模块的递归 coqchk、两次增量构建、结构测试和全量回归。只接受既有 classic / functional_extensionality_dep 假设边界。

旧423个失败、1个错误以及 audit 的 stale function identity、旧 whitespace 失败必须保留，不能为了此检查点改写历史证据。六阶段覆盖仍为94/1/1/1/1/0，最终 GOOD_OS 未完成。

下一步将同一精确入口与资源归还方法接到 changed/same 连续路径，然后处理 WFInt 的真实入口闭包；不能把这条 quiet 强入口的成功直接推广到所有 ISR。
