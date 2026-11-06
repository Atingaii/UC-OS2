# 第237步：EOI/Enter 不再要求 ISR 全清，明确深度约束的放置边界

## 已落实的进展

新增 `certiucos/v293/proofs/V293InterruptEntryGeneral.v`，稳定接口 `V293_interrupt_entry_general` 从实际 `BuildintPre` 加原显式 globals frame 出发，复用上一轮的控制值开包，连续证明实际 EOI 与同一规格中的精确 Enter 调用。

与第236步相比，移除了 `forall j, ir j=false`，其他查表、合法中断号、地址绑定、typed storage 等要求不变。后置不再把 ISR 位图写死为全清，而是精确保留 `isrupd (isrupd ir i true) i false`，并保留 `i::si`、空 critical 栈以及 `nest_after` 的旧值/新值关系。已有 Enter 合同支持任意 ISR 位图，因此不修改 C、AST、旧规格、Inv 或任何冻结证据。

这消除了一个实际多余的入口要求，不是另加一个更强的入口。仍然只覆盖 EOI/Enter 前缀。

## 给初学者的解释

| 项目 | 含义 |
| --- | --- |
| ISR 位图 | 哪些中断的请求位还处于活动状态 |
| ISR 栈 | 当前及被打断的中断上下文；与位图不是同一个概念 |
| EOI | 只清当前中断位，不应连带清除其他位 |
| Enter | 按实际 running/nesting 值决定是否增加 nesting，不改 ISR 栈 |
| Inv | 必须满足框架规定的稳定性，不能任意加入想要的等式 |
| 非空入口 | 真有具体内存满足前置，而不是前置矛盾导致证明形式上通过 |

探针 `audit/probes/V293InterruptEntryGeneralProbe.v` 保留原 `JBmemory 1 Int.zero Int.zero`、ready/TCB/storage、地址绑定、`RDprogram/QCspec` 和三函数 `GoodI/WFFunEnv/WFIFun`。使用 prior 位1活动、进入位0、栈 `[0;1]` 的状态，从原 typed 资源重建实际 builder。`EGentry_nonempty` 与 `EGactual_prefix` 分别验证非空性和实际前缀推导；`EGother_active_survives`、`EGEOI_exact` 证明 EOI 后位1仍为 true，并精确恢复 prior 位图。

## 去掉全清条件的对照

这是对入口要求的消融，不是两次完整执行的性能实验：

- 原第236步主接口：要求 prior 所有位 false。
- 新接口：其余要求不变，保留实际 EOI 后位图，不再要求 prior 全清。
- 具体新增入口的 `EGnot_all_clear` 证明 prior 位1为 true，因此它确实不满足原来的全清要求；不是把一个原本已满足全清条件的入口重新命名。
- 同一真实字节堆上的新 builder 前置非空，新前缀成立，EOI 只清当前位。

位图和栈同时变化的具体 fixture 是边界样例，不单独宣称它是单因素运行时实验；本轮没有宣称两次完整执行或覆盖所有 Exit 路径。

## 为什么不能直接把 nesting=栈深度放进 Inv

本轮检查的是框架的确切约束，而不是仅凭名字推断。

`framework/logic/assertion.v` 的 `inv_isr_prop` 最后一条要求：若当前 ISR 位图为 `empisr`，将 ISR 栈替换成任意栈后，同一堆和抽象资源仍满足该断言。

`V293_irq_inv_depth_relation_empty_at_clear` 在 Coq 中证明：对任意断言 p 与内存函数 depth，若 p 满足该稳定性、并且所有满足 p 的状态都满足 `depth(getmem st)=length(get_is_s st)`，那么 p 不可能包含 ISR 全清的状态。证明保持堆完全不变，只分别把栈设为合法样例 `[]` 和 `[0]`，会得到同一个 depth 同时为0和1。

这个结论只针对这种**对所有满足断言的状态要求精确相等**的放置方式。它不否定框架 soundness，不排除 heap-only 界限，也不排除初始化可达状态上的、按执行位置区分的关系。`EGheap_only_bound_closure` 正面检查字节上界仍满足 Inv 的 ISR 稳定性。

实际边界也有独立见证：`EGsnapshot_load_nest` 从 owned 字节断言推出真实 `load Tint8` 结果为1，`EGbuilder_allows_depth_mismatch` 证明同一个实际 builder 可以配栈深度2。进入中断后、调用 Enter 前，栈已经增加而计数尚未更新，这种相位差本身可能是正常状态。该见证不是初始化可达证明，也不是 C 程序运行时反例，不能据此擅自改源码。

## 明确未完成的部分

- globals 仍是显式附加 frame，不是由生产 Inv/LocalInv 供给；本轮尚未解决地址绑定。
- fixture 仍为常 Aemp LocalInv，不是生产 ISR LocalInv；不是初始化可达。
- lookup 固定内容、current priority 与当前 TCB 的对应，以及适当位置上的 nesting 语义关系仍需解决。精确深度等式不能直接强塞进现有 Inv。
- 新前缀支持任意满足 builder 的 ISR 位图，但没有连接这些状态的 Exit/iret；不是 `WFInt`。
- 没有生产 ISR 抽象动作/tick 本体闭合。`GOOD_OS`、同程序 K1–K4 未闭合，uCOS3 未开始。
- 六门仍为 `94/1/1/1/1/0`；旧423失败、1错误及 audit/whitespace 失败保留。结构测试不替代 Coq 语义检查，也不宣称语义 TDD。

## 验证与下一步

本轮实际日志、失败编译快照、源码重建、逐根假设与递归 `coqchk`、完整构建/测试均放在 `audit/logs/stage237-interrupt-entry-general/`。以 `verification.json` 的实测结果为准。

下一步优先落实生产入口的全局地址绑定、lookup 内容与 current/TCB 对应，再按实际前缀后置分流到 Exit/iret。nesting 的关系需要按框架允许的边界处理；本轮没有选定或实施新的全局架构，也不把开放条件当作已由初始化保证。
