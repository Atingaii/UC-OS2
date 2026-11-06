# 第223步：同一就绪不变量下的三函数联合环境

## 本步解决什么

第222步已证明真实 `OSIntEnter` 的上下文契约，但只接入单函数环境。本步把该契约接进原来的三函数程序，与动态 `OSIntExit`、`OS_SchedNew` 共用同一个 ready/TCB/storage 不变量，建立真实 `WFFunEnv`、`WFIFun` 并证明实际 Enter 调用。不修改 C、固定配置、AST、框架、tactics、旧证明或历史失败证据。

生产接口：`certiucos/v293/proofs/V293InterruptReadyEnvironment.v`。
非空与单条目对照：`audit/probes/V293InterruptReadyEnvironmentProbe.v`。
前瞻协议及完整核验日志：`audit/logs/stage223-interrupt-ready-environment/`。

## 证明链条

| 接口 | 已证明的内容 |
| --- | --- |
| `V293_ready_irq_inv_layout` | Enter 的 prefix/running/nesting/suffix 布局与原动态 Exit 的 Inv 定义相等，不更换资源不变量 |
| `V293_ready_irq_spec` / `unit` | 保持原三函数代码单元，仅替换 Enter 规格条目；Exit 与 SchedNew 的契约保持原定义 |
| `V293_ready_irq_domains` | 程序与规格定义域相同 |
| `V293_ready_irq_WFFunEnv` | 三个真实本体分别用已经闭合的完整契约检查；无需假定现成 callee InfRules |
| `V293_ready_irq_WFIFun` | 将上述真实函数环境接到框架 WFIFun，不保留开放的函数体义务 |
| `V293_ready_irq_Enter_call` | 联合 Spec 和同一 Inv 下，用原 call_rule 建立真实 scall；调用契约保留 OS 两栈、共享资源与当前线程局部资源 |

`REenvironment` 使用原 `RDprogram`、原 `RDinv` 实例化联合环境，并证明该 Inv 的实际 `GoodI`。因此不是另造一个程序或更弱的不变量来得到接口兼容。

调用定理只要求 Enter 与 Exit 标识不同即可选择正确规格；整个三函数环境另需标识互异、局部名称不遮蔽及 `GoodFrm extra`。不能把调用定理更少的 lookup 前提当成整个环境已无条件成立。

## 真实非空与单因素对照

`REheap` 从真实 typed TCB、完整 lookup、ready 位图和控制存储实例构造同一共享 core。`REentry_nonempty` 将其关闭成新 Enter 的边界，`REbuilder` 精确计算真实 `BuildPreI`、`BuildRetI`：返回构造器还明确要求 `result=None`，并非只有所有权后置。

构造入口使用断言稳定性调整 localenv、辅助栈与 abstract code；物理内存和抽象资源仍是原实例。**这只是满足性证明，不是从 OSInit 到此状态的可达性或实际执行轨迹。** `REexit_nonempty` 保留原动态 changed Exit 的独立非空入口（nesting<=1、任意 counter/旧缓存/临界区栈），并确认联合 Spec 中 Exit 条目未变；它不声称这个入口由前述 Enter 调用到达。

`REsingle_entry_control` 固定程序、状态、新逻辑实参，只把 Enter 规格条目换回旧规格：

- 新条目的实际 BuildPreI 可被同一真实状态满足；
- 旧条目不能解码新上下文实参，实际 BuildPreI 得到含 Afalse 的前置，任意状态均不满足；
- 其他所有函数的规格条目与原环境相等。

**这是单条目规格适配/解码入口对照；旧侧提前拒绝，不是两份合法入口，更不是两次完整函数或 ISR 执行。不能用它证明任何下游机制。** 下游本体、builders 与调用的正确性来自单独的 Coq 证明。语义证明先于新增 Python 结构回归，不声称语义 TDD。

## 对抗式复核与明确限制

1. **不变量是否偷偷变弱？** 布局定理是定义相等；实例直接使用原 RDinv，未删除 ready/TCB/storage 因子。
2. **函数环境是否循环假设被调用函数正确？** WFFunEnv 的三个分支分别调用完整 Exit/Enter/SchedNew 契约，无额外 callee InfRules 前提。
3. **真前置是否为空、后置是否漏掉返回值？** 真实堆实例满足新边界；REbuilder 精确保留 result=None。
4. **条目对照是否混入状态或程序变化？** 对照固定新实参和同一物理状态，证明除 Enter 外其他规格条目都不变；它只说明解码入口适配。
5. **是否已连接整段 ISR？** 没有。联合环境不等于连续 EOI→Enter→Exit→iret 的推导；原 ISR p_local 的精确返回资源尚未重建，生产 ISR 抽象规格与 WFInt 尚未闭合。
6. **所有权是否等于控制语义？** 没有建立 nesting 与 ISR 栈深、running 与启动、lookup 与优先级缓存的一致性，也没有完整生产数据 Inv 或初始化。

## 核验与下一步

实测结果以本目录 `verification.json` 为准。逐根假设检查、两个入口的递归 coqchk、两次构建、新增5项结构回归和全量回归均保留原始日志；旧失败 ID 与顺序、不利编译快照及既有审计/空白失败保留，不报告全绿。

下一步优先重建原 ISR p_local 的精确返回资源，再把联合环境中的中间调用连续接到原中断入口与返回规则；不能把函数环境的闭合直接升级为 WFInt。其后仍需生产不变量、API/初始化、源码级 GOOD_OS 与同程序 K1–K4。

六门覆盖仍为 `94/1/1/1/1/0`，持久总目标 active，uCOS3 未开始，未提交/推送。专用一次性 Trust 驱动与产品在逐项清点后清理，原缓存按字节恢复；源码、失败证据和可复用 Coq 产品保留。
