# 第206步：真实调度调用保持 ISR 现场及已取得资源

## 为什么要做

第205步证明完整非调度路径，但没有调用 `OS_SchedNew`。退出调度路径需要实际调用该函数；旧 plain 契约只允许外置 `GoodFrm`，而 ISR 位图、ISR 栈、临界栈不是 `GoodFrm`。已有的 `SWINV` 版本又不能直接替代任意 ISR 现场和本次临界规则取得的低层不变量。不能把这些资源丢掉、强称为 frame，或把整个调用正确性当作前提。

本步复用已有 `V293_sched_internal_payload` 的真实函数本体证明，仅新增适合该调用边界的动态契约，没有复制调度算法或修改框架。

## 新增的最小接口

生产入口：`certiucos/v293/proofs/V293OSSchedISRContext.v`。

- `V293_sched_ISR_context I held ir si ci` 是 `OS[ir,false,si,ci]` 加上 `held=true` 时的 `invlth_isr I 0 (gettopis si)`。
- `held` 表示调用前是否持有该不变量，**不是当前 IE**；调度调用发生在 IE=false 的临界区内。
- 这些资源放在 `GoodFunAsrt` 的函数规格内。文件同时证明此上下文不是 `GoodFrm`；调用规则外只放普通 `GoodFrm frame`。
- 编码含六个逻辑字段：位图两字节、抽象操作、held、ISR 位图、ISR 栈、临界栈。不是固定某一次调用的栈。畸形编码返回 `Afalse`；字节范围和非空就绪条件保留在真实前置中。
- 资源所属的 `I` 和规则环境的 `RI` 分开，不要求它们相同。

`V293_OSSchedNew_ISR_contract` 对原 `V293_OSSchedNew_function` 的实际 `BuildPreI/BuildRetI` 直接产生 `InfRules`；只有源码查找、名字不冲突和真实 builder 等式作为前提，未预设 callee/中段证明。`V293_OSSchedNew_ISR_WFFunEnv` 闭合该增强规格的**单个调度函数**环境。

## 本轮实际向上接到了哪里

`V293_OSSchedNew_ISR_call` → `V293_OSSched_ISR_prefix` → `V293_OSIntExit_context_same_dispatch`。

最后一个定理实际连接：

1. `OSIntNesting` 的条件递减，初值0或1时结果0；
2. nesting/lock 两个调度 guard 均为真；
3. 真实 `OS_SchedNew()` 调用，计算最高就绪优先级；
4. 从优先级表读取并写入最高任务指针；
5. 最高优先级等于当前缓存时，优先级比较为假，不调用 handoff，counter 不变。

它是 **enabled dispatch 的同优先级中段**，不是第205步的“跳过调度”，也不是不同任务切换。任意 ISR、两栈和已持有资源都通过该调用保留；证明结论只有一个 `InfRules`，没有整个中段或 dispatch 的 Hoare 前提。

## 非空正控与单因素对照

探针：`audit/probes/V293OSSchedISRContextProbe.v`。

- 从独立构造字节内存的 `BLnonempty` 建立 `QSpre_nonempty`，不是假设目标断言成立。
- 同一具体堆、全局/局部名字、抽象任务表和操作，`QSselector_nonempty` 满足正确编码选择的调用前置（余下资源放 `Atrue`）。
- 对照仅将编码中的临界栈字段 `nil` 改为 `true::nil`，其他字段和物理状态不动。`QSboth_decoders` 证明两侧都成功解码；`QSwrong_stack` 由实际 `Acs` 不一致排除错误前置。因此不是畸形编码的提前拒绝。
- `QSenabled_same_dispatch` 在 ready bitmap=(0,16)、最高/当前优先级12、nesting=1、lock=0 的场景实例化实际中段；`QSscheduler_environment` 实例化单函数环境。

**对照只检查规格与现场身份，不是两份完整执行的消融。** 具体正控仅为 held=false、空两栈、ISR 全清、测试用空 LocalInv；参数化生产定理没有这些限制。未构造 held=true 的独立非空生产不变量见证，也未构造新的实际 builder 分配态非空见证；不能把调用前置非空写成初始化可达或 `sat(INV)`。

## 源码、核验与回归

证据目录：`audit/logs/stage206-scheduler-isr-context/`。

- `protocol.json` 在新增 Coq 源码之前冻结本步主张和对照。
- `source-check.json`/`source-recheck.json` 从固定配置重建修复源码，逐一定位 OSIntEnter、OSIntExit、OS_SchedNew；保留函数文本与哈希。原源码、配置、AST、框架、旧证明/测试和第205步冻结证据不变。
- 每次编译保存源码快照和完整日志，包括失败；`stable-compiles.json` 指向最终成功版本。
- `trust.json` 逐根 `Print Assumptions` 并递归 `coqchk`；允许集不扩大。检查期间 Coq 输入不变。
- 新增5个结构回归；它们不替代 Coq 语义证明。完整回归逐项比较旧失败/错误的顺序，不删除旧失败。
- 最终实测结果、清理清单及原缓存恢复结果以 `verification.json` 为准；未提交/推送。

## 还没有完成

1. 该增强 scheduler Spec 和旧 plain Spec 不同，尚未把它接入第204步的同一三函数环境，不能借旧 iff 宣称已闭合。
2. 新接口尚未连接退出函数的 saved 初始化、run guard、encrit/excrit、return 的完整调度路径及其全部实际 builders。
3. 仍没有不同任务 handoff 的整体 Hoare、从生产 Inv 取得 nesting/lock/就绪数据的证明、生产 ISR/LocalInv/WFInt、完整初始化、源码级 `GOOD_OS` 或同程序 K1–K4。
4. 六门维持 `94/1/1/1/1/0`，本步不提高覆盖。uCOS3 未启动，总目标保持 active。

下一步应先把本步调用接口与第205步临界资源规则接起来，闭合**完整同优先级退出路径**，然后再处理不同任务 handoff 和统一函数环境；不能只靠增加文件数宣称接近整核完成。
