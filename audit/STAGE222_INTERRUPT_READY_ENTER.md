# 第222步：从就绪共享边界进入真实 OSIntEnter 调用

## 本步解决什么

第221步接通了 ISR 包装两端，但中间函数尚未接入。本步只推进其中的 `OSIntEnter`：从同一 ready/TCB/storage 不变式取出真实控制字节，证明完整原函数体，再接真实函数构造器和调用规则。不修改 C、固定配置、AST、框架、tactics、旧证明或历史失败证据。

生产接口：`certiucos/v293/proofs/V293InterruptReadyEnter.v`。
非空与单因素对照：`audit/probes/V293InterruptReadyEnterProbe.v`。
冻结前协议和全部核验记录：`audit/logs/stage222-interrupt-ready-enter/`。

## 证明链条

| 接口 | 已证明的内容 |
| --- | --- |
| `V293_storage_byte_value` | 实际 `Tint8` 类型匹配推出值是某个 0..255 字节；不把任意值假定成 1 |
| `V293_enter_ready_extract` | 从同一 SWINV、全局名称绑定、当前线程局部不变式和空局部域提取 running/nesting；任意 prefix/suffix 存储布局保持不动 |
| `V293_OSIntEnter_ready_updates` | 使用原更新语句：仅 running=1 且 nesting<255 时递增；更新后仍是合法字节，关闭回原 SWINV |
| `V293_OSIntEnter_ready_body` | 连接完整原函数体，包括实际 return；保留同一 Inv、中断栈和临界区栈 |
| `V293_OSIntEnter_ready_contract` / `ready_builders` | 接入真实 `BuildPreI` / `BuildRetI`，处理参数列表与非法逻辑实参，不增加额外 callee-Hoare 前提 |
| `V293_OSIntEnter_ready_WFFunEnv` | 为这个新契约建立单函数真实代码环境；不是旧三函数联合环境的替换声明 |
| `V293_OSIntEnter_ready_call` | 用原 `call_rule` 证明实际 `scall`，frame 仅为空局部域；OS 上下文在契约内，不假装它满足 GoodFrm |
| `V293_irq_ready_enter_call` | 第221步 EOI 后的 closed 断言加全局名称绑定，推出本次调用入口并连接调用 |

外部逻辑实参只传 abstract code、中断栈和临界区栈；**不要求调用者猜 running/nesting 的物理值**。全局名称绑定是环境地址约束，不是函数值或执行结果的预言机。内部从存储提取值以核验分支，外部后置重新隐藏这些值，因此这里只提供共享所有权保持，不提供长期计数/栈深关系。

原代码、表达式与类型转换沿用已锁定的 V2.93.01 模型，四个相关配置后函数重新还原并核对定义、函数体与源码区间哈希，详见 `source-check.json` 与 `source-recheck.json`。

## 非空与单因素对照

`ENnonempty` 从第221步的真实 TCB 与完整存储物理实例获得当前入口；`ENbuilders_nonempty` 证明真实 BuildPreI 可满足，不是仅靠空前置的形式通过。

`ENzero_nonempty` 先通过两个合法物理 byte store 构造 running=0、nesting=0 的基线，这一准备步骤不是消融本身。`ENsingle_running_control` 从这个固定基线只把地址 `(96,0)` 的 running 字节从0改为1：

- 两侧都满足同一个共享不变式入口，保留同一 TCB、nesting、ready/dispatch/其他存储、环境、中断状态、栈、抽象资源和 abstract code；
- 对每个不同地址，证明物理内存内容不变；
- 对两侧分别求值原 `V293_OSIntEnter_running` 表达式，分别为 false/true；
- 原计数函数在 nesting=0 时分别为0/1；nesting=255 的饱和事实另作纯计算检查。

**这不是两份完整 OSIntEnter 或完整 ISR 执行，也不是从 OSInit 可达的证明。** 255 对照是计数函数计算，不冒充该状态的整段执行。它没有修改生产 AST，也没有删除其他不利结果。语义证明先于本轮新增 Python 结构回归，不声称语义 TDD。

## 对抗式复核与边界

1. **typed storage 是否足以推出字节，而不是多了一个运行值假设？** 展开实际 `rule_type_val_match Tint8`，使用 Int.unsigned 范围；extract 只返回0..255，不固定 running=1/nesting=0。
2. **更新是否遗失任意前后缀或 TCB？** 两个字节的拆合保持 prefix/suffix、ready core、dispatch cell 和线程局部资源；close 回相同构造的 Inv。
3. **中断上下文是否非法放进 call frame？** Ais/Acs 和 SWINV 归入 GoodFunAsrt 契约；call frame 只有 A_dom_lenv nil。
4. **call 是否循环假设被调用函数正确？** 实际 body 和内部 builder 契约已先证明，单函数 WFFunEnv 闭合；调用定理只要求 Spec lookup，不接受一个现成的 callee InfRules。
5. **能否立刻串出整段 ISR？** 不能。本步只是 closed 边界到 Enter。当前局部接口使用 CurLINV，未证明原 ISR `p_local` 逻辑见证的精确返回重建；尚未联合旧动态三函数 Spec，未连续连接 Exit/调度/iret，也没有生产 ISR 抽象规格或 WFInt。
6. **任意合法字节是否等于生产控制语义正确？** 不是。storage 仍只是类型/所有权，尚无 nesting 与实际中断栈深度、running 与启动状态、lookup 与就绪/优先级缓存的一致关系。

## 核验与下一步

实测结果以 `verification.json` 为准：逐根假设打印、两个新增入口及递归依赖的 coqchk、两次增量构建、新增5项结构回归、全量测试旧失败集合与顺序复核、四函数源码身份复核，均保留命令、退出码与原始日志。所有失败编译快照保留，既有审计失败与空白失败不改写。

下一步是把新 Enter 上下文契约接进现有动态函数环境，继续连接 ISR 中间 Exit/调度调用与精确返回资源；随后仍有生产不变式、WFInt/API/初始化、顶层 GOOD_OS 与同程序 K1–K4 的工作。

六门覆盖仍为 `94/1/1/1/1/0`。本步不是整核里程碑，持久总目标 active，uCOS3 未开始，未提交/推送。专用一次性 Trust 驱动与产品在清点后删除，原缓存按字节恢复；源码、失败证据及可复用 Coq 产品保留。
