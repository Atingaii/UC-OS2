# 第205步：中断退出非调度路径的完整本体 Hoare 证明

## 这次从哪里往前推进了

第204步只把三个函数放进同一 P/Spec，并准确暴露 OSIntExit 的本体义务。本步不再增加调用图包装，而是直接证明已接受归一化本体的非调度路径：

`saved=0 → running判断 → encrit → nesting递减 → 两级调度判断 → excrit → return`。

接口为 `V293_OSIntExit_nondispatch_body`，位于 `certiucos/v293/proofs/V293OSIntExitNondispatch.v`。

| 输入路径 | 本步证明的结果 |
| --- | --- |
| running=1，nesting≥2 | nesting 变为 pred nesting；不调度；恢复原 IE/ISR 栈/临界区栈；返回 None |
| running=1，lock>0 | nesting 饱和递减至 pred nesting；不调度；恢复原现场；返回 None |
| running≠1 | 不进入临界区，nesting 不变；原现场保持；返回 None |

所有路径都真实写 saved=0；局部字节仍分配着。本体 Hoare 的 return 不是完整函数调用及局部释放的执行定理。初始 IE 可以为 true 或 false；ISR、ISR 栈和临界区栈均参数化。byte 范围为 0…255。

## 资源证明不是把中段留作假设

原 `V293_time_critical` 提供临界区资源取得/归还的规则，但要求证明任意 extra 资源穿过中段。本步通过真实 `V293_OSIntExit_disabled_hoare` 消去这个前提，再接 saved 初始化、running guard 和 return。

初始 IE=true 时，原 encrit1/excrit1 规则取得并归还 `invlth_isr I 0 (gettopis si)`；IE=false 则走 encrit2/excrit2。实际 OS 状态和取得的不变量不是 GoodFrm，不把它们强行作为普通 frame。标量更新规则直接携带它们；GoodFrm 只用于外围普通数据。

主接口没有 dispatch 证明、callee lookup、端口契约或执行结论前提，Spec 和 ambient I 任意。归一化仍沿用 ADR-0005/0010，不是原端口 refinement。

## 非空性和前瞻单因素对照

协议在编辑新 Coq 源码之前记录在本步 `protocol.json`，原 C 三函数重新预处理并逐项核对来源。

`audit/probes/V293OSIntExitNondispatchProbe.v` 从既有独立字节/环境见证提取实际所需资源，构造 `QNpre_nonempty`。相同内存下，任意初始 IE、两种栈及 running/nesting 都可满足前置；具体见证 lock=0，因此运行中的实例采用 nesting≥2。空 LocalInv 仅是测试 fixture，仍保留真实当前任务指针资源，不是生产不变量或初始化可达证明。主定理的 lock>0 路径由参数化 Coq 推导覆盖，不冒充已构造了该分区的具体见证。

单因素对照只在**临界尾段**删除 excrit：相同内存、ISR 和压栈状态下，正控实际执行原 `loststep/excrit_step`，恢复 IE 和栈；删除后保留 `enabled::ci`，与恢复所需的 `ci` 长度不同，所以两种 IE 下都不满足原 OS 后置。该对照没有构造两个完整函数执行，也不能代替 saved、递减或 dispatch 的独立证明。

## 对抗性核查

- 前置是否空洞：独立资源见证，不从 InfRules 反推可满足性。
- 是否仍藏着中段证明前提：主定理及 critical 定理都不含该前提；内部实际证明任意 extra 更新规则。
- 是否只照顾 IE=true：接口量化 enabled，原临界规则分别处理两值；尾段也显式实例化两值。
- 是否误把 Atrue 当作生产不变量：具体剩余资源可藏在测试 frame 的 Atrue；ambient I 的取得/归还仍由真实规则参数化。但生产不变量资源分配尚未建立。
- 是否完成第204步 iff：没有。这里只证明受限路径的本体断言，尚未接到三函数环境的全部真实 builder，不能宣布 WFFunEnv。

递归 coqchk、逐根假设、完整回归和原有失败保留的实际结果见 `audit/logs/stage205-interrupt-exit-nondispatch/verification.json`。失败编译尝试保留源快照，不改写为成功。

## 仍须完成

最外层 nesting=1/lock=0 的调度路径，包括共享 ready/task 资源访问、实际调度契约和 switch/LocalInv 交接；还须统一真实 builder、生产 ISR/WFInt、完整任务不变量和初始化，再闭合源码级 GOOD_OS 与同程序 K1–K4，之后才启动 uCOS3。

本步的 nesting/lock 属于调用者持有的普通数据侧。尚未证明生产 Inv 能以该方式提供资源，这是集成时必须处理的边界。六门仍 94/1/1/1/1/0；总目标保持 active，未提交、未推送。
