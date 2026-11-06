# 第225步：原 OS_SchedNew 保留精确局部资源

## 为什么要做这一步

最终目标仍是固定 V2.93.01 源码级 `GOOD_OS` 与同程序 K1–K4，然后才开展 uCOS3。第224步已贯穿 Enter 并接通 EOI→Enter，但原调度器契约只保存 `CurLINV`，不能凭此恢复中断返回规则要求的精确 `p_local`。

`CurLINV li tid` 包含存在的逻辑见证和 `Atrue`，后者允许隐藏额外资源；`p_local li tid nil` 没有该剩余资源。问题是证明边界过弱，不是新发现的 C 运行错误。本步不改旧证明，不从弱后置条件逆推强后置条件。

## 本步交付

生产文件：[V293OSSchedExactLocal.v](../certiucos/v293/proofs/V293OSSchedExactLocal.v)。

1. 保持原 bitmap、名称绑定和原函数程序。两次真实赋值分别调用原 `assign_rule`，读取和侧条件可弱化，前后断言一直保留精确 `p_local`。
2. `V293_OSSchedNew_exact_body` 连接两次赋值与原 return，保持最低就绪优先级结论及 `result=None`。
3. 复用原 entry context、return bindings 和局部单元释放规则，证明真实 `BuildPreI` / `BuildRetI` 契约；`V293_OSSchedNew_exact_contract` 不以 callee 的 `InfRules` 为前提。
4. `V293_OSSchedNew_exact_WFFunEnv` 连接既有单函数 unit。资源所属 `I` 与规则 ambient `RI` 分离并任意量化；没有以空 invariant 替换生产环境来制造通过。
5. `V293_OSSchedNew_exact_call` 使用原 `call_rule` 和原临界区逻辑实参 codec。`SWINV` 与两栈在 callee 契约内；仅外部 `frame` 要求 `GoodFrm`。完整本体可保留任意内部 payload，不把栈误放在 frame 中。
6. `V293_sched_exact_post_retains` 显式给出精确局部资源、原输入数组、名称绑定、关中断标志与更新后的优先级字节。复用原 generic-common 的 `V293_OSSchedNew_post`，删除开发中发现的重复定义。

## 非空入口与单因素对照

[探针](probes/V293OSSchedExactLocalProbe.v) 直接在原 scheduler 字节 fixture 上构造精确 current 片段，并在同一真实数组/输出/局部字节堆上满足原 builders。`ELbuilders_nonempty` 同时给出实际 `BuildPreI`、`BuildRetI` 等式和入口满足性，不是任意 `Afalse` 前置。

**可满足性 fixture 的 owned CI** 为 `ELCI k := V293_shared_inv (S k)`，是既有不变量的空尾。它只检验通用 scheduler 契约非空，不是生产 ready/TCB/storage ISR 不变量的联合非空实例。`ELenvironment` 和 `ELactual_call` 的 ambient `RI` 仍任意；任意参数定理不等于已安装真实生产环境。

复用第224步已冻结的 `RLlocal_exactness_control`，在本步信任驱动中再次直接检查该根及递归模块，不复制一个同义新定理。固定 `REstate`、物理堆、TCB、程序与其他参数，仅将局部断言由 `CurLINV V293_shared_li OwnershipWaiting` 换成 `p_local V293_shared_li OwnershipWaiting nil`：前者成立、后者不成立。这是单因素局部断言反例，**不是 scheduler 完整前置反例、不是两次函数执行，也不能证明下游 dispatch/switch 已工作**。本步非空入口与该旧对照是不同 fixture，不能合并成一条执行轨迹。

## 验证与保留的失败

协议在实现前固定于 [protocol.json](logs/stage225-sched-exact-local/protocol.json)。实测以本步 [verification.json](logs/stage225-sched-exact-local/verification.json) 为准，包括两次构建、新结构测试、全量测试、逐根假设、递归 `coqchk`、配置后源码身份及旧文件校验。

开发编译失败的源码快照、错误和诊断输入全部保留，不重写失败。新增 Python 测试是结构回归，语义依据 Coq，不声称语义 TDD。本步实际假设闭包只有 `Classical_Prop.classic` 与 `FunctionalExtensionality.functional_extensionality_dep`，收尾与只读核验另行检查这两项上限。继承的 trust 白名单还列有旧 `Eqdep.Eq_rect_eq.eq_rect_eq`，本步未使用；不改写该旧白名单或已录制的 trust 报告。

旧全量回归的423失败、1错误应原 ID / 顺序保留；旧 `make audit` 的 stale function evidence identity 和旧 `inferules.v` 空白失败不修改、不降低 gate。审查由本轮同一执行者完成，不称独立审查。清理只针对先清点的一次性信任驱动及其编译产物、任务缓存备份和一个本步空临时文件；保留证据、源码、可复用 Coq 产物及既有缓存，并恢复两份既有算术缓存原字节。

## 明确尚未完成

- 精确局部逻辑见证当前固定为 `nil`；任意 LocalInv 不允许自由改变见证。选定常量 Aemp 的 LocalInv 才有第224步的定义相等性质。
- 新契约尚未替换原三函数 Spec 的 scheduler 条目；不能认为 Enter→Exit→调度已经连续连接。
- 仍需在 storage prefix、ready dispatch、switch 与完整 Exit 的边界保持精确资源，然后联合统一环境。
- 非初始化可达；未建立生产控制值/lookup 关系、完整 ISR、嵌套中断闭包、`WFInt`、API/初始化、`GOOD_OS` 或同程序 K1–K4。
- 六门保持94/1/1/1/1/0，总目标 active；未提交/推送，uCOS3 未开始。

## 下一步的最小接口

首先在 `V293_resource_OSSched_critical_prefix` 所在的真实 call→指针赋值前缀中使用新 exact call，而不是更换旧弱后置中的符号。随后重建 `V293_retained_storage_prefix_returned` 对应的精确返回边界，复用原半权限数组归还与 `V293_dispatch_output_named`。只有该边界实际保留局部资源，才能继续处理 ready dispatch/private 和 Exit builder，最终接回完整 ISR。
