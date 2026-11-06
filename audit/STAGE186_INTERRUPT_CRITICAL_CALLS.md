# 第186步：OSIntExit 的 saved 初始化与真实指针调用边界

## 从哪里继续

第185步证明了真实递减、嵌套／锁守卫和调度分支，但没有处理 `V293_EnterCritical(&saved)`、`V293_ExitCritical(&saved)` 的实参及资源边界。本步直接使用固定源码的实际 `scall`，不把它们替换成 `encrit/excrit` 原语，不构造空端口实现。

源码重放及预先冻结的单因素协议见 `audit/logs/stage186-interrupt-critical-calls/`。原 `OSIntExit` 位于锁定 `os_core.c` 的693–736行；准确哈希、配置后函数体与直接调用清单记录在 `source-check.json`。C、配置、原AST和旧证据均保持不变。

## 解决了什么

生产模块：`certiucos/v293/proofs/V293OSIntExitCriticalCalls.v`。

1. `V293_saved_pointer_argument`：从 caller 持有的 `Alvarenv saved Tint32 (bs,0)` 推出真实 `&saved` 的值和类型，不把表达式求值当成外加前提。
2. `V293_saved_pointer_call`：通过框架实际 `call_rule` 证明指针实参调用。callee 的 `GoodFunAsrt` 资源可以包含 saved 的物理内存、共享状态及中断资源；caller 的局部名称绑定留在 `GoodFrm` 中。该名称断言不能成为 `GoodFunAsrt`，模块单独证明这一点。
3. `V293_OSIntExit_saved_initialize`：执行真实 `saved := 0`，入口允许任意旧值；把物理保存槽交到 callee 资源，局部绑定仍归 caller。
4. 稳定接口 `V293_OSIntExit_critical_calls`：按原AST组合真实 enter、真实 nesting/dispatch 中段和真实 exit。四个地址参数化资源 `entry/acquired/leaving/restored` 可不同，各自的函数资源合法性和 CurLINV 都显式检查；两个真实 Spec lookup 不被省略。

**这里仍要求调用者提供整个中段在上述 acquired/leaving 资源下的 Hoare 证明。** 第185步中段使用的联合资源含 caller 名称；本步尚未完成将这些名称剥离为 caller frame 并接入四个 callee 资源的桥梁。不能把两个各自通过的接口当成已完成组合。

## 非空物理见证与单因素对照

探针：`audit/probes/V293OSIntExitCriticalCallsProbe.v`。它独立构造两个物理32位槽、真实当前任务指针槽及同一 caller 局部环境，没有导入旧 audit 探针。

| 检查 | 保持不变 | 改变与结论 |
| --- | --- | --- |
| 指针绑定 | 同一物理堆、值、IE、局部类型与 domain | 只把局部绑定从块751改指向752；两个正确实参均可求值，旧地址由实际求值冲突排除 |
| 保存值 | 同一局部绑定、IE及其他物理块 | saved 从0改1，指针地址不变；新资源可满足，旧值资源被同一堆的 `load Tint32` 排除 |
| 块外保持 | 其他物理资源 | saved 块751以外每个字节保持相同 |
| callee lookup 消融 | 签名、地址与其他输入 | 仅去掉对应函数 lookup 后，匹配条目变成 None；只验证输入层，不证明下游执行或 body |
| caller/callee 隔离 | 同一名称断言 | `GoodFrm` 成立，`GoodFunAsrt` 不成立 |

`SCnonempty` 与 `SCalternate_nonempty` 同时持有完整资源与余下 caller frame，不是分开造不兼容堆。`SCcall_checked` 实例化非 identity 契约，演示 saved=0/IE=true 到 saved=1/IE=false 的资源可表达且两端非空。这只是契约的两个独立快照，**不是一次执行，也不是端口实现证明；1不被声称为实际 CPU_SR 编码。** 该示例同时改变两个字段，不充当单因素消融。绑定、保存值、lookup 对照分别隔离因素。

探针的空 LocalInv 仅用于非空见证，不代表生产ISR不变式。真实初始化和指针调用的 InfRules 实例另由 `SCinitialize_checked`、`SCcall_checked` 检查。

## 检查方法与限制

- 每次 Coq 编译保留原源码快照及日志，包括失败尝试。新源码不含未完成证明占位符，不修改旧 framework、tactics 或测试以消除失败。
- 对两入口全部 Lemma/Theorem 逐根 `Print Assumptions`，递归 `coqchk`；只接受前一步已有信任边界，具体根和依赖以 `trust.json` 为准。
- 新增5项结构／证据测试；完整回归运行两轮，必须保留旧423失败、1错误的完整有序ID，而不仅比较数量。旧 stale identity 审计及 inferules 第581–586行空白问题继续保留，不宣称全绿。
- README、VERIFICATION_STATUS 只前置本步说明，_CoqProject 只追加新生产文件。最终结果、编译次数、清理清单与哈希以 `verification.json`、`checkpoint-evidence-manifest.json` 为准。

尚未完成：第185步中段的 callee/caller 资源桥、实际临界保存恢复契约与实现、OSIntCtxSw 义务、运行守卫、真实函数 builder、完整 OSIntExit、生产ISR/LocalInv、全局初始化／环境、全交错 simulation、同程序 K1–K4、最终 `GOOD_OS`。本步也没有新增 RuleSound 到完整函数语义的结果。

六门仍为 `94 / 1 / 1 / 1 / 1 / 0`，第一阶段未完成，uCOS3尚未启动，总目标 active；未提交／推送。下一步优先把已证中段的局部名称与函数资源分离，完成与本步真实临界调用接口的同资源连接，而不是再增加不相连的抽象。
