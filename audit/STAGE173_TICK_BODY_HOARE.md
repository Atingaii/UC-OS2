# 第173步：原 tick 完整函数体的条件 Hoare 连接

## 本步解决的边界

第171步连接了 hook 调用契约与原后缀，第172步提供了真实返回／释放接口。本步补上函数体开头的 `cpu_sr=0`，并用 `ret_rule` 接入 `sret`，证明原 AST 的完整 body，而不是将 hook 换成 `skip`。

**准确结论：这是依赖明确 `Spec hook` 的完整 body 级 `InfRules` 证明，并通过 RuleSound 导出条件 `RuleSem`。它尚未连接 `BuildPreI`／`BuildRetI`，不是 `WFFunEnv`、完整函数实际执行或最终 `GOOD_OS`。**

固定对象仍为 uC/OS-II V2.93.01，源码提交 `0c4a48e6fbc6e915714e816196619a5481accf0c`。实际函数位于 `csrc/upstream/v2.93.01/checkout/Source/os_core.c:937–1008`，第950行保留 CPU hook；本步重新核对实际文件、函数区间和 analysis-port 说明的哈希，见 [source-check.json](logs/stage173-tick-body-hoare/source-check.json)。关闭应用 hooks 不等于关闭 CPU hook；analysis-port 只有其声明，不是可执行实现。

没有修改 C、配置、AST、framework、tactics、旧证明、旧测试或冻结证据，没有添加新不变量、CPU hook body 或执行成功 oracle。

## 最小证明链

生产文件：[V293TimeTickBodyHoare.v](../certiucos/v293/proofs/V293TimeTickBodyHoare.v)。

1. `V293_tick_body_entry` 使用 raw `V293_time_cell` 拥有 saved 的任意旧字节值，包括真实分配后的 `Vundef`；scan 同样是 raw `Vundef`。这没有把未初始化值当作有类型的整数／指针。
2. `V293_tick_body_initialize` 复用赋值规则执行真正的 `cpu_sr=0`。该操作只求值左地址与常量，不读取 saved 原值。saved 的局部绑定保留在 caller frame，不混进 hook callee 的 `GoodFunAsrt` 资源。
3. 稳定接口 `V293_tick_body_hoare` 的程序精确为 `sseq (V293_tick_body ...) sret`：原赋值、真实 `scall hook []`、原完整后缀与 void return。它明确列出 hook 的 Spec、合法有限未挂起链、环境绑定、ISRclear、栈顶及 frame 等条件。
4. `V293_tick_body_return` 只接受 `None`，拒绝任意 `Some v`。这不仅是返回类型的文字声明，另有 Coq 拒绝定理与同一状态负控。
5. `V293_tick_body_return_to_caller` 以完整 None 返回断言为前提，调用第172步真实 `sret/free` 语义。两个 local 各4字节全部消失，caller 环境与剩余资源恢复；空字节绑定只在蕴含 `Aemp` 时剥离，资源环境运输仍要求 GoodFun。

## 独立实例与同端点消融

探针：[V293TimeTickBodyHoareProbe.v](probes/V293TimeTickBodyHoareProbe.v)。协议在证明前冻结，见 [protocol.json](logs/stage173-tick-body-hoare/protocol.json)。

| 检查 | 证据及严格边界 |
| --- | --- |
| 实际分配后的完整入口非空 | `BHallocated_entry` 从原 caller 资源和两次真实分配构造完整入口；saved、scan 均为 `Vundef`，不预先假设 saved 为0 |
| 原调用确实到达该入口 | `BHallocated_prefix` 执行 call、函数查找、两 local 分配与分配结束，到达精确 body 与 callee 环境 |
| 初始化前单因素负控 | 固定同一实际分配内存 Mi、环境、抽象状态与其他资源，完整 saved=`Vundef` 入口成立，只把 saved 见证改为0则拒绝 |
| 真正赋值与初始化后单因素负控 | `BHinitialize_execution` 通过原赋值产生 Ms，完整 saved=0 入口成立；固定同一 Ms，只改 saved 见证为 `Vundef` 则拒绝 |
| 两段 prefix 真正组合 | `BHsame_initialization_controls` 用语义传递组合 call→两分配→赋值→hook 调用点，保留 canary90=99 与原 caller 槽70；不是只并列两段存在性结论 |
| 原完整 body 逻辑实例 | `BHrules` 实例化正式 `InfRules`，`BHsemantics` 导出 `RuleSem`；仍以真实 hook 的 Spec 为条件 |
| void 返回 post 独立非空 | `BHstopped_return_fixture` 对 `run<256` 且 `run<>1` 构造完整 None post；固定同一状态仅把 None 改成 Some0 即拒绝 |
| 真实释放连接 | `BHreturn_releases_locals` 将完整 body 返回断言接入正式实际释放接口；前提仍是给定该 post |
| 不伪造 hook 实现 | `BHmissing_hook_still_blocked` 保留固定程序缺失 hook body 时无下一步的结论，不能从 Spec 推出真实返回 |

**不要混同三类证据。** 实际调用前缀现在已经真正连接到赋值后 hook 调用点；条件 body 逻辑证明覆盖原完整 AST；停机返回 fixture 则独立指定 ghost `END`，没有执行 clock++ 或缺失的 hook。它只证明完整返回 post 非空与尾部可用。运行分支的完整 post 独立非空实例本步未建立。三者不能拼成未证明的完整 tick 执行 trace。

## 验收与保留的失败

- 稳定生产 `body07`、探针 `probe09` 源快照与编译结果见 [stable-compiles.json](logs/stage173-tick-body-hoare/stable-compiles.json)。共16次编译、12次非零诊断全部保留，见 [compile-summary.json](logs/stage173-tick-body-hoare/compile-summary.json)；这些开发诊断不是语义消融。
- 20个新根的假设检查与两个新入口及其递归依赖的 `coqchk` 结果见 [trust.json](logs/stage173-tick-body-hoare/trust.json)。检查期间561份 Coq 输入保持不变；这是本步入口的递归检查，不是此前全部入口重检。允许假设集合未扩大；本步实际依赖经典逻辑、函数外延性及既有 Eqdep。
- 新增5项结构回归通过；全套由2023项增至2028项，仍为旧423失败／1错误，完整失败／错误 ID 与本轮基线及第172步完全相同。结构回归不能替代 Coq 语义证明。
- 构建、清理后构建、project audit 通过。`make audit` 仍因旧 coverage input identity 退出2；`git diff --check` 仍报告旧 inferules 第581–586行六处 whitespace。不修改旧失败刷绿。
- 逐条反向审查见 [adversarial-review.json](logs/stage173-tick-body-hoare/adversarial-review.json)。最终旧文件核对、测试、清理与判定见 [verification.json](logs/stage173-tick-body-hoare/verification.json)。所有失败快照、日志、协议、源文件与可复用 Coq 产品保留。

## 下一步与总目标

当前 body 入口固定 scan=`Vundef`，但框架 `buildp` 对每个 local 的 raw 值做存在量化，`BuildRetI` 也要求精确的函数级资源组织。**raw local 可以表示 `Vundef`，问题是当前接口尚未覆盖 builder 的任意初始 scan 见证，而非 builder 无法表达未初始化值。** 下一步应沿已有支持任意 scan 的第169步接口，补足 caller／hook frame 与 body 的参数化连接，再核对 builder 前后条件；不能把当前具体可满足入口冒充所有 builder 前置条件。

同时，CPU hook 真实实现保持／返回、生产 ISR 安装、初始化／WFIFun／最终源码级 `GOOD_OS` 和同程序 K1–K4 仍未闭合。边界保持 IE=false／ISRclear、合法有限未挂起链及既有 LocalInv。六阶段覆盖仍为 `94/1/1/1/1/0`，本步不授予整函数覆盖信用。

第一阶段未完成，uCOS3 未开始，总目标保持 active；不提交／推送。先完成 uC/OS-II 最终证明，再按老师附件进入 uCOS3，不以局部模型成果宣称整核验证。
