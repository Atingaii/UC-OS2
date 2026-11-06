# 第204步：中断退出调用闭合与精确剩余证明义务

## 为什么做这一步

第203步只闭合了 OSIntEnter、OS_SchedNew 的共同内部环境。原 OSIntExit 调用临界端口及 OSIntCtxSw；这些端口只有声明，没有可装入 P 的函数体。只给调用规格不能满足 WFFunEnv 的真实函数定义要求。

本步继续沿用 ADR-0005、ADR-0010 已接受的源码级抽象：临界调用解释为 encrit/excrit；切换调用点解释为当前优先级缓存赋值加原框架 switch。没有新增端口函数体，没有修改 C、原 AST、框架或旧证明，也没有声称原端口 refinement。

## 本步实际建立的东西

- `certiucos/v293/proofs/V293InterruptExitEnvironment.v`：三个内部函数在同一 P/Spec 中的真实定义、域匹配、语法条件。对归一化退出函数静态枚举所有直接调用，证明每个 callee 在同一 P 有函数体。
- `V293_exit_env_remaining_body`：**WFFunEnv 当且仅当归一化退出函数对所有真实 BuildPreI/BuildRetI 输入的本体 InfRules 成立**。反向中已把进入函数与调度函数的原参数化本体定理在新的 P/Spec 下重新构造，不把旧单例环境直接搬过来。
- 这是一条剩余义务提取定理，**没有证明等价式右侧，也没有证明三函数 WFFunEnv/WFIFun**。通用退出规格 xp/xq 没有可实现性承诺；具体旧 UIfp/UIfq 也尚未证明适用于新的调度规格和原始 switch 规则。
- `audit/probes/V293InterruptExitEnvironmentProbe.v`：数值实例有实际的 exit300/enter301/sched200 三个不同定义；原退出体调用序列为 `[201,200,203,202]`，仅临界归一化后为 `[200,203]`，完整归一化后为 `[200]`。
- 归一化前后保留真实函数参数和 saved 局部声明，实际 builder 与原 BLprogram 的 builder 相等。复用原非空 UIfp/UIpre 资源，给出 run/nesting/lock 范围内的非空状态；不是 Afalse 前置。这只排除前置空洞，不建立初始化或可达性。

本实例使用原 `V293_witness_li`；**没有**把上一轮 name-only 时间不变量推广为生产任务不变量，也没有声称把三时间 API 与退出函数一起闭合。

## 前瞻单因素对照

协议在改源码前冻结，见 `audit/logs/stage204-interrupt-exit-environment/protocol.json`。

| 唯一变化 | 保持项 | 实测／证明的边界 |
| --- | --- | --- |
| 仅不做切换调用点映射 | 临界映射、三个定义的域、Spec、其余函数、函数声明和局部 | 域仍匹配；203 没有函数体，静态调用闭合被拒绝 |
| 仅删除调度函数200 | 退出体、进入函数、Spec、其余 lookup | 静态调用闭合被拒绝，WFFunEnv 在域边界被拒绝 |

对照检查的是静态链接义务，不是执行消融；不能从提前拒绝推断切换、释放、返回或下游资源规则已正确。

## 对抗性核查与限制

1. “有规格却没有函数体”：逐个检查实际 callee 的 P lookup，不能用 EqDom 代替调用图检查。
2. “前置根本不可能满足”：保持原真实 builder，给出独立非空堆见证；没有代替所有状态的本体证明。
3. “把退出体正确性藏在假设”：接口明确为 iff，右侧完整列出真实 builder→InfRules，状态仍为开放。
4. “归一化等于原端口执行”：仅沿用已接受抽象，不作该推论。
5. “更多 Coq 文件等于覆盖提高”：六门仍为 `94/1/1/1/1/0`，不提升 full_target_linked。

编译快照含失败尝试；最终采用 body03/probe06。对 probe 的旧大段依赖 import 作删除消融，缺失的必要名字按编译错误精确补回，其余不保留。逐根假设、递归 coqchk、全量测试、旧文件身份、清理结果的实测数据以同目录 `verification.json` 为准，不把已有审计失败改成通过。

## 下一步的实质义务

直接针对归一化退出本体建立资源化 Hoare 定理，尤其是临界区取得/释放、共享 ready/task 资源与调度规格的兼容，以及 switch 后目标任务 LocalInv 的交接；再消去本步 iff 的右侧。只证明更多静态调用或存在性 trace 不会完成这一步。

之后仍需生产 ISR/WFInt、完整任务不变量、初始化、同一程序源码级 GOOD_OS 与 K1–K4；再按老师要求推进 uCOS3。当前总目标保持 active，未提交、未推送。
