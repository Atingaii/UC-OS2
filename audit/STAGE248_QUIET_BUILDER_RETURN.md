# 第248步：实际中断入口的非调度完整返回

## 本步补了什么

稳定接口为 `V293_interrupt_quiet_builder_continuous`，生产文件是
`certiucos/v293/proofs/V293InterruptQuietBuilder.v`。它从真实 `BuildintPre`
生成的入口出发，连接同一 bound LocalInv、原 ready/TCB/storage Inv 和原
动态 Enter/Exit/Sched 候选规格下的真实 `EOI; OSIntEnter; OSIntExit; exint`。
第238步已有入口到 Enter 的连接，本步不把它重复计入新成果。

入口是 `pre //\\ filter`：普通合取表示在**同一个状态、同一个堆**上观察
running、nesting、lock 三个既有字节，不再外加 ready/TCB snapshot，也不
通过分离合取复制三个字节。`V293_irq_quiet_builder_open` 先打开 builder，
再用实际 load 的唯一性确定过滤条件中的值就是 builder 中的值。

过滤条件为三个字节都小于256，且 `run=1 -> 1<=nest \/ 0<locked`。
它限制本次返回不进入调度路径，不能删掉后仍声称覆盖全部入口。

## 为什么255不应被排除

旧连续证明为了让计数恢复原值，要求有递增空间。本步去掉这项限制，
但**不把准确后值弱化成“任意字节”**：

| 进入前 running/nesting/lock | Enter后 nesting | Exit后 nesting | 本步结论 |
| --- | --- | --- | --- |
| 1 / 1 / 0 | 2 | 1 | typed 非空入口及完整 wrapper |
| 1 / 255 / 0 | 255 | 254 | typed 非空入口及完整 wrapper；不声称恢复255 |
| 1 / 0 / 0 | 1 | 0并进入调度分支 | 被 quiet 过滤拒绝，不冒充已证明 |

`V293_interrupt_bound_quiet_exit_depth` 在原 BDspec 中直接证明实际调用，
后置保留计算出的精确 nesting，running 的只读两半在返回前重组。
`V293_interrupt_bound_quiet_snapshot_depth` 由实际规则依次连接四段，
用后值的范围证明关闭原 Inv，而不是把后值改写成原值。

## 非空见证与单因素检查

`audit/probes/V293InterruptQuietBuilderProbe.v` 只作为独立检查，不被生产导入。
它把当前版本已有 typed ready/TCB/storage 物理布局参数化为 nesting；
没有搬用历史内核证明。

- `QJfiltered_nonempty`：所有1至255的 nesting 都有 full-memory/frame 分解，
  同一个片段同时满足 bound snapshot 和带过滤的真实 builder。
- `QJactual_wrapper`：实例化原 BDspec、RDinv、LDli 的完整 wrapper。
- `QJtyped_pair`：分别实例化1和255；running、lock、全局/局部环境、抽象状态及代码/规格不变。
- `QJonly_nesting_changes`：两份完整内存除 `(96,0)` 外每个地址的读取相同，
  不只是其它 block 相同；`QJliteral_nesting_load` 检查该字节的实际 load。
- `QJdispatch_filter_rejected`：1/0/0与过滤条件不能同时成立，避免把过滤器说成全入口。
- `QJsaturated_return_literal` 和 `QJsaturated_return_nonempty`：深度254的
  返回资源可以关闭原 `BuildintRet`，且有独立 typed 非空见证。

入口/返回资源分别构造不是两次 C 执行，也不是从启动状态到达255的证明。
真实函数体的连续连接由 Hoare 定理给出；独立返回资源见证只排除后置为空。

## 审查边界

- 仍是 `spec_done None` 的非调度中断规格，没有把 quiet 与 changed/same
  的 `sched;;done` 合并，更没有用任选规格绕开分支不匹配。
- 沿用原 all-clear ISR 返回边界和 `gettopis<=INUM` 条件；不是一般嵌套 ISR 的完整证明。
- 不是 `WFInt`，不是初始化可达，不是新的内核漏洞，也不是 `GOOD_OS`。
- 第246/247步的当前优先级关联问题仍存在，本步没有修好全局不变量。
- K1–K4 未闭合，uCOS3 未开始；仅两个阶段依次全部完成才是最终停止目标。

## 复现与结果定位

本步生产模块已追加到 `_CoqProject`，正常构建会包含它。没有改固定
C/config/AST/framework、旧 Inv/LI/BDspec，也没有改旧测试或冻结证据。
旧源码定位证据的输入 hash 仍一致，见 `source-identity.json`；本轮没有重新
执行预处理，因此不把输入复核说成重新生成源码翻译证据。

证据目录为 `audit/logs/stage248-quiet-builder-return/`：
`protocol.json` 在实现前固定；编译失败及源码快照全部保留；
`stable-compiles.json` 指向最终通过的编译；`trust.json` 检查全部新根及递归依赖；
`full-tests.json`、各命令日志及 `verification.json` 是本步实际结果。

历史基线是旧423失败、1错误，且 make audit 与 whitespace 已失败。
本轮注册生产模块会改变 `_CoqProject` 身份；部分旧测试冻结了它，
可能新增身份失败。不能为了维持旧失败数而不注册模块、更新旧证据、
删测试或改通过门槛。实际新增/消失的失败清单单独记录，不宣称全仓全绿。

## 下一步

本接口解决 quiet 分支从 builder 出发的连接和255边界，但不能单靠它
关闭 WFInt。后续须处理调度分支所需关联在真实入口上的来源，以及三种
路径的统一抽象规格；第247步已排除了简单的全程当前优先级等式方案。
在可检查的新不变量/边界方案形成前，不将已有强入口证明重命名为全入口证明。

## 本轮实测

- 新9项生产根和18项独立检查根，共27项；Print Assumptions 和递归 coqchk 均通过。
  仅沿用框架既有 classic / functional_extensionality_dep，没有新增逻辑假设。
- 正常构建、project audit、5项新增测试通过。
- 完整2404项测试：425失败、1错误。旧423失败和1错误保留，旧失败相对顺序不变。
- 新增两项分别属于第246/247步的源身份测试，均停在旧 `_CoqProject` hash断言处；
  详见 test-delta.json 和 new-failure-details.log。没有绕过断言重跑，
  **不声称早退后的检查本轮均已执行通过**。
- make audit 仍在 stale function evidence input identity 处失败；
  git diff --check 的旧六行空白失败未改变。六门覆盖仍为94/1/1/1/1/0。

以上是局部检查点通过，不是全仓通过。没有改旧失败、测试或冻结证据，
没有提交/推送，也没有开始 uCOS3。
