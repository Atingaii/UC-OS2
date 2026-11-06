# 第294步：最高优先级仍是当前任务时的完整客户端调用

## 本步解决什么

第293步证明的是从 helper 调用切点到返回。本步把它接到两层相同的客户端 `scall f nil`，不让调用者提供执行成功、内存写入成功或下游 `TaskSim` 结论。

唯一公开接口是 `V293_exit_equal_client_call_TaskSim`。三个辅助 Lemma 分别连接临界段与 guard、函数体和分配入口；直接复用既有 active resource、frame、分配与客户端桥接引理，不再定义一份资源模型。

## 精确前置与路径

- 固定 V2.93.01 源码、配置和既有 boundary AST；C、框架与中断切换边界未变。
- running=1，nesting 为 0 或 1，lock=0；当前任务在抽象任务表中，并且仍是最高优先级就绪任务。
- IE=false、si=nil、ISR 标记全清，空 LINV；临界栈 ci 可任意。它不是任意中断环境下的证明。
- 显式绑定真实外层函数与真实 helper，以及分支专用的高层 `END None` API。名字不别名及 global binding 前提保留。

证明依次构造：客户端调用与 API 入口 → 任意 fresh saved 分配 → saved 初始化 → running true → encrit → 饱和递减 nesting → nesting/lock 双 guard → 真实 helper 的任意 fresh 局部分配/执行/返回 → target 指针写入 → 推导 high=current，取不切换分支 → excrit → free → 返回调用者。

后置是原 storage 家族的 `RDYINV G t ** LINV ...`，不是 Post=True，也不是返回所有单元旧值：nesting 可以递减，high/target 可以更新。当前任务不切换；本步没有新增“计数器数值保持”等强于后置的单独定理。

## 非空实例与前瞻单因素对照

`audit/probes/V293ExitEqualCallTaskSimProbe.v` 独立定义 ECcells、ECdecoder、ECmemory 和 ECresource，不把旧 ACmemory 或 helper 切点堆当成本步实例。堆包含真实任务记录、ready bitmap、priority table、完整 256 字节 decoder、running/nesting/lock、current/high/target/counter；无预分配 saved。current=4 与就绪任务记录一致，old high=88、old target 指向另一等待任务。ECbase 构造空间断言，ECnonempty_client_call 对全部 n<=1 和 ip 实例化公开定理。

在编写新证明前，protocol.json 冻结了入口对照：仅移除 f 的抽象 API binding，client code、concrete program、heap、ISR specification、scheduler 和其他 API 项不变。ECbinding_single_factor 核对差异；ECabstract_entry 给出有绑定时的高层 sfexec 步；ECmissing_binding_no_high_step 排除无绑定时任何高层下一步；ECclient_step_unchanged 与 ECactual_client_low_step 保留具体调用步骤。

这是局部入口对照，不是完整调用执行消融，不证明 helper、guard 或所有下游机制分别必要。它也不靠更早的拒绝来宣称整条执行链获得验证。

## 验证、旧失败与证据

详见 `audit/logs/stage294-exit-equal-call/`：前瞻 protocol、旧文件基线、每次成功/失败源码快照、重复编译、逐根假设、递归 coqchk、build、全库测试与旧失败身份差分，以及只读 checkpoint。

第一次 production 编译在同 Section 引理应用处错误指定已固定的 nc；第一次 probe 编译缺 list_scope。两次失败快照原样保留；只修正证明应用与 notation scope，不改变目标或 gate。最终实测以 verification.json 为准；全库旧失败保留，make audit 及旧 whitespace 问题不因本步而被标成通过。

清理只针对本步一次性 Trust 六项与两份缓存备份；先核对每项身份再删除。原 lia/nia 缓存恢复到基线字节，既有 pyc 保留；源文件、依赖和验证证据保留。没有 commit/push。

## 仍不等于什么

- 是完整调用的一个分支，不是统一 OSIntExit 规格；尚未消费抽象 sched no-op。
- 强 current guard 缺口仍保留，不把 END None 分支等同于完成该缺口。
- 未闭合 WFIFun/WFInt、整个 GOOD_OS 或同程序 K1–K4；uCOS3 未开始。目标继续 active。
- 下一步需要在统一抽象规格与统一资源接口下汇合这些分支，而不是把多个分支专用 API 绑定直接并列当作一个完整规格。

## 下一步的最小连接点

已有 `V293InterruptCommonDispatch.V293_same_schedule_reduce` 在 IRQ snapshot 的 InfRules 层消费同任务调度，但它的资源和层次不是本步 ready-storage TaskSim 接口，不能直接拿它当作已连接证明。下一步先在同一现有资源上证明抽象 `sched` 选择当前任务时的真实高层步骤，再连接本步 END None 残余；确认无需新资源模型后，才汇合需要切换与不切换分支。quiet/nested/locked 分支是否应消费调度仍取决于统一规格的准确条件，不能无条件添加 sched。

## 最终实测

| 检查 | 结果 |
| --- | --- |
| 生产与探针同 SHA 串行重复编译 | 各两次通过 |
| 全部新证明根 | 13 根，逐根假设仅 classic / functional_extensionality_dep |
| 递归 coqchk | exit=0，约 539.54 秒 |
| 项目 build / project-audit | 通过；活动 V293 文件 368 个 |
| 新增测试 | 5 / 5 通过 |
| 全库测试 | 2636 项；434 failure、1 error，与上一步身份及顺序完全一致，无新增 |
| make audit | 仍因旧 function evidence input identity 过期而失败 |
| git diff --check | 仍有旧 framework/inferules.v 空白问题；本步新交付文件单独检查通过 |

旧检查点在新增 _CoqProject 条目处准确拒绝新树，原脚本与旧封存未改写。它之前在 Coq 运行期间触发进程 guard 的失败尝试也保留，不将该失败误记作项目扩展的证据。
