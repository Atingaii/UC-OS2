# 第331步：真实切换堆上的倒计时资源闭包

## 解决的问题

第328步给出了原始客户端经延时调用、调度调用而切换至新任务的实际全局前缀。第330步仅证明旧任务在资源满足时的两层返回后缀，并未证明旧任务已被唤醒。不能把返回后缀当作唤醒可达性。

本步先补较小且必要的资源接缝：从第328步切换末端的同一总堆，构造旧任务的延时字段 `3 → 2 → 1` 两次写入，并重装同一个 `V293_ready_full`，不凭空加入扫描器或链表资源。

## 稳定接口与证据

- 生产文件：`certiucos/v293/proofs/V293SwitchedCountdownClosure.v`。
- 公共接口 `V293_ready_countdown_store`：输入完整记录/位图/优先级表所有权、抽象槽与任务查找事实、`2 ≤ d ≤ Int.max_unsigned`；输出实际成功的 `store`、原 `tick_wait_step` 的抽象迁移、同一个完整就绪资源和精确4字节之外的内存不变性。不以成功写入、执行或模拟关系为输入。
- 实例：`audit/probes/V293SwitchedCountdownClosureProbe.v`；`SCtwo_countdowns` 对任意初始IE和调度计数器，先复用 `DGglobal_switch` 原全局执行，再在其输出堆依次构造两个写入。不是独立重造的倒计时fixture。
- 旧任务最终仍是 `wait os_stat_time 1`，当前物理指针与抽象curtid仍为新任务；完整ready关系、其他记录及原frame都保留。`SCobserved` 可观察原计数器、guards、canary等frame字段。缓存仍为4，而调度high为6；没有缓存同步结论。
- 固定源码重放同时记录 `OSTimeDly`、`OS_Sched`、`OS_SchedNew`、`OSTimeTick` 的配置后身份。它只约束源码来源，不把两个store提升成完整tick函数的执行。

## 事前单因素消融

协议 `audit/logs/stage331-switched-countdown-closure/protocol.json` 在实现前冻结。保持原全局前缀、同一切换堆、同一 `3 → 2` 物理写入以及全部其他资源不变，只中和抽象任务表的提交。

`SCcommit_ablation` 在同一个更新堆上证明：提交后的任务表满足物理记录关系；保留延时3的旧任务表则不满足。拒绝来自已经写入2的延时字段，与其他门无关。这是晚对应关系门的片段消融，不是突变ISR的执行或整个程序的K1–K4。

## 严格边界

**本步不是实际tick AST执行，不是合法ISR入口或扫描循环，也不是到期唤醒、旧任务重新调度或全局返回。** `store` 与抽象一步是分别证明的资源闭包，尚没有把它们接成原C小步轨迹。没有暗中添加TCB Next字段、扫描器局部变量或中断上下文；这些资源仍需从真实上层入口取得。

下一步要解决合法扫描/ISR资源如何连接到同一可达堆，再处理 `1 → 0` 时的就绪位更新和重新调度。完整API闭包、统一WFInt、初始化、全局ProgSim、最终GOOD_OS、同程序K1–K4仍未完成；uCOS3须在阶段一完成后再开展。总目标保持active。

## 验证与历史失败

本步的独立编译、递归coqchk、逐根假设、注册工程增量构建（不是清理后全新重编）、新增8项测试与两轮全量结果均由本步日志记录，汇总见 `audit/logs/stage331-switched-countdown-closure/verification.json`。局部证明通过不等于全量通过。

旧测试与冻结证据不改写。追加生产文件可能使旧的严格 `_CoqProject` 快照测试新增失败；必须据实保留，无新增失败门不得用豁免制造通过。总体审计的旧源码证据身份问题以及旧inferules的空白问题也不改写。未执行Git提交或推送。

### 本次实测结果

- 10根递归内核复核通过；887个Coq输入在复核期间保持。假设范围不超出既有经典逻辑和依赖函数外延。
- 两轮新增测试各8项通过；注册工程增量构建和project-audit通过，不宣称全新重编。
- 两轮全量各2900项、441失败、1错误。相对第330步新增的失败是 `test_time_delay_nested_return.TimeDelayNestedReturnTests.test_history_and_bounded_completion`：旧测试要求_CoqProject严格等于当时快照，本步新增生产注册使其失败。旧440失败和1错误的身份、顺序完整保持。
- 因此 `local_proof_checkpoint_passed=true`，但 `full_regression_delta_gate_passed=false`、`local_checkpoint_passed=false`、`full_target_complete=false`。没有删除测试或改变通过门槛。
- make audit仍因旧函数证据身份过期失败；git diff --check仍为原6处inferules空白问题。
- 清理前逐项审查并删除10个一次性信任驱动/对象/备份及2个一次性生成脚本；恢复4份原缓存，306个既有pyc、旧源码/测试/冻结证据和本步失败日志保留。可复用生产/probe对象保留。
