# 第348步：从真实函数调用入口连接共享就绪资源

## 本步解决什么

第347步从“九个局部对象已经分配、CPU_SR已经初始化”处开始。本步复用原分配前奏，把稳定接口前移至真正的 `sfexec OS_TCBInit` 入口：七个实参值已经求出，但内存中尚无这些局部对象。由原语义构造分配、参数写入、CPU_SR初始赋值，再连续执行原初始化／发布／返回，并接原抽象创建步骤。

接口：`certiucos/v293/proofs/V293CallReadyCommit.v` 的 `V293_OS_TCBInit_call_shared_return_under_hooks`。

| 顺序 | 输入和输出 |
| --- | --- |
| 调用入口 | 调用者环境、旧任务记录和原物理字段；不要求九个局部对象的所有权或已初始化CPU_SR |
| 分配 | 复用 `V293_tcb_call_prologue_records`，构造实际中间内存Mi并保留全部旧任务记录 |
| 初始化／返回 | Mi直接满足第347步接口；不额外假设这段执行，也不自行拼另一返回堆 |
| 创建／就绪 | 在实际同一个Mf上保留原shared_ready_records与ready_core，以及真实hpcrt_step和参数readback |

抽象客户端内存 `clientM` 和内核内存 `Mf` 仍是不同状态分量。当前线程/spec_crt、完整优先级表、位图关系、新鲜任务、两个CPU hook契约等原前提保持不变。九个局部块仍须互异且相对入口内存新鲜；本步没有把这些选择前提也消除。

## 为什么没有把hook改成空函数

固定源码配置保留CPU hooks，源码树只有它们的声明，没有实现。分析头不是运行端口；不能从“应用hooks关闭”推出“CPU hooks无作用”。本步不编造空实现，不把缺失的sfexec变成框架原语。源码、配置、ADR0005及手工映射的非验证前端边界不变。

## 事前单因素对照

方案在代码之前冻结于 `audit/logs/stage348-call-ready-commit/protocol.json`。

复用原非空旧任务的字节级入口，不复制大段物理fixture。正向程序有OS_TCBInit函数体，真实分配与前缀到达首个CPU hook；负向仅删除该函数绑定，其他函数、物理内存、实参、继续体和中断状态不变，既没有第一步，也不能到达返回。另证九个局部块在该初始内存确实不存在。

该对照只检查函数入口机制。负向在入口就停止，不能证明下游hook、发布或抽象创建正确；正向前缀不等于完整条件接口的闭合实例。**没有构造满足两个hook契约的完整启动实例。**

## 距离最终目标还有什么

本步不是整个OSTaskCreate的TaskSim／ProgSim，也不是冷启动OSInit或具体GOOD_OS。它不覆盖实参表达式求值及调用者前后续控制；仍要求已有当前线程/spec_crt。没有额外宣称完整链表不变量、当前任务属于任务表、当前任务ready或完整初始化可达性。九局部释放发生在复用的执行证明中，但本接口未额外导出独立free字节结论。

真实CPU hook、调用者模拟、冷启动bootstrap、完整初始化链、真实ISR的未过滤WFInt、同程序K1–K4和uCOS3仍未完成。总目标active，不登记full_target_linked。

## 复查

`PYTHONDONTWRITEBYTECODE=1 python3 -B -m unittest discover -s tests -p test_call_ready_commit.py -v`

实测日志、重复编译源码快照、逐根假设、递归coqchk及两轮全量回归位于 `audit/logs/stage348-call-ready-commit/`，最终汇总 `verification.json`。旧失败不改写、不豁免；未提交或推送。
