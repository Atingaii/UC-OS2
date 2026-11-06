# 第282步：helper 调用前缀覆盖所有合法局部分配

## 目标与本轮结果

最终目标仍是固定 uC/OS-II V2.93.01 的整核源码级 GOOD_OS 与同程序 K1–K4，完成后再开始 uCOS3。本步没有降低验收目标。

本步将真实 `OS_SchedNew()` 的四步调用前缀连接到原框架 TaskSim：

1. `scall` 进入无参调用准备；
2. `sfexec` 保存调用者环境、清空被调用者局部环境；
3. 分配 `INT8U y`，取得新块上的原始 `Vundef` 所有权；
4. 进入原来的 helper 函数体。

生产接口 `V293_sched_helper_call_TaskSim` **是条件接口**：要求对每个 `fresh M b`，证明分配后原函数体的 TaskSim。它不是完整 helper 的资源闭合接口，也没有接通第281步的目标赋值切点。局部所有权与 CurLINV 由前置资源构造；函数体模拟没有被伪装成已证明的结论。

文件：`certiucos/v293/proofs/V293SchedHelperTaskSim.v`，已登记 `_CoqProject`；独立控制 `audit/probes/V293SchedHelperAllocationProbe.v` 不登记生产工程。检查结果见 `audit/logs/stage282-helper-allocation/verification.json`。

## 为什么需要全后继桥

原来的固定后继桥要求任意 frame 上只有同一个局部后继，适用于已构造的 store 或纯步骤，不能直接用于非确定性分配。

新内部桥 `V293_branching_cstep_TaskSim` 对所有任务拥有堆上的真实后继量化。从实际总堆步骤，经框架 `cstep_frame` 分离共享与外部 frame，得到该次实际选择的局部后继，再使用对应的 CurLINV 和 TaskSim。无步进中止义务在任意兼容总堆上另行构造进展，不能拿某次局部选址强行扩展到所有 frame。

公开调用接口内部实际构造全部进展步骤，没有把 `cstep`、整条 trace、唯一后继或任意 frame 的进展作为公开前提。仍保留的函数体 TaskSim 是明确的继续义务，不是资源闭合证明。

## 单因素控制与边界

- `HAtwo_real_successors`：同一任意初始堆、同一程序/环境/代码，有两个合法 fresh 块、两个真实分配步骤，后继不同；包含空堆实例。
- `HAno_fixed_successor`：把“所有合法后继”中和为“固定同一后继”的连接方式在该真实步骤上不成立。这是连接机制的必要性反例，不是完整入口执行消融。
- `HAframe_excludes_old_choice`：只占用原 fresh 块后，旧选址不再 fresh，但仍存在别的合法选址；程序和分配大小不变。
- `HAhelper_real_prefix`：固定原 helper 函数绑定，任意合法选址都能实际到达原函数体，未插入初始化 store。

这些结论验证分配与调用前缀，不提供整条原活跃调用的非空 TaskSim 见证，也不证明后续两个赋值、释放和返回。没有用预先选定的一条 trace 代替对所有真实执行步骤的要求。

## 不变项与未闭合项

C、配置、AST、框架、ADR-0010 和第281步及以前的证明/冻结日志不变。调用前缀沿用 `ie=false`、`si=nil`、空局部候选 `V293_shared_li`，没有新增任意中断交错结论。

**不是完整调用入口 TaskSim；GOOD_OS 未闭合，同程序 K1–K4 未闭合，uCOS3 未开始。** helper 函数体、资源释放/返回、外层 guard、等优先级分支返回、初始化与 WFInt/WFIFun 等整核连接义务仍在。旧测试失败、已有审计失败及历史空白错误不删除、不改写。

下一步：对任意 fresh `y` 从所有权证明两个真实字节赋值的 TaskSim，连接 `sret`、字节释放、调用者环境恢复，再调用第281步目标赋值接口，消去本步的函数体 TaskSim 前提。
