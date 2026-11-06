# 第277步：同一套返回步骤支持弱 storage 与强 current

## 本步回答什么问题

第276步已在旧任务实际切出堆上交付弱 `storageInv` 的 `SWINVt/SWPRE_NDEAD`，但第273—275步的 pending 返回接口固定使用强 `currentInv`。不能把“强接口已证明”误当作弱资源也能调用它，更不能补一个未成立的 cache 假设。本步抽取不变式无关的返回步骤，再实例化既有 storageInv；不另造不变式，不改源码/AST/框架。

稳定接口：

- `V293_invariant_pending_TaskSim`：任意满足明确资源闭合条件的 I/Core。
- `V293_storage_pending_TaskSim`：实例化已有 `V293_ready_storage_inv/core`。

两者都不把 `TaskSim`、执行轨迹或 whole-heap `free` 作为公开前提。内部单步引理当然含后继模拟前提，它们是构造原框架归纳/余归纳义务的证明工具，不是公开入口的循环 oracle。

## 原框架中发生的真实步骤

`SKIP → excrit → SKIP → sret → free(saved) → free(nil) → caller`。

| 保存栈顶 | excrit 后任务所有 | excrit 后共享所有 | 后续步骤 |
| --- | --- | --- | --- |
| false | saved、Core、CurTid | 空 INV | 同一个泛型 suffix |
| true | saved、CurTid | Core 封装为 INV | 同一个泛型 suffix |

`excrit` 不改变总内存或总抽象状态，只改变 IE/保存栈和资源分区。普通 C 步并不需要“共享 INV 为空”：只要保持 IE/中断栈不变并保留兼容的共享资源，就能量化任意共享堆和外部 frame。删除普通 C 步对强 Core/空 INV 的依赖后，两类实例仍可由同一引理核查。真正需要 nil/false INV 为空的是本步 excrit 的所有权交接。

公开泛型接口的逻辑前提为：`I(S INUM)` 是 Aemp、Core 是 GoodInvAsrt、ISR 全清时 Core 能分别封装进 disabled SWINV 和 enabled INV、函数绑定/有限 SKIP caller、任务独占 saved 和 Core/CurTid。返回后仍是精确的 `RDYINV I t ** LINV ... t nil`，不是 Atrue。

## 非空见证及边界

`IWactual_old_cut` 复用第276步原完整调用实际达到的旧任务切出堆；`IWpartition` 从该堆提取任务子堆和任意兼容外部 frame，建立恢复 callback 所需的 pending TaskSim。`IWnonvacuous` 用两次 fresh 分配提供前提见证。

- saved(bs) 私有，确实是旧任务本次分配的保存区。
- 目标 saved98 与 RCframe 外部保留，不能冒充旧任务的 private saved。
- 同一堆支持两个保存栈顶的资源快照控制；false 是实际切出保存值，true **不是原完整入口 true 可达性**。
- 切出点可达，不等于旧任务已经全局切回。这里是在恢复 callback 的代码位置建立模拟见证，不是在全局轨迹中跳过 switch。
- 同一实际堆仍有 cache=4、旧 current=blocked，保留原强 guard 拒绝；弱 storage 后置条件不提升为强 current 后置条件。
- `IWcurrent_compatible` 另用原强 Core 的资源闭合引理实例化同一个泛型接口；因此不是只为某个 fixture 写死弱结论。
- `IWowned_saved_necessary/IWreject_missing_saved` 只证明保存区所有权的逻辑必要性/拒绝控制，**不是完整单因素执行消融**。未完成所有独立非空反模型，`protocol_fully_completed=false` 明确保留，不把早期拒绝冒充下游机制覆盖。

## 本步仍未完成什么

**不是完整入口 TaskSim，也不是整核证明。** 尚需把泛型/弱恢复接口接到原 switch 的全称恢复义务，再向前连接实际函数入口。最终强 current/cache 一致性、WFInt/WFIFun、初始化可达性、任意中断交错、完整共享循环及其余整核义务均未由本步闭合；ADR-0010 不变，空目标 LINV、si=nil、ISR 全清边界不变。GOOD_OS 未闭合，同程序 K1–K4 未闭合，uCOS3 未开始。未提交/推送。

## 可复核材料

目录：`audit/logs/stage277-invariant-pending/`。

`protocol.json` 在新证明前冻结；`baseline.json` 覆盖1626项旧输入。各次编译保存当时的完整源码与日志，包括失败；稳定版各编译两次，逐根 `Print Assumptions` 和递归 `coqchk` 单独记录。`verification.json`、`test-delta.json` 记录实测结果，不把既有测试/审计失败改成通过；`checkpoint.py` 只读复核本步证据与边界。

## 本次实测

| 检查 | 结果 |
| --- | --- |
| 三个新证明文件各重复编译两次 | 全部通过 |
| 逐根 Assumptions 与递归 coqchk | 16 个定理根通过：9 个生产、7 个独立核查；仅沿用原经典逻辑/函数外延性依赖 |
| 串行 build、工程范围审计 | 通过；351 个活动 V293 文件、103 个框架/策略文件 |
| 新增回归 | 5 项通过，清理后复测仍通过 |
| 全量回归 | 2551 项；保留既有 434 failure、1 error，ID 与顺序完全不变 |
| make audit | 原 stale function evidence identity 失败仍在，退出码 2 |
| git diff --check | 原 inferules.v:581–586 空白失败仍在，退出码 2 |
| 清理 | 逐项核对后移除14个一次性文件，共744841字节；既有缓存恢复原字节，正式证明/日志/失败快照及可复用 Coq 产物保留 |

这些结果是局部检查点，不是全仓通过。原276检查点的4项 live 输入因追加工程登记/说明而变化，旧冻结文件未改。
