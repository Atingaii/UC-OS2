# 第274步：恢复中断时交还共享资源，再完成 pending 返回

## 要解决的缺口

第273步只处理保存栈顶 `false`。本步新增 `V293EnabledPendingTaskSim.v`，唯一上层接口 `V293_enabled_pending_TaskSim` 从实际任务拥有的 `saved ** (Core ** CurTid)` 开始，证明保存栈顶 `true` 的 pending 返回，接通原 `TaskSim`。公开接口没有 TaskSim、ProgSim、执行或 free 成功前提。

| 时刻 | IE / 保存栈 | 任务拥有 | 共享 INV 拥有 |
| --- | --- | --- | --- |
| pending SKIP 与 excrit 前 | false / true::ci | saved、Core、CurTid | 空物理堆、空抽象资源 |
| excrit 后 | true / ci | saved、CurTid | Core |
| sret、释放 saved 后 | true / ci | CurTid，原 RDYINV 与空 LINV | Core |

**Core 不复制。** excrit 的物理堆与总抽象状态均不变；用真实 `join Mt Ms M` 和 `join Ot Os O` 把 Core 的所有权从任务交给共享侧。高层零步保持总抽象状态，不能借此声称发生了高层调度。

## 实现与验证边界

- `V293_enabled_cstep_TaskSim` 构造原七项义务。每次量化任意兼容共享 INV 与任意可分离外部 frame；先合并共享/外部 frame，再证明真实 cstep、唯一后继及精确释放残余，最后重新分离共享资源。没有固定共享堆为某个实例，也没有假设共享堆为空。
- `V293_enabled_excrit_TaskSim` 仅在退出前利用 false,nil 的空共享结论；退出后显式提供非空 Core 所在的 INV。不是把第273步的空共享论证直接套到 true 分支。
- `V293_enabled_return_suffix` 只需要 saved 与 CurTid，不再要求任务拥有 Core。释放使用原 `free_mono` 与 `join_free`；返回原 caller，端点严格是 `RDYINV ** LINV`，不是 Atrue。
- 初始 SKIP 复用第273步的 false-IE 单步传递，不改旧生产证明与冻结日志。

独立 probe 的 `EPtransfer` 展示真实任务/共享/外部资源分区、保存区可释放及 true 返回后缀 TaskSim。`EPnonvacuous` 复用同一完整调用实际到达的物理堆，并同时构造 false 与 true 的 pending 包。

**必须区分可达性：完整入口轨迹仍只对应原 false 保存栈。** true 包由同一达到堆上的单因素快照控制得到：仅目标保存栈顶 false 改为 true，代码、环境、物理堆、抽象状态、资源分区及外部 frame 不变。没有证明 true 快照从原完整入口可达；不能把两项存在性拼接成一条 true 完整调用轨迹。

## 前瞻消融与反向核查

协议在本步源码编辑前冻结，见 `audit/logs/stage274-enabled-pending-tasksim/protocol.json`。

1. **栈顶单因素控制**：同程序、同堆仅切换保存栈顶，原 excrit 实际后继分别恢复 IE=false/true；两种 pending 包分别由273与274的原 TaskSim 支持。此处是快照/原语控制，不是两条完整入口执行的对照。
2. **所有权分区边界**：相同 whole heap 把全部字节移至外部时，whole-heap free 可成功，但空任务堆 free 失败，也不能满足 owned saved 前提。不是把 whole-heap free 成功当作任务所有权证据；不是两个实际 C 完整执行。
3. **空保存栈边界**：同一 excrit 在空保存栈无原 loststep 后继。
4. **共享资源交接检查**：检查物理及抽象两组精确 join、原 INV 与空目标 LINV，不把旧 saved/RCframe 当作目标任务私有 LINV。
5. **信任边界**：逐根 Print Assumptions 和递归 coqchk；保留所有失败编译快照，不新增证明公理或修改原执行规则。

## 尚未完成

这不是整核证明。仍限 ISR 位全 false、共同 si=nil、空目标局部候选、既有 pending、有限返回 client 家族。原任务仍 blocked；typed high=88 不代表初始化可达；ADR-0010 不变。TaskSim 内部量化共享堆不等于证明任意中断交错下整个内核不变式。

切换前 TaskSim、真实调度切回与共享循环、完整 WFInt/WFIFun、整核 GOOD_OS、同程序 K1–K4 仍未闭合；uCOS3 未开始。没有提交或推送。

实测编译、信任检查、完整测试及旧失败差分记录于本目录日志。最终以 `verification.json` 为准，不沿用旧阶段的通过声明。
