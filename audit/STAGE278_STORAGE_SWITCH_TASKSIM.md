# 第278步：原旧任务切出点的弱 storage TaskSim

## 这一步真正连接了什么

第276步已从原完整活跃调用到达的旧任务切出堆，在同一共享子堆建立 `SWINVt / SWPRE_NDEAD`；第277步补齐弱 storage 的 pending 返回。现在把二者接到**原框架 TaskSim 的 switch 义务**，不再要求上层先提供一个恢复 TaskSim。

生产公开接口：`V293_storage_switch_TaskSim`，位于 `certiucos/v293/proofs/V293StorageSwitchTaskSim.v`。它只接收固定调度器、真实函数绑定、有限 SKIP caller，以及：

`saved ** (SWINVt G old //\\ SWPRE_NDEAD scheduler target old)`。

括号中的两个断言作用于**同一个**共享堆/抽象状态，不允许借 task-private saved 或外部 frame 补足 SWPRE。公开前提没有 TaskSim、ProgSim、执行轨迹或 free 结果；结论使用原 `TaskSim`，不是新定义的弱化模拟。

## switch 与恢复时的资源分区

| 时点 | 旧任务保留 | 交出/归还的共享资源 | 外部 frame |
| --- | --- | --- | --- |
| 实际切出点 | saved(bs) 私有 | 同一 Mc/Oc 上的 SWINVt 与 SWPRE_NDEAD | saved98 与 RCframe 外部 |
| switch 义务 | 固定 Ml/Ol，真实 saved 所有权 | 交出 Mc/Oc | 不并入任务或共享资源 |
| 恢复 callback | 同一个 Ml/Ol | 任意兼容 Mc'/Oc'，满足原 SWINVt | 原 TaskSim 继续量化所有兼容外部 frame |
| 返回 suffix | 只释放旧任务拥有的 saved(bs) | 按保存栈顶重新分配给任务 RDYINV 或共享 INV | 不释放、不借用 |

`V293_storage_resume_callback` 对 Mc'/Oc' 全称量化，不能把“归还原来的堆”写成公开接口限制。它从归还的 SWINVt 提取 ISR 全清及既有 storage core，拼接保留的 saved，然后**只调用一次第277步的通用弱 pending 接口**，处理任意保存栈顶。不重新复制 excrit/sret/free/caller 的两套执行证明。高层 `spec_done` 的匹配复用第275步的真实 done→SKIP 引理。

`V293_storage_switch_TaskSim` 直接构造原 TaskSim 的七类义务。switch 分支交付原资源分区、同共享堆 SWPRE、局部候选以及全称恢复 callback；普通/事件/初始化/释放等不适用分支由原代码形状排除。nil/false 额外共享 INV 的空性复用第277步的一般引理，不暗加 cache 条件。

## 同一真实切出堆的独立核查

- `WSactual_old_switch` 复用原 `OPactual_entry` 完整分配/调用轨迹，到达的仍是 **OwnershipWaiting 旧任务的原 switch**，不是目标任务的返回位置。
- `WSpartition` 在同一个达到堆提取任务堆与外部 frame，调用生产公开接口。saved(bs) 私有，来自本次实际分配；saved98 与 RCframe 外部。
- `WSnonvacuous` 用两次 fresh 分配和既有 `SPph` 的调度器规格构造真实非空见证，不另造程序或初始堆。
- `WSresume` 单独暴露任意兼容共享资源归还的全称结论，前提只有 OPpre，不接收模拟结果。
- `WSresume_concrete` 实例化归还原 Mc/Oc，给出至少一个兼容 callback；这是**条件恢复有实例**，不是全局切回可达性，尤其不证明 blocked 旧任务当前可被调度。
- 同一实际切出堆仍保持 cache=4、旧任务 blocked，以及原强 current guard 拒绝。弱 storage 的局部接口不能冒充最终强 current/cache 不变式。
- 保存栈顶的生产接口是任意 bool；实际原完整入口见证只声称 false。true 支持来自第277步的同一通用返回证明，不冒充本入口 true 可达。
- `WSsaved_necessary/WSreject_missing_saved` 是逻辑必要性/拒绝控制，**不是完整单因素执行消融**。原错误目标拒绝由第276步继续保留；未完成独立非空完整执行反模型，`protocol_fully_completed=false`。

## 与总目标之间仍有的距离

本步是实际切出点的弱 TaskSim，**不是完整调用入口 TaskSim**，也不是 ProgSim/整核证明。仍需把模拟义务沿真实函数的分配、临界区、调度、比较、计数和复制前缀向前连接，并解决最终强 current/cache、初始化、WFInt/WFIFun、任意中断交错和完整共享循环等义务。

固定源码、配置、AST、框架及 ADR-0010 不变；si=nil、ISR 全清、空目标 LINV、有限 SKIP caller 的边界不变。GOOD_OS 未闭合，同程序 K1–K4 未闭合，uCOS3 未开始；总目标保持 active，未提交/推送。

## 证据入口

`audit/logs/stage278-storage-switch-tasksim/` 中保留事先冻结的 protocol、1631项旧输入身份、每次完整源码编译快照、独立 Assumptions/coqchk 日志、回归差分及清理清单。最终实测以 `verification.json` 为准；旧失败和冻结证据不改写。

## 最终实测

| 检查 | 结果 |
| --- | --- |
| 新生产源与独立 probe | 各稳定编译两次通过；首编也通过 |
| 逐根 Assumptions / 递归 coqchk | 10 根全部通过，递归核查约 528 秒；779 项 Coq 输入身份不变，仅沿用既有 classic 与函数外延性 |
| 单线程 make build / project-audit | 通过；352 个活动 V293 文件、103 个框架/策略文件 |
| 新测试 | 5 项全部通过，清理后再次通过 |
| 全量回归 | 2556 项，434 failure / 1 error；旧失败和错误 ID、顺序完全相同，无新增 |
| 初次结构测试 | 1 项字面量转义错误；raw string 修正后 4 项结构测试通过；原失败日志、结果及源码快照保留 |
| make audit / git diff --check | 仍失败：既有 stale function evidence 身份与 inferules 581–586 行空白，不掩盖 |
| 旧材料 | 1631 项输入中仅 README、VERIFICATION_STATUS、工程登记与生成依赖文件变化；旧冻结文件不改写 |
| 清理 | 逐项核对后删除 12 项一次性产物，共 735271 字节；原算术缓存恢复，既有 306 项 Python 字节码身份不变 |

本地检查点通过不等于全仓通过；最终 GOOD_OS、同程序 K1–K4 及后续 uCOS3 仍未完成。下一步沿真实函数前缀向入口推进 TaskSim，不能用存在一条全局 trace 代替全称模拟义务。
