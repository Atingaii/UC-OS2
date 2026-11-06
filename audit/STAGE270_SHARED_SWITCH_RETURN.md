# 第270步：把共享资源接通到实际切换与目标任务返回

## 前因与本步结果

第269步的端点在 switch 后，已经重新封装共享候选，但尚未接到目标任务已有的 pending 返回。本步复用原生产执行规则，把**切换前的弱 shared-storage 候选 → 真实切换到最高 ready 任务 → 重新封装 current 候选 → 目标 excrit/sret/free/caller**连接起来。

不能直接把269与268拼成完整共享循环：268的环境任务显式切回旧任务，但旧任务在抽象任务表中仍 blocked，不是最高 ready；cache也尚未恢复。新增 `STblocked_old_not_selected` 机器证明这一不适用条件，旧证据不改，环境切回不冒充调度器选择。

## 为什么返回 core，而不是一直返回 SWINV

`excrit` 恢复保存的 IE，合法结果可以是 true。`SWINV` 自带 `IE=false`，所以保持完整 SWINV 的说法会越界。本步没有削弱旧不变式，而是打开它，保留既有 `V293_ready_current_core`、完整 `CurTid` 资源和独立 frame。flags 的纯状态断言不占内存；当前任务指针的两半所有权没有丢弃。

生产文件 `certiucos/v293/proofs/V293OSIntExitSharedReturn.v` 唯一上层接口为 `V293_int_exit_shared_switch_return`：

- 输入是**弱 storage** 共享候选，适用于复制与 switch 之间的暂态；不强求该暂态满足 current guard。
- 保留目标 pending 的精确代码、saved 环境、非空临界栈、函数绑定、共同 si 和最高 ready 条件。
- 由所有权实际构造 store/current 与 free 成功；没有把执行成功、ProgSim 或释放成功当作前提。
- 输出原 `lpstep`、原有限全局执行、共享 core、`CurTid victim`、frame，及当前指针正确、saved 四字节删除、其余地址保持结论。
- 生产接口本身不独立声称缓存一致：current guard 仍包含最高 ready 分支，沿用269的缓存对照结论，重封装不等于 cache 正确。

这是真实有限执行的资源连接，不是 ProgSim 或完整 Inv 保持定理。

## 独立实例与前瞻单因素对照

`audit/probes/V293SharedSwitchReturnProbe.v` 复用267的同一个 `FWtasks/FWos` 程序、入口物理堆和 `FTto_switch`，没有再造只有 skip 的程序。

`STfull_call_shared_return` 从 `sfexec` 和任意给定 fresh saved 分配开始，接通完整活跃调用。全局 target93、high91、nesting96、lock97、cache94、running新鲜块、counter95 保留在共享资源中；旧任务 saved 块仍独占且可读，目标 saved98 真正释放。`STsaved_retained` 另核查旧 saved=0、canary90=99；只读 lookup92 仍在 `RCframe`，**不是任务私有 LINV**，也没有转换成既有 IRQ builder 布局。`STnonvacuous` 构造可满足入口的真实执行，不只给出条件式。

前瞻协议 `audit/logs/stage270-shared-switch-return/protocol.json` 在实现前冻结。`STsaved_top_actual_ablation` 先用实际完整调用到达同一 switch 堆，再只删除目标任务保存栈的第一个 false：

| 固定项/变化项 | 原保存栈 | 只删除目标栈顶 |
| --- | --- | --- |
| 达到的物理堆、任务代码、环境、程序、抽象任务表 | 相同 | 相同 |
| 目标初始 IE / si | false / nil | false / nil |
| 目标保存栈 | false :: true :: vci | true :: vci |
| 实际 switch、excrit、sret、free、caller | 全部执行 | 全部执行 |
| 返回 IE / 保存栈 | false / true :: vci | true / vci |
| 最终完整物理堆、共享 core | 相同 | 相同 |

两条分支都由同一个生产接口构造真实执行。store/free 的确定性证明整个最终物理堆相同；非目标 aux 映射不变。**变体从共同到达的 switch 快照开始**，不声称两个不同保存栈都由同一初始完整调用生成；也不是只改语法后早拒绝的伪消融。blocked 非最高 ready 的证明仅是适用条件检查，与这项实际双执行对照区分。

## 审查与验证

实测见 `audit/logs/stage270-shared-switch-return/verification.json`：稳定重复编译、全部新增根的 Print Assumptions 与递归 coqchk、完整 unittest、构建、审计和清理分别记录。文本结构测试不是 Coq 内核证明。失败编译及输入快照保留，旧失败和旧冻结证据不重写。工程只新增一行生产登记，README/状态仅前插。

## 仍未完成

- 目标 pending 已存在；共同 si 是公开前提，未证明任意任务上下文兼容。
- 原调用者仍挂起；**不是旧任务切出后再调度切回的完整共享循环**。
- typed 初态 high=88，而配置最低优先级12；不是初始化可达证明。
- 沿用 ADR-0005/0010 的显式源码级边界，不是原外部 CPU-port 的细化证明。
- 不是所有 OSIntExit 分支、任意交错、完整中断安装、WFInt/WFIFun、GOOD_OS 或同程序 K1–K4。
- uCOS3 尚未开始；未提交／推送。总目标仍 active。

下一步需在真实 ready/blocked 与缓存转换下接通原任务恢复，把共享 core 与各任务 pending/saved 资源放进统一 Inv/局部不变式义务；不能复用268的环境切回来省掉调度正确性。
