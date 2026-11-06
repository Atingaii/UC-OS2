# 第275步：切换边界的原 TaskSim 与旧任务恢复 callback

## 结论及范围

新增 `V293SwitchReturnTaskSim.v`，唯一供上层使用的接口是
`V293_switch_return_TaskSim`。起点是**已经处在 switch primitive 边界**、
拥有 saved 单元与 `SWINVt //\\ SWPRE_NDEAD` 的任务；不是 OSIntExit 完整入口。
这不是整核证明，也不是已经接通原活跃调用前缀的证明。

固定上游 V2.93.01 提交 `0c4a48e6fbc6e915714e816196619a5481accf0c`、
两类授权修复、函数 AST 和 ADR-0010 抽象切换／中断边界不变。
没有新增内存语义、全局执行规则或候选不变式，没有改原 TaskSim 七项义务。

## 本步真正补上的部分

原 TaskSim 的 switch 义务不是单次全局切换轨迹：它要求保留旧任务的私有状态 `ol`，
交出共享 `Mc / Oc`，并对任意兼容替换 `Mc' / Oc'` 给出旧任务的后续模拟。
本步直接构造这项恢复 callback，而不把它作为定理的前提。

1. `ol` 仅保留保存区与原局部环境；Core 不复制、不冻结在私有状态里。
2. `SWPRE_NDEAD` 与 `SWINVt` 必须在**同一个共享 Mc** 上成立，不能借用 saved 或外部 frame。
3. 恢复时只要求新的共享资源满足原 `SWINVt G t`，且与 `ol / Ol` 可分离组合。
   `Mc'`、`Oc'` 不要求等于切出时的内存或抽象值。
4. 高层起点是真正的 `sched ;; done`；恢复高层是 `done`，不是偷偷改成 `SKIP`。
   `V293_resume_high_done` 使用原 `hapi_step / hapiexit_step` 完成 done 到 SKIP 的真实高层步，
   然后接已有 pending 返回模拟。
5. 保存临界栈顶 true / false 分别接274／273，执行 excrit、sret、真实 free 与原 caller。
   端点 P 仍是精确的 `RDYINV G t ** LINV ... t nil`，不是任意真后置条件。

公开前提不包含 TaskSim、ProgSim、全局执行或 free 成功假设。仍要求 ISR 全清、si=nil、
非空保存临界栈和既有有限 client 家族。环境未归还兼容 SWINVt 时，callback 不适用；
这里没有证明环境最终切回或公平性。

## 独立实例究竟验证了什么

`V293SwitchReturnTaskSimProbe.v`：

- `SPpartition` 从273同一实际达到堆提取 saved 私有区、Core/CurTid 共享区和完整外部 frame；
  以原 `SWINVt` 重封装。没有复用输入 packet 中的旧 TaskSim 证明。
- `SPresume` 对任意新共享堆和抽象状态调用实际恢复 helper，两种保存栈顶均适用。
- `SPnonvacuous` 复用完整入口的实际 false 路径和真实 store/free 见证，证明上述资源前提有实例。
  true 是同一堆上的栈顶快照控制；没有证明 true 快照从原完整入口可达。
- 这些实例的 `t` 是已经选中的 OwnershipReady，不是仍 blocked 的 OwnershipWaiting。
  **callback 资源前提非空，不等于公开 switch 接口的 SWPRE 前提已从原切出路径交付。**
  本步没有增加原真实活跃切出路径的公开接口完整前提非空见证。

保存区所有权与空临界栈的单因素边界沿用冻结274 `EPowned_free_boundary`、
273 `PTsaved_stack_boundary`；本步没有通过改 frame、换内存或删失败制造新结果。
这两项是局部边界，不是完整执行消融，不据此推断全部下游机制成立。

## 对抗复核发现：复制缓存后的真实连接缺口

独立 `SPcopied_cache_gap` 证明：在 OwnershipTasks 不变、旧 current 仍是 blocked 的
OwnershipWaiting 时，只要缓存读出4，较强 `V293_current_guard` 就不成立。
已有同程序实例中旧任务优先级为6，而源码先将缓存复制为目标优先级4、再执行 switch。
这个中间点不能无条件套用本步要求的强 current 不变式。

因此，不能把270的弱 storage 切换轨迹和本步强 current TaskSim 直接拼起来，
也不能用新目标的返回证明冒充旧任务完整切回。这个反例保留为下一步连接义务，
不弱化门禁、不重写旧证据、不把失败改成通过。

下一步应使原切换义务能消费这个实际过渡态（比较复用弱 storage 候选与对过渡态作最小调整），
并从同一真实前缀交付 SWPRE_NDEAD，再重封装恢复后的 current 条件。
必须同时保留缓存不一致的拒绝对照，而不是删掉 guard。

## 证据与复现

本步目录：`audit/logs/stage275-switch-return-tasksim/`。
先冻结 `protocol.json`；保留每次失败和成功的源码快照与编译输出。
生产与 probe 各两次稳定编译、逐根 Print Assumptions、递归 coqchk、串行工程 build、
project audit、完整单测及旧失败 ID／顺序差分均由脚本留证。实际结果以 `verification.json` 为准；
尚未生成该文件时不得宣称完整检查点已通过。

```bash
python3 -B audit/logs/stage275-switch-return-tasksim/checkpoint.py
```

旧冻结材料不变；根 README／状态仅追加新的头部，工程仅登记新增生产模块。
原仓库 coverage audit stale evidence 与旧空白检查失败仍须如实保留。
清理先记录逐项 bytes/SHA，再删本步一次性 Trust 产物与已用缓存备份；
恢复原缓存字节，保留源码、失败快照、日志和可复用 Coq 对象。

**总目标仍 active：源码级 GOOD_OS、WFInt/WFIFun、同程序 K1–K4 未闭合；uCOS3 未开始。
没有提交或推送，不把局部检查点当作两个阶段最终目标完成。**
