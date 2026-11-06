# 第308步：同一程序覆盖全部不调度中断分支

## 本步要消除的缺口

第307步仅覆盖 running=1、原嵌套深度1..254，且依靠整块内存恒等完成返回。本步不另造几份程序或假定后置资源，而是从同一未附加 quiet 过滤的 `BuildintPre`、同一输入堆、同一两个函数绑定，构造全部不调度分支的完整实际返回。

`V293InterruptBuilderQuietExecution.v` 的上层接口是 `V293_builder_quiet_global_return`。相同接口涵盖：

| 原控制字节 | Enter 后 | Exit 后 | 实际结果 |
| --- | --- | --- | --- |
| running≠1；任意有效深度、锁 | 深度不变 | 深度不变 | 不调度 |
| running=1；深度1..254 | 深度+1 | 原深度 | 不调度 |
| running=1；深度255 | 仍为255 | **254** | 不调度，但不是内存恒等 |
| running=1；深度0、锁>0 | 深度1 | 深度0 | 不调度 |
| running=1；深度0、锁0 | 深度1 | 需进入 dispatch | **不属于本步结论** |

有效控制字节均限0..255。唯一选择条件为 `V293_control_dispatch (V293_control_enter c)=false`，不是删除真实控制信息后加入“可以任意不调度”的规格。

## 如何连接实际执行与资源

1. `V293_quiet_call_exact` 在函数内部选择 fresh 块、分配及清零 saved 局部变量，执行真实分支，释放局部块并返回原 caller。它不要求上层提供分配、释放或执行存在性前提。
2. `V293_builder_snapshot_exit_memory` 在同一实际后继堆保留完整 ready/TCB/storage snapshot；不是对另一个投影堆重建资源。
3. `V293_builder_quiet_execution` 从原 builder 提取环境、字节、写权限与分离性，组合 EOI/Enter/Exit；同一后继同时支持 snapshot、控制字节读回与固定控制前端轨迹。
4. `V293_builder_quiet_return_ready` 在该后继恢复旧 `BuildintRet`，使用 builder 自身的低位 ISR 清零事实，不假设全部 ISR 位均为 false。
5. `V293_builder_quiet_global_return` 要求显式入口一步与返回一步，中间提升同一局部轨迹。最终任务代码、表达式/语句 continuation、caller、任务辅助状态与 ISR 恢复原值；内存使用计算出的精确 `Mf`，不把255→254错误写成 roundtrip 恒等。

精确后继内存写成：

```
final = control_exit (control_enter c)
Mf = put_byte M nesting_address final.nesting
```

这是堆相等的标准表达，不声称每个分支都实际执行一次写指令；跳过写入时，由已有真实可写字节与 frame 证明这个表达式等于原堆。除嵌套字节外，整块原内存保持不变，fresh 局部块也已精确释放。

## 非空实例和单因素观察

`audit/probes/V293InterruptBuilderQuietExecutionProbe.v` 始终使用原 `BNprogram` 的两个函数，不替换为 `RDprogram` 或不同的 quiet/dispatch 程序。输入由原非空 canonical ready/TCB/storage fixture 分离得到，再更新真实 running/lock 所有权字节；没有假定更新后的 snapshot。

六组原输入 `(running,nesting,lock)` 为 `(0,0,0)`、`(2,255,0)`、`(1,1,0)`、`(1,254,0)`、`(1,255,0)`、`(1,0,1)`。它们共用 shadow caller、非空表达式和语句 continuation，并保留另一个为 true 的 ISR 位。

饱和实例 `QEcompleted_saturated_observation` 先得到完整入口、主体、返回和 `BuildintRet`，再证明最终字节254，且最终堆不等于原堆。随后按预先冻结的 `ablation-protocol.json`，只把最终观察期望254改为255：基线编译通过，变体在 `exact Observed` 处拒绝，失败上下文包含完整三段轨迹。它只证明完成后观察对错误期望敏感；**不是删除执行机制的消融，也不是所有机制必要性的证据**。

## 验证与失败保留

原始命令、退出码、耗时、每次失败的源码快照、递归复核、假设闭包、全回归及清理记录均保存在 `audit/logs/stage308-builder-quiet-execution/`。最终实测汇总以该目录 `verification.json` 为准。生产与 probe 均执行两次固定哈希重编译；新生产文件只追加注册一次，probe 不注册。

此前全回归基线为2717项、437失败、1错误；不修改旧测试或冻结报告以制造通过。本步还保留既有 `make audit` 的 stale function evidence input identity 与旧六处 inferules 空白问题。新回归若增加失败必须单独解释，不能覆盖旧结果。

本步已完成的实测如下；局部检查通过不改变全仓尚有失败的事实。

| 检查 | 实测结果 |
| --- | --- |
| 生产文件固定哈希重编译两次 | PASS；2.723秒、2.666秒 |
| 非空 probe 固定哈希重编译两次 | PASS；2.586秒、2.551秒 |
| 增量构建 | PASS |
| 10个结论的假设检查及递归 `coqchk` | PASS；递归复核424.623秒；仅原允许的经典逻辑、函数外延性 |
| 新增回归 | 7项全部通过 |
| 完整回归 | 2724项，437失败、1错误，88.247秒；与第307步失败/错误标识及顺序完全一致，无新增失败 |
| 项目审计 | PASS；382个活动证明文件、103个框架/策略文件 |
| 综合审计 | FAIL，退出码2；保留旧函数证据输入身份失配 |
| `git diff --check` | FAIL，退出码2；与第307步相同的六处旧空白问题，输出逐字节一致 |
| 完成后的饱和深度单因素观察 | 期望254通过；仅改为255后在最终观察处拒绝 |
| 历史与环境保留 | 非许可变更文件及上步冻结清单核对通过；306个原有 `.pyc`、原有根目录求解缓存逐字节不变 |
| 一次性文件清理 | 逐一核对后删除17个临时检查器、其产物和本步缓存备份；保留失败快照、日志、协议、源码及可复用编译依赖 |
| 最终检查点 | `verification.json`：局部检查通过，整体目标未完成，目标仍为 active |

Git HEAD保持 `1f57743c638c7e1ccdcc594e51dc90c0c7406789`，没有提交或推送。本步证据以 `checkpoint-evidence-manifest.json` 冻结；该清单不覆写上一步清单，也不要求旧清单中的可变入口文档永远保持旧内容。

## 仍未证明的内容

- 这是 normalized port 边界下的有限执行存在性，不是所有交错 safety、TaskSim 或统一旧 WFInt。
- builder 是实际 pint 后 handler-entry 堆的输入资源；尚未从初始化证明可达。未启动/非最高就绪等实例也不声称初始化可达。
- 局部实际执行接口可带原 aop，但连接旧返回 builder 的接口仍要求高层 `END None`；固定控制前端不是已完成迁移的旧全局 osintspec。
- 未覆盖需调度分支、完整内核函数表与初始化；不将二函数程序称作完整内核。
- 源码级 `GOOD_OS` 和同程序 K1–K4仍开放，uCOS3尚未开始。目标保持 active，无 Git 提交或推送。

下一步应把上述真实控制状态及不调度结论接入统一中断模拟接口，并与需调度分支共用生产规格；不能仅凭新增有限轨迹例子报告整核完成。
