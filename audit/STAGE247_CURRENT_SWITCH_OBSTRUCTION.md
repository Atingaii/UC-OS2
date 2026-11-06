# 第247步：直接加入全程当前优先级关联不满足切换闭包

## 结论和决策

第246步确认实际中断入口不能无条件推出当前任务／优先级关联。本步进一步用 Coq 证明：**若候选不变量保留原来关联正确的 Waiting 入口，并要求每个 `SWINVt` 状态都具有关联，它就不能满足当前框架的 `GoodI`。** 因而不能仅给旧不变量附加一个全程等式来修复入口缺口。

不改 C、配置、AST、框架、旧不变量、规格或旧证明。新增证明是独立边界检查，不接入生产模块，也不增加 full-target 覆盖。

## 非空资源和实际切换

文件：`audit/probes/V293CurrentSwitchObstruction.v`。

从已有 `PPnonempty false nil` 的 typed 完整内存中，按 concrete／abstract join 拆出真实 `SWINVt PPinv OwnershipWaiting` 片段。不是假定候选 Inv 有模型，也不是用不满足入口的任意内存构造反例。

| 项目 | 切换前 | 框架第三子句要求的切换后 |
| --- | --- | --- |
| 抽象当前任务 | Waiting，优先级6，在任务表中仍存活 | Ready，优先级4 |
| 最高就绪任务 | Ready | 不变 |
| physical 当前任务指针，块1 | Waiting | Ready，真实 typed pointer store |
| 当前优先级字节，块94偏移0 | 6 | 仍为6 |
| 任务表、其它块字节 | 原值 | 不变 |
| 原 `SWINVt PPinv` | 成立 | 成立 |
| 从状态实际读取的当前任务／优先级关联 | 成立 | 不成立 |

`CScache_owned` 从 storage 所有权取得字节 load；`CSfields` 从共享资源取得实际抽象当前任务和任务表。`CSswitch_witness` 证明上述前后条件，包括两个字节 load 和块1之外逐字节不变。关联使用第246步 `NCcurrent_relation`：读取状态实际的 curtid、任务表和优先级字节，不把预期任务写入谓词。

## 比旧 switch 反例新增了什么

旧 `PPactual_switch` 已展示一次具体切换后的字节不一致，不能再次把它当作新发现。本步新增的核心定理是 `CSexact_strengthening_not_GoodI`，量化任意候选 `Inv0` 和任意 `li`，但带两个明确条件：

1. 每个满足旧 Waiting `SWINVt` 且具有关联的状态，也满足候选 Waiting `SWINVt`；
2. 每个候选 `SWINVt` 状态都蕴含 `NCcurrent_relation`。

在这两个条件下，定理证明 `~GoodI Inv0 V293_scheduler li`。证明真正提取并调用候选的 `GoodI` 第三子句，而非只对旧 `PPinv` 运行一次 switch。旧当前任务确实在同一任务表中，排除 dead 分支，不能通过私有资源释放分支回避矛盾。

第三子句更新 physical 当前任务指针和 abstract curtid，却不写当前优先级字节。因此第一条件带入的非空关联入口经该子句切换后，第二条件要求的关联无法成立。

## 单因素对照与范围

`CSwithout_strengthening_good` 复用已证明的 `PPgood`，检查去掉额外全程关联要求时原 `PPinv` 的 `GoodI` 确实成立。框架、scheduler、原资源、切换 pointer store 保持不变。主结论不是以早期拒绝代替下游检查。

**不是所有可能 Inv 不存在**：不保留全部旧关联入口的候选，或使用不同阶段边界的契约，都不在否定结论内。两个假设必须一起保留在引用中。这里也不声称已构造一个满足这两个假设的候选 Inv；非空的是旧资源及关联入口。

**不是可达内核漏洞，不是初始化可达，不是 `WFInt`，不是 `GOOD_OS`。** 这是框架闭包与候选加强方式之间的障碍，不是完整 C 执行反例。同程序 K1–K4 未闭合，uCOS3 未开始。

下一步检查能否将稳定执行边界的关联与 switch 过渡分开，在实际源代码写入顺序上恢复所需关联；本步尚未实现这种契约，不能预先宣称它可满足 `WFInt`。不得为消除障碍修改已冻结规则或偷偷补一次 priority store。

## 验证与复现

证据目录：`audit/logs/stage247-current-switch-obstruction/`。`protocol.json` 在首轮编译前冻结问题、单因素和保持项；上一步清单99项已核验。失败编译快照全部保留。

`probe09` 为首次通过版本；`probe10` 增加 witness 的可观察 load／frame 结论后通过。删掉两个直接 imports 的 `probe11` 失败，原因是 `V293_load_block_frame` 需要直接导入 `V293TaskPrioRekey`；恢复该 import 后 `probe12` 通过。最终只移除一个无用直接 import，证明正文与 `probe10` 逐字一致；不称两项都可删除。

```bash
python3 -B -m unittest discover -s tests -p test_current_switch_obstruction.py -v
python3 -B audit/logs/stage247-current-switch-obstruction/checkpoint.py recheck
```

独立 `Print Assumptions` 和递归 `coqchk` 的结果、构建／审计／测试真实退出码以 `trust.json`、`verification.json` 为准，不用外层日志运行器的成功代替内部命令成功。新增5项结构回归只检查证据接口；语义判据是 Coq 内核。旧423失败、1错误保留并核对具体顺序；`make audit` 的旧 evidence identity 失败及旧框架六行 whitespace 失败不改写。覆盖保持94/1/1/1/1/0，未提交／推送。

收尾先确认一次性 Trust 驱动／产物及缓存备份清单，再清理；恢复本步开始前两个根目录算术缓存的原字节。保留源码、旧数据、依赖、可复用 Coq 产物、日志及失败快照。
