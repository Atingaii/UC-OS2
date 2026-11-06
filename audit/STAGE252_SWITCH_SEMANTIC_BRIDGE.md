# 第252步：原物理 switch 的局部 ProgSim 桥

## 本步解决什么

第251步发现：实际 `OSPrioCur := OSPrioHighRdy` 复制后，当前抽象任务尚未切换，`GHinv` 的两分支都不成立；物理切换后又成立。原 `switch_rule` 要求在原语前关闭同一个 `SWINVt`，因此直接重用它会卡在瞬态。

本步不修补内核、不放宽 guard、不新增状态转换，而是直接使用框架已有的 `simulation.ProgSim` 构造子证明原物理 switch。**通用桥已闭合，非空有限上下文已验证；完整 Exit/Sched 环境尚未迁移。**

## 生产接口及真实义务

文件：`certiucos/v293/proofs/V293SwitchProgSim.v`。

| 接口 | 证明内容 | 保留的条件 |
| --- | --- | --- |
| `V293_switch_progress` | 确实存在原 `pswitch_step` | 当前任务有代码、环境及辅助状态；目标指针读取和当前指针写入均有效 |
| `V293_switch_all_successors` | 任意 `lpstep` 都产生同一任务表、client 状态、物理状态和目标任务 | 中断关闭；同一 typed 指针和成功 store |
| `V293_switch_no_output` | 原语点不存在 `lpstepev` | 原 switch 代码 |
| `V293_switch_no_abort` | 原语点不存在 `lpstepabt` | typed 目标可读、局部状态可投影 |
| `V293_switch_progsim` | 由高层匹配执行和后续模拟反向组合当前 `ProgSim` | **必须另证** `hpstepstar`、后继 `ProgSim`、高层当前任务一致 |

代码对 `lpstep` 的六个构造子逐项检查：中断步因 `ie=false` 排除；普通步不能执行 switch；三个栈操作与 switch 代码不符；余下物理 switch 的读写结果唯一。输出和异常单独排除，progress 单独建立，避免用“没有后继”制造空洞模拟。

桥是条件定理，不从不变量自动推出后续任务正确，也不要求瞬态满足 `GHinv`。原 `ProgSim`、`lpstep`、`switch_rule` 和框架顶层定理原文不变。

## 非空实例及对照

文件：`audit/probes/V293SwitchProgSimProbe.v`，仅作为独立验证实例，不被生产模块导入。

- `SPactual_copy_simulation` 直接复用第251步 `GHactual_copy_obstruction` 的同一份 `Mc`：原真实复制执行成立，旧 Inv 可关闭，新候选在任意分离 frame 下仍拒绝。
- 当前指针的物理 store 由既有记录所有权接口构造，不把成功写入或最终堆当成实例的输入假设。
- `SPschedule` 通过原 `hswi_step`，使用真实 `V293_scheduler` 和 `RIhighest`，从 Waiting 切到 Ready；不是把 scheduler 换成恒真。
- `SPpost` 穷尽检查 Ready 的 `SKIP/(kenil,kstop)` 终止上下文：中断关闭，没有普通步、输出或异常。后续模拟在实例中有独立证明，不是循环假设整个模拟。
- `SPbridge` 用上述高层匹配和后续证明实例化通用桥。
- `SPzero_high_match_rejected` 是单因素对照：保持切换后的物理状态和任务表，仅不更新高层当前任务，此时要求的后续 `ProgSim` 不成立。它没有证明所有高层匹配路径必须恰好一步。

原 guard 的正负对照继续使用第251步冻结证明，不改掉不利结果。新模拟成功不意味着旧 `switch_rule` 的闭合障碍消失，二者处于不同证明层。

## 严格边界

1. **不是任意 client 的证明。** 非空实例的 Ready 已经终止且中断关闭；不能由此推断能恢复 Waiting，或处理任意后续调度、中断、输出。
2. 实际复制 trace 用 `CGpending`，物理切换上下文用 `FCpending`。二者共享同一 typed 堆，但本步没有把它们声称为同一 continuation 下的完整执行，也没有证明从函数入口到返回的全局模拟。
3. 保留 ADR0010 接受的源码调用点解释边界，没有证明到汇编端口的语义保持；没有新增原语、修改 C/config/AST 或扩大授权修复。
4. 不是原 `InfRules` 推导，不是 `WFInt`，不是 `GOOD_OS`；K1–K4 未闭合，uCOS3 未开始。也不是初始化可达反例或内核漏洞结论。
5. 原 Inv/LI/BDspec 和所有既有证明、测试、冻结证据保持原字节；旧失败保留。未提交／推送。

## 路线选择及下一条真正义务

| 路线 | 证据／决定 |
| --- | --- |
| 继续强求当前候选在复制后关闭 | 第251步已反驳该 typed 中间态，不能反复尝试同一前提 |
| 放宽当前优先级 guard | 会重新接收已知的错误 same 分支入口，不采用 |
| 新增语义、phase 字段或全局规则 | 当前局部目标不需要，暂不增加复杂度 |
| 直接复用原 `ProgSim` | 原语穷尽分类及有限实例均由 Coq 检查；保留显式后续义务 |

下一步需要建立适用于**任意合法暂停任务**的后继模拟关系，并把实际复制前缀、切换以及任务恢复接到同一全局关系中。必须明确证明这种关系如何连接原 `WFInt`／顶层 refinement，不能把本桥直接标为函数环境、初始化或整核完成。

## 验证与复现

实测结果：`audit/logs/stage252-switch-semantic-bridge/verification.json`。编译尝试（含失败）保留日志和源快照；`trust.json` 对本步所有定理根执行 `Print Assumptions` 和递归 `coqchk`。信任根仅允许原框架既有的 classical/extensionality，不新增公理。

全仓构建、project audit、完整 unittest 和 `make audit` 均独立运行；完整回归旧失败与新增失败分别列于 `test-delta.json`，不通过重写旧证据使审计转绿。coverage 不增加。清理仅针对本步一次性信任驱动／产物和缓存备份，既有数学缓存恢复原字节，源码、失败证据及可复用编译产物保留。
