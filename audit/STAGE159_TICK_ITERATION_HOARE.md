# 第159步：按原顺序连接 tick 单次循环体 Hoare 规则

## 这一步解决什么

第158步已有延时分支的正式规则，但出口的 `ptcb` 仍指向当前任务。本步从真实拥有的 `OSTCBNext` 字段读取指针，执行原赋值，再按原顺序退出临界区；不是另造一个只算结果的循环模型。

原归一化 AST 保持不变：

```text
encrit ; (delay ; (ptcb = ptcb->OSTCBNext ; excrit))
```

源码版本仍为固定 uC/OS-II V2.93.01，上游提交、配置、两类授权修复及手工宏映射边界均不变；`source-identity.json` 保存并核查原函数定位与哈希。C、配置、原 AST、framework、tactics、旧证明／测试／证据均不修改。

## 接口与实际保证

生产文件：`certiucos/v293/proofs/V293TimeTickIterationHoare.v`。

| 接口 | 结论 |
| --- | --- |
| `V293_tick_advance_fragment_hoare` | 从指针绑定及十个 raw 字段推出真实 field7 求值，按原赋值更新局部 `ptcb`，保留真正 next 字段与同一 frame |
| `V293_tick_delay_advance_with_tail` | 使用既有 delay 规则连接 next 与已证明的 continuation，保持原右结合，不调换退出顺序 |
| `V293_tick_iteration_hoare` | 单次原循环体的 `InfRules`；覆盖所有 unsigned delay、全部物理 status 字节及两种初始 IE，出口恢复原 ISR／IE／中断栈／临界栈 |
| `V293_tick_iteration_semantics` | 仅经既有 `RuleSound` 正向导出 `RuleSem`，不从执行端点反推规则 |

主接口没有执行或表达式求值前提；求值由原始字段所有权推出。前提明确保留 byte／地址范围、环境、`CurLINV`、`GoodFrm R` 和 `gettopis si <= INUM`，没有为编译通过而删除门槛。

初始 IE=true 时，`encrit1_rule` 获得的 `invlth_isr I 0 top` 作为额外的原样 frame 穿过 delay 与 next，再交还 `excrit1_rule`；初始 IE=false 使用对应第二条规则。`I` 任意，未换成空不变量。调用者必须在进入前另外拥有 raw 字段，本步**没有**从实际生产 IRQ 不变量借出 TCB 再重封闭它。

## 非空入口和单因素对照

探针文件：`audit/probes/V293TimeTickIterationHoareProbe.v`，不导入活动生产工程。

- `IHentry` 复用第158步构造的实际编码字节、只读 current 指针与 canary，以 `GoodFrm` 在不改内存／环境／抽象资源的情况下重基控制态。
- `IHrules` 直接实例化新生产规则，`IHbranch_cases` 检查 delay0／1／3／4294967295、11种 status 和两种 IE，共88个具体入口与规则实例；生产根本身仍是一般量化定理，不以88例替代。
- 首次使用旧探针中断栈顶3时正式上界失败：框架 `INUM=2`。失败快照保留；未改框架或上界，新入口和独立操作执行均使用合法栈顶1，并实际证明上界。
- `IHwrong_pointer` 从独立的原操作语义得到同一实际 `Mf`，只把局部指针期望替换为旧节点81:8；正确新指针、真正 next 字段81:28和 caller canary99同时保留。
- `IHwrong_ie` 绑定独立执行的实际终态，只把 IE 期望改为反值；同一实际临界栈仍为 `[false]`，canary99仍可读取。它和指针对照分开验证，不让一个早拒绝冒充两个机制都有效。

独立操作路径复用既有逐步执行定理，在新探针中以合法栈顶1实例化；只作负控，**不是新 `RuleSem` 的运行测试，也不是新 Hoare 的前提**。这两项操作负控针对 delay1／status1；并未声称对所有一般参数逐个执行。

## 验收证据

记录目录：`audit/logs/stage159-tick-iteration-hoare/`。

| 项目 | 实测结果 |
| --- | --- |
| 构建／清理后重建 | 退出0；保留两次命令及日志 |
| 稳定编译 | 生产 `iter07`、探针 `probe08` 退出0，源哈希前后一致 |
| 独立检查 | 12个新增根，329活动＋48探针模块全部通过；`coqchk`用时797.601秒 |
| 信任边界 | 实际classic／funext_dep／Eqdep均在原allowed中；533份Coq输入在检查期间不变 |
| 新增回归 | 7项通过，不用文本检查替代内核检查 |
| 全套回归 | 1944项；423失败、1错误，完整ID集合与第158步一致，各轮JSON保留 |
| 审计 | PROJECT PASS；coverage仍因旧函数证据identity过期退出2，未伪造通过 |
| 空白检查 | 仅旧 `framework/logic/inferules.v:581–586` 六行，退出2；新源／测试／说明无行尾空白 |
| 历史材料 | 本步前26485份旧文件，仅README／状态／项目入口／生成依赖有预期差异；核查见verification.json |
| 清理 | 先确认全部目标，再清理9个一次性文件，共673240字节；恢复两份既有缓存，保留源、失败证据及可复用产品 |

本步共保留15次编译快照，其中11次失败；包括中断栈上界的真实失败，不覆盖不利记录。10项对抗复核见 `adversarial-review.json`。最终验收以 `verification.json`、`checkpoint-report.json` 和身份清单为准，不以这张文字表格替代机器证据。

## 保留的边界和下一步

本步是单次循环体，不是完整 while、完整 tick API／ISR或完整函数。生产 LocalInv／Inv、任务／ready／等待关系与 raw 字段的转换、循环不变量、初始化／WFIFun、CPU hook、最终 `GOOD_OS` 和同程序 K1–K4 仍开放。CPU hook保持启用，不造空函数跳过。

宏归一化仍遵循 ADR0005：这是接受的源码级中断抽象，不是原 CPU_SR 端口调用的语义保持证明。实际假设包括既有 classic、funext_dep 及 RuleSound 路径的 Eqdep；不宣称无公理。

下一步优先让该稳定接口承接有限链／ready关系并构造原 while 的正式循环不变量，同时明确生产 IRQ 不变量的资源转移义务，不继续以孤立执行片段代替函数纵向连接。六门94/1/1/1/1/0不变，不增加函数覆盖信用。

第一阶段尚未完成，uCOS3未开始；两阶段总目标继续 active。本步不提交或推送。
