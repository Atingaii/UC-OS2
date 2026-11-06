# 第301步：固定控制前端与 Enter/Exit 资源更新

## 本步要补的缺口

第300步已从实际堆读取三个控制字节，但 `V293_control_exit_code` 仍只是选择函数。本步增加一个显式有状态的小步前端：同一个 `Enter` 或 `Exit` 操作符，依据保留的控制状态执行。它不是每个输入堆各闭包一个不同的高层规格，也不采用任选调度/不调度。

**这是迁移组件，不是已经安装到旧框架的生产中断规格。** 旧 `osintspec` 的结果类型仍是 `spec_code`，本步前端的结果类型不同。旧 `TaskSim`、`WFInt`、全局切换和 `GOOD_OS` 健全性没有随之迁移。

## 精确对象及更新顺序

[生产接口](../certiucos/v293/proofs/V293InterruptFixedControlSpec.v)在第300步的 `(osabst * V293_irq_control)` 上定义：

| 操作 | 读取的控制状态 | 后继代码 | 保留的状态更新 |
| --- | --- | --- | --- |
| `Enter` | running、递增前 nesting | `Core (END None)` | running=1且depth<255时递增，其他不变 |
| `Exit` | running、**递减前** nesting、lock | enabled时 `Core (sched ;; END None)`，否则 `Core (END None)` | running=1时depth取pred；running和lock不变 |
| `Core` | 旧抽象状态 | 仅由原 `spec_step` 决定 | 控制字段保持不变 |
| `Seq` | 前一个操作的后继 | 执行前项、消费其END再到后项 | 只转送已有状态更新 |

`V293_control_exit_exact` 排除 Exit 的其他一步结果。`V293_control_core_exact` 和 `V293_control_core_trace_exact` 双向反射旧一步/有限步：不是只有可嵌入而容许额外旧行为。`Core` 不给非最高当前任务凭空增加 self-sched。

`V293_fixed_control_intspec` 在 `i<INUM` 时总返回**相同**的 `Seq Enter Exit`。它是新前端的固定表，不是旧 `osintspec` 类型的实例。`handler_prefix` 只跑到 Core 后继；enabled 时没有自动完成后面的调度。这张前端表仅表示 Enter/Exit 配对控制前缀，不包含一般 ISR 工作体、EOI 或返回的完整模拟。

## 与真实源码连接到了哪里

源身份见[锁定清单](logs/stage301-fixed-control-spec/source-identity.json)：固定 V2.93.01、上游提交、冻结修复清单、配置、原 AST 和复用证明均不改，没有重新预处理。原 `os_core.c:663–671` 的 Enter、`693–736` 的 Exit 是本步控制语义依据。

- `V293_control_enter_source`：复用真实 `V293_OSIntEnter_updates_hoare`，前后三个控制字节资源对应 `c` 与 `enter c`。lock作为帧保留。
- `V293_control_exit_source`：**仅 running=1 的真实递减前缀**，复用 `V293_OSIntExit_decrement_hoare`；running与lock帧保留，depth对应 `exit c`。
- `V293_control_cells_capture`：这些字节资源唯一确定 reader 观察值；结合前后 Hoare 资源，可分别读取更新前后控制字段。**两个端点观察不是一条具体 `cstep` 执行轨迹，也不是已经建立的新前端模拟关系。** 这些 Hoare 规则仍使用原 `InfRules`，没有让它消费新 `Enter/Exit` 操作符。
- `V293_fixed_control_builder_prefix`：从原、未过滤 `BuildintPre` 捕获有界 c，再执行新固定前端的前缀。原 builder 的 `intspec` 与新表是两个不同对象；该定理不声称它们已相等或是同一个 WFInt 的参数。

## 独立判别和反例

[Coq 探针](probes/V293InterruptFixedControlSpecProbe.v)复用原 AC 堆：running=1，n=0或1，lock=0。唯一修改 `(151,0)` 锁字节到1，所有其他地址保持：

- 同一个旧抽象任务状态、同一个新 `Exit` 操作：原堆到 `Core (sched ;; END None)`，修改后到 `Core (END None)`；两者都保留退出后的depth=0和各自lock。
- 原完整调用仍分别使用 `CCspec` 与 `QCspec`。新前端同代码对照不把这两条旧调用伪装成同一个旧高层程序的轨迹。
- n=0/1都覆盖；真实配对前端还覆盖depth=255饱和后落到254、running=0/2、lock=255。不能把255配对说成恢复原深度。
- quiet 当前非最高时可到END；enabled的Core sched仍不能自步完成。**全局 `hswi_step` 尚未提升到本前端。**

[前瞻消融协议](logs/stage301-fixed-control-spec/ablation-protocol.json)在执行前冻结。三个独立 Coq 对照，每组只改一个规则表达式，并编译同一个具体判别式：忽略锁、重复递减后再选择、丢弃退出状态更新。三个基线通过，三个变体各自失败；源快照与失败日志均保留。这只证明各判别式能区分相应变体，不统计其他下游根的消融通过数。

Python 独立逐步控制条件影子检查262144组，三个单因素变体的差异数分别为510、1、65280；它不模拟内存或调度器，不能代替 Coq/源码级整核证明。

## 审阅结论与下一步

1. 本步把选择函数推进为可执行的新固定前端，并给出资源更新接口；没有完成旧框架状态迁移。
2. 下一条主线应为新前端选择并落实**实际健全性接口**：全局切换、C执行与控制观察的保持、函数/中断模拟，以及初始化。不能只再增加选择器或局部表。
3. 当前不变式允许的 Waiting-current 堆未证明初始化可达。更强入口不变式仍需建立和保持，不能直接删掉反例。
4. 完整单一目标 `GOOD_OS`、同程序 K1–K4 和后续 uCOS3 均未完成。目标保持 active，未提交/推送。

实测结果与清理记录见[verification.json](logs/stage301-fixed-control-spec/verification.json)和同目录日志；增量 build 不代表 clean build，原审计/全回归失败不转换成通过。

## 最终实测

- 生产13个根、探针5个根，共18个；双稳定编译、全部 Print Assumptions 和递归 coqchk 通过，复核约570秒。只保留既有 classic / functional_extensionality_dep 信任边界。
- 新测试8/8通过；完整回归2678项，436失败、1错误，与第300步失败ID及顺序完全相同。一次预检查误用 unittest 的-k，发现0项，未计为通过；随后实际执行7项非信任测试及全部8项新测试。
- 增量build通过；project audit为375个活动Coq文件及103个框架/战术文件通过。make audit仍因旧function evidence身份失配失败；git diff --check仍只有原581–586六处尾空白。
- 原2690个输入除README/status前插、project追加及生成依赖文件外保持；上步106项冻结证据受保护。35个本轮临时文件逐项确认后清理，源快照/失败日志保留；原306个pyc及两根原缓存不变。
