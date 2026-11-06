# 第160步：从单次循环体连接原 tick while 的正式 Hoare 规则

## 这一步解决什么

第159步已经得到原单次 `encrit ; (delay ; (advance ; excrit))` 的正式规则，但不能直接推得完整循环。本步为既有 `swhile (V293_tick_guard ptcb) (V293_tick_iteration ptcb rows group)` 构造循环不变量，再应用框架原 `while_rule`，保持原 guard、循环体、临界区顺序和 AST 不变。

主接口 `V293_tick_while_hoare` 覆盖任意合法有限任务链、全部 unsigned delay 与物理 status 字节及两种初始 IE；`V293_tick_while_semantics` 仅经既有 `RuleSound` 正向导出 `RuleSem`。它不是完整 `OSTimeTick` 函数的定理，也没有从独立执行端点倒推 Hoare。

生产文件：`certiucos/v293/proofs/V293TimeTickWhileHoare.v`。

## 循环不变量与精确出口

不变量只有连接所必需的三部分：

1. 同一 `aop`、ISR／IE／中断栈／临界栈、caller frame；局部指针、已处理 raw 字段、剩余任务链、ready 位图和 idle 优先级字段各自分离拥有。
2. 剩余任务合法，位图仍为 byte；真实 guard 的求值和类型由拥有的局部指针及优先级字段推出，不作为 oracle 前提。
3. 固定最终字段等于“已处理字段＋剩余任务经既有 after 映射的链”，固定最终位图等于从当前位图继续折叠剩余链的结果。

每次迭代将一个任务的更新字段移到已处理前缀，并按照真实 next 字段前移局部指针。剩余链非空时，合法优先级不等于 idle 的12，guard为真；链空时只需 idle 优先级，不需要 idle 的 delay／next 字段，guard为假，等式确定完整出口和两行位图。

| 稳定接口／辅助连接 | 实际用途 |
| --- | --- |
| `V293_tick_node_iteration_hoare` | 从任务字段＋两行 ready 资源实例化第159步，保留未选择行和优先级字段 |
| `V293_tick_while_guard_owned`／`guard_resource` | 从拥有的字节证明真实 guard 值、类型和非 undef |
| `V293_tick_while_step_hoare` | 将更新节点接到已处理前缀，保留剩余链与同一 frame |
| `V293_tick_while_hoare` | 原 while 的一般化 `InfRules`，精确最终链和位图 |
| `V293_tick_while_semantics` | 经既有健全性定理得到同接口 `RuleSem` |

框架的 while 规则提供该框架下的部分正确性／simulation 结论。本步没有另加终止性变式或证明所有外部调度均终止；独立操作探针中的有限执行不能替代一般终止性定理。

## 非空入口和单因素对照

探针：`audit/probes/V293TimeTickWhileHoareProbe.v`，不导入生产工程。

- 在同一实际编码堆构造六任务混合链：delay0／3／1，status0／1／9／8，跨两行 ready；包含真正只读 current 和独立 canary99。入口并非把任意堆满足前置条件当成假设。
- `WHentry`、`WHrules`、`WHnonvacuous` 联合给出入口可满足、一般规则实例与真实真 guard，两种初始 IE均覆盖；正式入口的中断栈顶1确实满足原 `INUM=2`。
- 独立操作执行从同一字节堆开始，得到最终指针 idle、group3、两行4／4以及每项任务更新字段。它复用旧操作语义定理，不是新 `RuleSem` 的运行测试，也不是新 Hoare 的前提。
- `WHguard_exit` 从同一个实际终态的 idle 优先级12和局部指针证明原 guard 为假，并保留实际 row4和 canary99。
- 两项负控分别只替换同一实际终态的指针或 row 期望：拒绝旧头指针、拒绝 row0；另一个正确观测和 canary99保持。不修改输入、实际终态或资源以制造拒绝。
- 探针证明调试中曾把分离合取的结合律误当成定义等价，`change` 被 Coq 拒绝；最终显式使用既有结合律与列表分解。失败源码和日志保留，不通过改语义或放宽规则绕过。

## 验收证据

记录目录：`audit/logs/stage160-tick-while-hoare/`。

| 项目 | 实测结果 |
| --- | --- |
| 构建／清理后重建 | 退出0，日志及命令均保留 |
| 稳定编译 | 生产while12、探针probe07退出0，编译期间源哈希不变 |
| 独立内核检查 | 20个新增根；330活动＋50探针模块通过；coqchk 841.019秒 |
| 信任边界 | 实际classic／funext_dep／Eqdep未超既有allowed；535份Coq输入在检查期间不变 |
| 新增回归 | 7项全部通过；信任检查前另有6项静态smoke通过，不代替第7项内核门 |
| 全套回归 | 三轮均1951项、423失败／1错误，完整旧失败及错误ID集合保持 |
| 审计 | PROJECT PASS；旧coverage证据identity过期，make audit仍退出2 |
| 空白检查 | 仅旧framework/logic/inferules.v:581–586六行，退出2；新源／测试／说明无行尾空白 |
| 历史材料 | 核对26571份旧文件，仅README／状态／项目入口／生成依赖有预期差异 |
| 编译证据 | 保留20次快照和日志，包括16次真实失败；旧LoopProbe源字节不变，仅重建缺失vo |
| 清理 | 逐项确认后删除8个一次性文件，共674316字节；恢复两份既有缓存，保留源码、失败证据和可复用Coq产物 |

新增独立检查的50份探针包含此前缺失编译产物的旧 `LoopProbe` 和新 `WhileHoareProbe`；不是只在第159步48份基础上机械加1。10项对抗复核见 `adversarial-review.json`。验收以 `verification.json`、`checkpoint-report.json` 及身份清单为准，不以文字表格替代机器证据。

## 保留的边界和下一步

caller仍须在进入前另外持有 raw 字段及 `CurLINV`；IE=true获取的任意 IRQ invariant只是原样 frame 穿过迭代后归还。本步没有完成生产 IRQ invariant 与 TCB／ready／等待关系的借出及重封装。空见证 LocalInv 的具体入口不能证明实际全局不变量已经建立，更不能证明该入口从真实初始化可达。

原 C／配置／AST／framework／tactics、全部旧证明、旧测试及冻结证据均不改。宏归一化仍遵循 ADR0005，不是原端口调用的语义保持证明。实际假设仍受既有 allowed 集合约束；不宣称无公理。

下一步是让循环稳定接口进入完整 tick 的纵向规格，连接生产共享资源、CPU hook 和 ISR 边界；CPU hook保持启用，不制造空函数跳过。原 while 与已有 clock／局部分配及返回片段尚未构成完整函数定理。初始化／WFIFun、最终 `GOOD_OS` 和同程序 K1–K4仍开放。

六门94/1/1/1/1/0不变，不因新增文件赋予函数覆盖信用。第一阶段未完成，uCOS3未开始；总目标保持 active。本步不提交／推送。
