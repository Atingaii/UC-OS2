# 阶段26：同次成功返回的当前指针与全部任务字段联合所有权

## 对象与边界

目标仍为固定配置的 uC/OS-II V2.93.01，上游 `0c4a48e6fbc6e915714e816196619a5481accf0c`，只有原先两类已授权 C 修复。只读核对的 repaired 程序身份应为 `74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da`。本轮不改 C/config/port/framework、正式覆盖、旧测试／门禁／证据，不重绑旧报告身份，不提交 Git。手工AST与配置后源码、端口归一化仍沿用既有对应边界，不授已验证C前端、编译器或硬件信用。

只在 `certiucos/v293/proofs/V293TaskRecordOwnership.v` 原1235行逐字前缀之后追加生产证明。活动源仍167项，其他166源和12项保护输入保持。实现前冻结8813个历史文件身份、835个既有缓存路径和HEAD，见 `audit/logs/stage26-current-all-ownership/baseline.json`。

本轮只覆盖选定字段、受阻调度成功更新与返回。不是完整TCB、链表或分配器所有权；不是完整共享Inv、初始化可达性、所有API或ISR、正常无锁切换、源码级GOOD_OS与同程序K1–K4。uC/OS-III尚未启动。

## 最小连接与对抗审查

- `V293_current_fragment_local` 提取当前指针真实编码片段及其块支持集。保留框架 `CurTid` 的只读半份额，不能据此宣称其完整可写。
- `V293_current_task_records_block_frame` 提取整个 `CurTid ** owned_task_records` 片段，把内部join原样保持到最终内存；支持集为当前指针块和实际任务成员块的并集。不是从两个独立的 `** Atrue` 结论拼出联合资源，不从load构造权限。
- `V293_current_tasks_fields_reconstruct` 依靠物理／抽象域正交，将联合空间资源和更新后的抽象字段组合；不是复制物理资源。
- `V293_critical_wait_current_all_owned_execution` 只调用一次旧全任务成功执行根。五store内存模型用于frame比较，不是第二次API执行。程序执行、spec_step、更新任务表、位图／priority table／event关系与联合资源都属于同一个Mf／Os'／OO'。

非目标任务块仍需避开实际写／free集合。current块仅在不等于目标TCB块时要求避开该集合；相等时用目标整块精确frame，因此没有增加不必要的块互异要求。字面例子只覆盖不同块，不授同块API执行实例信用。入口任意R不保证跨local free保持。

## 入口与终态消费

新 `V293CurrentAllOwnershipProbe.v` 从实际入口重新组合current块80的半份额与目标41、ready任务60的完整选定字段。不复用任何旧执行完成定理；旧入口布局与终态消费辅助可复用。

同一次返回：目标 `(41,8)` 优先级8→6，仍等待SEM `(72,5)`、delay1、消息 `(120,7)`；另一任务 `(60,0)` 仍ready、优先级4，current仍60。ready16/0不变、event0/1→64/0，返回0、caller恢复、locals释放；run／ISR／lock仍1/1/0。终态消费者从同一联合状态读回current，并分别证明两任务字段可实际store。另用实际load排除错误current=41以及旧规范任务表所有权。并不声称这些后续store保持内核Inv。

## 前瞻消融

实现前的 `protocol.json` 冻结两个单因素控制：

| 控制 | 唯一改动 | 未改变部分／信用 |
| --- | --- | --- |
| DroppedCurrentFrame | current块安全前提改成True | 其余前提、结论和整个目标Proof后缀保持；downstream_credit=false。 |
| WrongCurrentPointer | 仅返回的CurTid改指目标TCB | 入口与其余输出、整个目标Proof后缀保持；不从提前拒绝授下游信用。 |

隔离Positive须以完整候选源重证，不导入候选自身；Production、新Probe、Positive须分别编译并各自coqchk。4个正控根与5个probe根使用旧假设白名单，不放宽。开发成功不替代生产和隔离重证。所有失败快照保留。

开发root01通过；root02在局部clear过早移除 `fst t <> bt` 后失败；root03仅保留该事实即通过，未改前提／结论。整份生产源随后独立通过。具体时间输出和诊断见root01–03及root-diagnosis.txt。

## 验收结果

生产源当前1528行／97,023字节，原1235行／76,317字节逐字保持，追加293行；SHA256 `7070546811cd77db6750c73c39f38ed0054c3bbdd335cce7064d35d0a4bab3f5`。新probe404行。生产与字面probe首次独立编译均通过，15个旧fixture逐项重编全部退出0。

gate01实际退出0，8项符合预期，198个冻结输入保持：

| 实际检查 | 退出码 | 秒数 |
| --- | --- | --- |
| Production coqc | 0 | 152.32 |
| 隔离完整源Positive coqc | 0 | 148.20 |
| 新Probe coqc | 0 | 16.55 |
| DroppedCurrentFrame | 1（预期拒绝） | 143.35 |
| WrongCurrentPointer | 1（预期拒绝） | 144.57 |
| Production独立coqchk | 0 | 211.07 |
| 新Probe独立coqchk | 0 | 225.81 |
| Positive独立coqchk | 0 | 209.62 |

两项控制的目标Proof都从1470行开始。DroppedCurrentFrame实际1500行拒绝：True不能作为CurrentSafety函数应用；WrongCurrentPointer实际1526行拒绝：abstract_current不能统一成目标TCB指针。整个Proof后缀保持，均downstream_credit=false；不是独立证明后续每个机制都有检测能力。字面终态另有实际load排除错误current的定理。

4个正控根和5个probe根的假设并集仅classic、functional_extensionality_dep，原白名单未改。三个独立coqchk目标分别是生产模块、新CurrentAll probe和隔离Positive，非旧probe替代。

新增6项测试实际通过。旧952项与全量958项均331失败1错误，332个诊断按kind/id重数相同，没有新增或移除。比上轮328诊断增加4项旧all-task测试诊断：源SHA、生产快照、负控快照以及从旧定理一直计数到文件尾而受到新追加定理引用污染的未限定范围断言。最后一项不是源正确性失败，也不是纯快照检查；旧定理逐字保持。旧328个诊断全部保留，不能将332项统称为快照问题。逐条差量与trace见four-added-diagnostics.txt及old/full-diagnostic-comparison.json。

范围审计、冻结C只读重验、diff检查实际通过；默认make audit仍退出2：stale function evidence input identity。正式六阶段94／1／1／1／1／0保持，未重绑历史报告。增量make build退出0，仅COQDEP／nothing-to-be-done；没有当前SHA的source-only全仓干净构建，旧构建身份不能套用。清理后的最终复核另见下文。门禁隔离树12项已按完整path／category／size／SHA清单整体核对后清理，快照、成功和失败日志全部保留。

## 一次性材料清理

全部验收与回归完成后，按事先冻结的完整manifest逐项再次核对path／category／size／SHA，再首次删除87项，共10,314,225字节：80个fixture／probe一次性Coq产物、开发隔离树6项及一个本轮误建且未使用的空临时文件。开发Root.v与root03精确快照一致，快照和所有成功／失败日志保留。835个既有缓存路径和生产模块5个可复用产物保留，源、依赖、用户数据及凭据不动。gate隔离树12项另按完整manifest已清理。

## 后续

下一缺口是将ready位图、priority table和event的真实空间资源纳入同一个联合保持，再推进正常调度、其他API／ISR、初始化与顶层连接。正式六阶段和整核状态不因本局部证明晋级。中文入门见[当前任务和全部任务字段为何要一起归还](../docs/开发中/当前任务和全部任务字段为何要一起归还.md)。

## 文档与清理后的最终复核

再次实际执行全量958项，47.92秒，仍331失败1错误；332个诊断与清理前按kind/id重数完全一致，无新增／删除。范围、只读冻结C、默认audit、diff最终退出码分别0／0／2／0。final-integrity.json确认其他166源、12项保护输入、8813个历史文件、198个门禁冻结输入、HEAD及旧文档正文保持，835个既有缓存路径仍在，87个清理目标仍不存在。未增加证明逃逸，不晋级正式覆盖，不完成总目标。
