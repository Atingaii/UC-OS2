# 阶段26：把任务字段的读数关系连接到空间写权限

## 范围与仍然开放的目标

本轮补的是选定 TCB 字段的空间资源断言及其解释，不是整个 TCB／链表／分配器不变量，也不是一个新的完整 API 证明。没有证明该资源在 `OSTaskChangePrio` 的完整执行中保持。最终源码级 GOOD_OS、同程序 K1–K4、初始化及 API／ISR 保持仍开放，uC/OS-III 未启动。

固定对象仍为 uC/OS-II V2.93.01，上游 `0c4a48e6fbc6e915714e816196619a5481accf0c`，只含既有两项授权修复。冻结程序 SHA256 仍为 `74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da`。不修改 C/config/port/framework，不授编译器、ABI 或验证 C 前端信用。

## 真实差量和构建登记

- 新增 `certiucos/v293/proofs/V293TaskRecordOwnership.v`：227行，SHA256 `651b1d1cdd3575ee239db392b9b899a77eef3c37506844ca1b330f03de31e782`。
- 新增 probe：266行，SHA256 `820bd25e95e458e0813ef5c1e0e736c476a9b2454b8e7663cb3679a5bcc8539e`。
- 全部既有166个活动源逐字不变，包括7773行的 `V293CriticalReturn.v`，未追加或重写旧完整执行证明。现167个活动源：64个目标源和103个 framework/tactics 源。
- `_CoqProject` 在原字节前缀后仅追加空行与新模块路径。旧SHA `49910507...`，新SHA `ff979a3f...`。其余11个受保护输入保持，不能宣称12个全部不变。修改前的协议和快照保存在 `build-registration-protocol.json` 与 `Before_CoqProject.snapshot.txt`。
- 8274个既有 audit/scripts/tests 文件及 HEAD 按基线保持，不重绑旧报告，不修改旧测试／门禁以接受新身份。新增文件数不计函数覆盖进展；正式六门不晋级。

## 证明链

`V293_owned_record_cell` 同时要求 `rule_type_val_match` 和实际 `Amapsto ... true ...`。字段列表用分离合取组合，任务列表使用 `TcbMod.lst` 的规范枚举，不另传一份可能不完整的任务清单。

`V293_owned_record_cell_load` 从真实片段得到 typed load；`V293_owned_record_cell_store` 从完整权限得到一次 store 的存在性。后者不包含整 API 后置资源或任意新值的类型合法性。

`V293_record_layout_sound` 分别检查 ready、时间等待和四类 IPC 状态，解释为旧的 `V293_task_record`。`V293_owned_task_records_sound` 将结果量化到同一个任务表的每个成员，并沿真实 join 将读取运输到整个物理内存。

`V293_shared_task_records` 为 `(CurTid ** shared_fields) ** owned_task_records`。一般 soundness 根从同一个状态得到实际 `abstcblsid` 槽位与全称物理字段对应；不是两个互不相关的存在式内存见证。

它仍不保证 current 是任务表中的 ready 成员，不保证等待事件存在于 ECB 表，不保证优先级唯一、TCB 分配合法性、栈或链表正确，也未证明全部抽象表均可实现。不得直接称为完整共享 `Inv`。

## 具体非空见证与语义反例

probe 构造同一物理内存：current `(60,0)` 为优先级4、ready、NULL消息；另一个任务 `(41,8)` 为优先级6，等待 SEM `(72,5)`、delay1、非空消息 `(120,7)`、pend0。字段编码实际分离，当前指针用半权限，与全部任务的完整字段片段及四个抽象槽位组合。

`OwnershipSharedLiteralSpatial` 检查该空间资源可满足，`OwnershipSharedLiteralRecords` 得到同内存／同抽象表结论。另有独立字面地址 `(41,58)`、`(41,56)`、`(60,48)`、`(41,36)` 的读取断言，防止只把候选布局重复当成外部期待。

该实例**不运行 API**，不能与上一轮的完整返回证明拼成未经检查的“资源保持”。它只排除本例新增入口的空洞性。

`OwnershipReadableNotWritable` 在同一半权限字节上检查：确实读取6，不能满足完整 `owned_record_cell`，向该内存写7不可能成功。它直接使用实际 load/store 及权限分支，不是将证明失败当作语义反例。

## 前瞻单因素控制

协议先保存在 `protocol.json`。隔离正控重新 elaboration 所有新定义和证明，不导入候选模块本身；原 raw-record 定义与旧依赖不变。

| 控制 | 唯一改变 | 保持不变 | 实际拒绝位置 | 可授信用 |
| --- | --- | --- | --- | --- |
| DroppedPhysicalCell | 单字段 `Amapsto` 改为 Aemp，保留类型纯条件 | 全部 lemma/theorem 声明与 Proof 后缀 | Proof第97行开始，第102行拒绝 | 固定读取证明确实消费物理片段 |
| WrongPriorityOffset | 布局的优先级偏移50改55 | 全部 lemma/theorem 声明与 Proof 后缀 | Proof第132行开始，第136行拒绝 | 固定布局解释证明依赖准确地址 |

两者均 `downstream_credit=false`。早拒绝不说明后面的 store、整个共享组合或 API 保持都能发现相同错误。半权限不可能写入是另外一项已检查的语义事实；不从负控报错外推。

## 开发失败及修正

所有生产01–09、probe01–12的源快照、日志和实际退出码保留。包括解析／显式导入／投影统一失败、SIGINT和超时。生产09与probe12实际编译通过。

逐句计时定位到两类大展开：先整体 `vm_compute` 再构造 Forall，使类型检查耗时明显增加；直接计算整个合并内存的 load/store 也出现超时。保留命题不变，改为逐字段证明并使用现有 mapsto/load 引理；单字节权限分支用 map_get_sig 重写，不展开内存 record 的全部证明字段。不据此声称普适性能优势。

probe08还暴露 full-pointer 与 `CurTid` 所需 half-pointer 不一致；没有放松 `CurTid`，改为构造它实际需要的半权限片段。

gate01实际退出1：Coq 编译正控与probe已过，但 probe 的多余 `Classical_Prop` 显式导入使 Print Assumptions 输出未限定的 `classic`，原严格假设检查器拒绝。gate02仅移除该未使用导入，全部定义／证明逐字不变；白名单和原检查器未修改，失败记录保留。Python首次8项检查在门禁运行期间执行，两项因最终 result 尚不存在而报错，日志也保留；不记作通过。

## 局部门禁的实际结果

gate02退出0，8项检查符合预期：生产／隔离Positive／独立probe共3次 `coqc`，两项预期负控退出1，生产／probe／Positive各一次 `coqchk`。后三项实际各约208／212／209秒，不能仅凭前面的编译结果代替。

184个不同冻结输入保持。4个正控根与8个probe根打印的假设并集均仅 `Classical_Prop.classic` 和 `FunctionalExtensionality.functional_extensionality_dep`。隔离树按清单核对后移除，所有变体源快照和失败日志保留。gate01依然保留失败结论，不改写成通过。

新增8项协议回归在门禁结束后实际全部通过；它们不增加正式函数覆盖。

## 全量回归和默认审计

- 全量实际934项，319失败、1错误，退出1。与同轮旧926项的320个诊断按重数完全相同，新增8项没有新增失败。与上一轮310个诊断相比，全部保留，另增6项旧 `_CoqProject` SHA检查与4项旧活动源集合检查；逐条 traceback 支持该6+4归因。不把其余310项都解释成快照错误。见 `legacy-diagnostic-comparison.json` 与 `test-comparison.json`。
- 增量默认构建退出0，重新生成 Makefile.coq 并执行 COQDEP，没有 Coq 重编；单独这一项不授源码干净构建信用。
- 范围审计、冻结源码只读检查、diff检查退出0。默认 `make audit` 仍退出2：stale function evidence input identity。旧覆盖和证据不重绑，正式六门保持94／1／1／1／1／0。

复查发现的关键边界：具体共享见证使用空 ECB 表，但任务表仍含等待 SEM 的成员。新增组合确实允许这一状态，因而不能推出事件／任务相容性；本报告不把该见证称为真实可达的合法内核入口。下一步必须另外组合事件资源／队列相容条件，不能从已有字段所有权循环推出它们。

## 当前身份的源码隔离干净构建

本轮另做了真实的 source-only 干净构建，不沿用增量构建的缓存结论。一次性驱动和前瞻协议保存在 `clean-build-driver.py.snapshot.txt` 与 `clean-build/protocol.json`。

复制且核对167个活动源、Makefile、_CoqProject、coqc-wrapper共170个输入到全新隔离树；入口没有 `.vo/.vos/.vok/.glob/.aux`，没有复制 archives 或工作树 Coq 缓存。登记的 `.v` 集合与全部167源严格相等，调用原默认 `make build`，Coq8.18.0、JOBS2。

实际退出0，耗时1032.53秒，生成167个 `.vo`。输入在仓库及隔离副本中均保持SHA一致。它建立的是**当前167文件身份可由源码重新构建**，不自动刷新历史函数证据或覆盖报告，不授 GOOD_OS／全部API／ISR／初始化／K1–K4 闭合信用。

结果见 `clean-build/result.json`、`input-manifest.json`、`build.log` 和 `build.exit`。隔离树的全部源副本／构建产物按路径、类别、大小、SHA核对后才统一删除，原始源文件和失败／成功记录保留；清单为 `clean-build/cleanup-plan.json`。

## 工作树清理和下一步

独立门禁结束、隔离构建已使用自有源码副本且不依赖工作树缓存后，工作树另清理15个本轮生成且已无需交付的 Coq 编译产物，共9,847,254字节。第一次删除前确认整个集合及其保留源／门禁快照；三个源分别为旧CriticalReturn、新资源模块及新probe。903个既有缓存路径全部保留，不声称其字节不变。全部源码、用户数据、依赖以及开发失败、gate01失败和gate02成功证据保留。隔离门禁与干净构建临时树按各自清单清理，另计。

下一步应在同一次实际 API 执行上证明字段资源更新与归还，保持其他任务资源；随后组合优先级表、ready／事件位图及事件队列相容关系。特别不能把本轮“资源能推出读数”逆用为“读数自动产生资源”。阶段一仍未完成，不提前启动 uC/OS-III。
