# 阶段26：目标任务字段所有权连接同一次成功返回与抽象更新

## 1. 固定对象与差量

目标仍为 uC/OS-II V2.93.01，上游提交 `0c4a48e6fbc6e915714e816196619a5481accf0c`，仅两类已授权 C 修复。只读重验后的程序身份仍为 `74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da`。实际配置后函数与手工 AST 的既有源码身份对应不等于已验证 C 前端或 ABI。

唯一追加的生产源是 `certiucos/v293/proofs/V293TaskRecordOwnership.v`：原422行逐字保持，追加477行至899行、53,598字节，SHA256 `c019819f51fda2b656b8a422d82fd54bcb0c1d629be632b18a7b6c2074002dd2`。其余166活动源、12个受保护输入（含 `_CoqProject`）、8547个既有 audit/scripts/tests 文件及 HEAD 保持。仍167活动源，64目标源＋103框架／tactics源。不改 C/config/port/framework、旧测试、门禁、报告或正式覆盖，不提交 Git。

日志根：`audit/logs/stage26-api-task-ownership/`。原 README／进度文档完整快照保留，新检查点只前置插入，不重写历史内容。

## 2. 从中间五赋值到真实返回

- `V293_critical_event_return_tcb_owned_block` 是既有受阻调度成功返回的增强根。真实成功更新执行与尾部返回执行各调用一次，保留其原有终态读数、优先级表、ready／event 位图、指针、返回0、caller恢复、局部释放和块 frame。新增整个目标 TCB 块的**字节与权限**等于五赋值内存中的同一块。它不假定一个满足出口的最终内存。
- `V293_owned_cells_block_local`／`V293_owned_task_record_block_local` 在实际资源片段上证明抽象域为空、物理支持集限于目标块以及环境重基址。
- `V293_owned_task_record_block_frame` 用实际 `Maps.sub` 与精确块 `get` 相等，把记录片段运送到返回内存；没有从 typed load 反推资源。
- `V293_owned_task_fields_reconstruct` 用记录片段的空抽象域和 `shared_fields` 的空物理域，在**同一**内存／抽象状态重建空间组合，不重复拥有资源。
- 稳定接口 `V293_critical_wait_record_owned_execution` 将物理优先级表／ready／event 等待位图对应与实际任务绑定作为入口条件。从入口资源导出目标可写权限，并由空物理新槽推出抽象 fresh。只调用一次 `V293_wait_prio_owned_step` 和一次上述真实返回根，得到同一 `Mf / Os' / OO'` 上的 `spec_step`、真实执行、更新后的对应关系以及 `(新目标记录 ** 新shared_fields) ** Atrue`。

出口不声称任意入口 `R` 穿过 local free 原样保持；它显式只重建选定记录资源。不是全部 TCB 字段或全部任务的空间保持，也不是既有全部 API 包装根／CurTid／事件数据资源的统一保持。一般等待原因允许 SEM/Q/MBOX/MUTEX 的选定单事件等待；此处的事件位图对应不能替代完整 ECB 数据／等待队列／任务相容不变量。

执行从既有成功更新 AST 开始，经过尾部返回，并非完整外部函数调用、参数分配和所有保护分支。例子 `run / ISR / lock = 1 / 1 / 0`，调度受 ISR 阻挡；不授正常无锁切换信用。初始化、所有 API／ISR、完整共享 Inv、源码级 GOOD_OS 与同程序 K1–K4 均未完成。uC/OS-III 未启动。

## 3. 字面入口与同次终态

新 probe `audit/probes/V293ApiTaskOwnershipProbe.v` 为478行、39,651字节，SHA256 `bcb2f1f6193315b8561b18b8cdcb632b2cc903ac45899e48887ab01defdf6b10`。

实际建立完整权限编码片段、片段到入口内存的 `Maps.sub` 和空间组合。直接重建原始物理入口，调用新一般接口；不调用 `RecordProbeExecution` 等已完成 trace。目标 `(41,8)` 从优先级8→6，仍为同一SEM `(72,5)` 等待、delay1、message `(120,7)`；入口 pend0 的字节位于不变区域。ready16/0不变，event0/1→64/0，旧槽清空、新槽安装目标，返回0、caller emp恢复及locals释放。入口另实际安装 ready 任务 `(60,0)` 的优先级4字段，但本轮联合空间出口不包含所有其他记录或 CurTid。

在上述同次返回结论的实际终态条件下，`ApiRejectsOldPriority` 排除旧8的所有权，`ApiFinalWritePermission` 推出实际 `store` 字节7存在（这是权限测试，不是额外业务修改）。`ApiPermissionMatters` 另保留半权限字节“可读6、不可写7、不具有完整所有权”的语义反例。

## 4. 前瞻单因素负控与对抗性复核

`protocol.json` 在实现前已固定因素。正控重新证明整份899行候选源，不导入候选模块。两项负控只改变一个声明因素，目标整个 `Proof` 后缀逐字不变：

| 因素 | 唯一改变 | 实际结果 |
|---|---|---|
| DroppedPermissionFrame | 目标块字节／权限相等改为 typed-load 相等 | Proof从680行开始，690行拒绝 |
| StaleReturnedPriority | 最终目标记录优先级由new改为old | Proof从853行开始，897行拒绝 |

均 `downstream_credit=false`。拒绝只支持固定证明对该因素敏感，不由早拒绝推出全部下游步骤有效；同次终态的反例和权限测试是独立支持。没有修改白名单、削弱门禁、删除失败或重绑旧证据。

主要反向检查：中间内存是否被偷换成终态；是否仅有读数而无权限；是否重复拥有抽象任务表；任意 frame 是否错误跨释放；是否把受阻调度当正常切换；是否借旧构建身份宣称当前通过。分别由精确块 frame、真实片段重建、抽象／物理空域、明确的 Atrue 出口及范围限制约束。

## 5. 实际检查结果

- `production06` 与 `probe30` 编译成功。所有 production01—05 和 probe01—29 的失败／人工中断及源快照保留，不把中断归类为成功或机器超时。production02 运行期间追加过源，且被人工中断，不授该轮源身份信用；最终 gate 输入在执行期间冻结。
- 13个未改历史 fixture 在当前依赖上重编，全部退出0，见 `fixture-builds.json`。
- `gate01` 实际退出0，8项符合预期：生产、隔离 Positive、新 probe 三次 coqc；两项预期拒绝；生产、probe、Positive 三次独立 coqchk，分别208.12／222.20／209.63秒。196个不同冻结输入保持。4个正控根及5个probe根打印假设并集仅 `Classical_Prop.classic` 与 `FunctionalExtensionality.functional_extensionality_dep`。假设检查器与白名单未改。
- 新增6项测试通过。最终候选旧940项实际324失败1错误；全量946项仍324失败1错误。325个诊断按重数完全相同，见 `all-diagnostic-comparison.json`。
- 与前一检查点的322个诊断相比，旧诊断全部保留，增加3项旧 task-owned-update 的生产 SHA、生产快照和负控全源快照过期检查，已逐条核对 final candidate 的实际 trace，见 `three-added-diagnostics.txt`。开发中间身份的旧测试运行也保留，最终身份另外重跑；不将其他历史失败统称为快照问题。
- 范围审计、冻结源码只读重验、`git diff --check` 通过；默认 `make audit` 仍退出2，原因是 `stale function evidence input identity`。正式六门保持94／1／1／1／1／0，不晋级。
- 增量 `make build JOBS=2` 退出0，仅COQDEP／nothing-to-be-done。本轮没有当前身份 source-only 全量干净构建，旧167源干净构建属于更早所有权源 SHA651b1d1c...。本轮仅授受影响源重编和其依赖闭包独立内核检查信用。

## 6. 清理与下一步

第一次工作树删除前已完整确认70个目标的路径、类别、大小、SHA与保留源／快照，全部验证结束后再次整体核对，再删除：13个fixture依赖产物65项＋新probe产物5项，共8,454,751字节。835个基线 Coq 缓存路径及全部生产可复用依赖保留；不声称重编后缓存字节不变。gate 临时树另按完整manifest清理12项、1,848,550字节；全部成功／失败源快照和日志、源文件、用户数据保留。见 `cleanup-plan.json`、`cleanup-revalidation.json`、`cleanup-result.json` 与 `gate01/temporary-cleanup.json`。

下一步将此选定记录保持接到全部任务记录、当前任务和物理ready／优先级表／event对应的共享资源组合，再推进正常无锁调度、完整 API／ISR 和初始化。不是再增加一个脱离真实执行的小模型。

[中文教学与补全表格](../docs/开发中/成功返回后仍然拥有TCB字段.md)。
