# 阶段26：同一次成功返回的全部任务字段所有权

## 1. 对象、修改和界限

固定目标仍是 uC/OS-II V2.93.01，上游提交 `0c4a48e6fbc6e915714e816196619a5481accf0c`，仅两类已授权 C 修复；只读重验程序身份仍为 `74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da`。手工 AST 与配置后源码的既有对应不是已验证 C 前端、ABI 或端口实现。

唯一追加的生产源为 `certiucos/v293/proofs/V293TaskRecordOwnership.v`：原899行／53,598字节逐字保持，追加336行至1235行／76,317字节，SHA256 `2085d67814b7e720cee8c02873f4184feb63b1944700e562c5fbb22ba011441a`。原前缀 SHA256 `c019819f51fda2b656b8a422d82fd54bcb0c1d629be632b18a7b6c2074002dd2`。不改其他166活动源、12项受保护输入、C/config/port/framework、旧测试／门禁／报告或正式覆盖；仍167源，未提交。

本次结果仅涉及选定字段资源、受阻调度的成功更新与返回。不是完整TCB／链表／分配器所有权、CurTid与全部位图／event联合空间不变量、完整外部调用及所有入口分支、正常无锁切换、初始化或全部ISR。源码级整核GOOD_OS与同程序K1–K4未完成，uC/OS-III未启动。

## 2. 最小证明连接

- `V293_owned_task_records_update`：对实际 `TcbMod.lst` 规范枚举，使用原真实五次store的字段frame，更新目标记录，同时保留整个列表其余资源。排序与实际查找决定规范枚举的更新，不引入另一张任务表。
- `V293_owned_task_records_block_frame`：将入口列表的同一个物理片段整体搬到最终内存。每个实际任务块要求精确 `get` 字节／权限相等；支持集外为空。不是从load或若干独立 `record ** Atrue` 拼出全列表。
- `V293_owned_tasks_fields_reconstruct`：记录拥有空抽象片段，`shared_fields`拥有空物理片段，因此能在同一内存、同一抽象状态联合归还。
- 稳定根 `V293_critical_wait_all_records_owned_execution`：只调用一次既有真实成功返回根，得到同一Mf／Os'／OO'；五赋值模型上的全列表资源与其精确frame连接。出口归还 `(全部记录 ** 更新后的shared_fields) ** Atrue`，保留实际执行、spec_step、ready／priority table／event位图关系。

非目标任务块必须避开真实写集合与local free集合，这一前提明确保留。没有任意R跨释放保持的承诺。没有额外要求所有任务块互异：同目标块的其他任务由精确整块frame和实际store的分离frame处理。字面API实例仅覆盖两个不同块，不授同块API执行实例信用。

## 3. 实际双任务入口与终态检查

`V293AllTaskOwnershipProbe.v` 不复用任何已完成执行定理。它从实际入口重新组合：目标(41,8)优先级8、SEM等待(72,5)、delay1、非空消息(120,7)，以及ready任务(60,0)优先级4、NULL消息。两份真实完整字段片段先证明join及对实际RecordProbeMemory的sub，再作为全列表入口交给新根。

同一次返回，目标优先级6而仍等待，另一任务仍ready／优先级4；ready16/0不变，event0/1→64/0，返回0、恢复caller、释放locals。run／ISR／lock仍1/1/0。独立终态定理排除旧规范任务表的完整所有权，并在同一返回内存分别证明两任务优先级字段可执行实际store；不声称后续任意写仍维护不变量，或执行了第二次API。

开发过程保留production01–08与probe01–14的快照／日志／退出码；没有删改失败以制造通过。probe的块别名rewrite故障用Print-All定位，保留c:block而不是先subst为positive字面值；随后修复局部重名、已有eq_dec接口名及实际map lookup的显式change。临时诊断语句已移出活动probe，失败的诊断快照保留。门禁执行前另纠正新驱动继承来的旧probe kernel目标，回归明确核对新模块身份。详见 `probe-diagnosis.txt` 与前后对抗审查。

## 4. 前瞻消融与验收口径

在实现前冻结 `protocol.json`、899行前缀、167源／12项受保护输入／8746个历史audit/scripts/tests身份与HEAD。两项单因素控制：

| 控制 | 唯一改动 | 保持不变 | 信用界限 |
| --- | --- | --- | --- |
| DroppedOtherTaskFrame | 非目标任务块安全前提改为True | 整个目标Proof后缀及其他输入 | 只按实际拒绝点报告，downstream_credit=false |
| StaleCanonicalTaskMap | 最终完整任务字段资源绑定旧任务表 | 整个目标Proof后缀及其他输入 | 不从提前拒绝授下游信用；同次终态旧表反例另证 |

Positive为隔离完整候选源重证，不导入候选自身模块；假设白名单沿用原辅助检查器，不放宽。真实Production／Positive／Probe编译、两个预期负控拒绝、三个独立coqchk应分别记录，不把一个模块的检查冒充另一个。

本轮实际结果、回归差量、完整输入身份与清理记录见下方验收节及 `audit/logs/stage26-all-task-ownership/`；历史检查点只属于其原身份。

## 5. 实际验收结果

gate01退出0，8项实际检查均符合预期：Production coqc143.03秒、隔离整源Positive148.62秒、新Probe19.53秒；两项负控各退出1；Production／新Probe／Positive独立coqchk各204.63／221.85／205.13秒。冻结197个不同输入，全部保持。4个生产／正控根及4个probe根的假设并集仅classic、functional_extensionality_dep，原白名单未改。

DroppedOtherTaskFrame的目标Proof从1180行开始，实际1216行拒绝，原因是True不能作为非目标任务frame函数应用；StaleCanonicalTaskMap的目标Proof同从1180行开始，1232行拒绝，原因是实际更新表无法与旧表统一。两个整段Proof后缀均未改，均downstream_credit=false；拒绝点以各自完整候选快照行号为准。

14个旧fixture实际按顺序针对当前生产身份重编，全部退出0。新增6项测试通过。旧946项：327失败1错误；全量952项亦327失败1错误，328个诊断按kind/id重数相同，没有通过删除旧测试或改门禁换取绿灯。较上一检查点325个诊断仅增3项旧API-ownership源SHA／生产及控制快照身份检查；原325个诊断全部保留，新增3项trace逐条核对。不能把全部旧失败概括为快照问题。原有error仍是stale function evidence input identity。

范围审计、冻结源码只读重验及diff检查通过。第一次误用不支持的freeze脚本--check参数返回2，该失败与后续无参数只读成功日志均保留。默认make audit仍返回2，正式六门94／1／1／1／1／0不晋级；未重绑历史证据。增量make build返回0，仅COQDEP／nothing-to-be-done。没有当前生产SHA的source-only全量干净构建；旧167源干净构建不可套用当前身份。

75个本轮工作树fixture／probe一次性Coq编译产物共9,262,776字节，在首次删除前完整列出path／category／size／SHA并逐项确认；全部验收后再次重核完整集合，已清理。835个既有Coq缓存路径、生产模块5个可复用产物、全部源与成功／失败证据保留。gate隔离临时树12项另按完整manifest重核清理。文档更新仅前置新检查点，README／VERIFICATION_STATUS旧正文逐字保留，快照与SHA见documentation-baseline.json。

## 6. 下一步与总目标

下一步将CurTid当前任务指针与全任务字段资源在同次执行上联合保持，再统一ready位图／priority table／event的实际资源与关系，推进正常无锁调度、其他入口／API／ISR和初始化可达性。最终仍须固定同一个V2.93.01程序上的源码级GOOD_OS与K1–K4；本步不完成目标，也不提前开展uC/OS-III。入门说明和填好的双任务表格见[中文教程](../docs/开发中/一次返回如何归还全部任务字段.md)。

### 文档与清理后的最终复核

再次执行全量952项，48.69秒，仍327失败1错误；328个诊断与清理前按kind/id重数完全一致，无新增／删除。范围、只读冻结C、默认audit、diff实际退出码依次0／0／2／0。final-integrity.json逐项确认其他166源、12项受保护输入、8746个历史文件、197个门禁冻结输入、HEAD和旧文档正文保持，835个既有缓存路径仍在，75个清理目标仍不存在；不新增证明逃逸，不晋级正式覆盖，不完成总目标。
