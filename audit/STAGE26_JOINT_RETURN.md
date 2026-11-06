# 阶段26：同一次返回联合归还当前指针、任务字段和位图

## 对象与边界

固定 uC/OS-II V2.93.01，上游 `0c4a48e6fbc6e915714e816196619a5481accf0c`，repaired C SHA256 `74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da`；只保留原有两类授权修复。未改 C、config、port、framework、旧测试／门禁／证据、白名单或正式覆盖，未作 Git 提交／推送。工作树包含大量既有修改，不能全归为本轮成果。

实现前 `audit/logs/stage26-joint-return/baseline.json` 冻结167活动源、12保护输入、9118历史文件、835缓存路径和HEAD。唯一活动源改动是 `V293TaskRecordOwnership.v`：原1861行逐字保持，追加351行，现2212行／144244字节，SHA256 `93b194a1496dde4c6d640f0d9e827aa3f14871873397f56a19d8df1c1de0de57`。

仅覆盖优先级调整的选定成功更新／返回路径，调度因 ISR 条件受阻。仍非完整TCB／event／priority table／链表／分配器资源，非完整Inv、初始化可达性、所有API／ISR、正常无锁调度或整核GOOD_OS。手工AST与配置后C、端口归一化仍沿用既有边界；无已验证C前端、编译器或硬件信用。uCOS3尚未启动。

## 本轮闭合的连接

两个独立定理分别得到 `exists Mf`，不能未经证明认定是同一内存。即使内存相同，独立 `P ** Atrue` 与 `Q ** Atrue` 也不蕴含联合分离资源。

- `V293_current_tasks_bytes_joint`：先分离真实当前指针／全部任务选定字段片段，用支持集证明新增字节不在该片段中，借join将实际load和完整权限转到剩余内存；从剩余内存构造联合字节列表，再真正star连接。
- `V293_owned_cells_abstract_empty`：物理字节列表不占抽象资源。
- `V293_current_tasks_bytes_fields_reconstruct`：联合物理资源与只占抽象资源的shared_fields。
- `V293_critical_wait_joint_owned_execution`：入口契约与旧current/all-task执行根逐字相同。只调用一次真实bitmap-return执行根，在其同一Mf／Os'／OO'归还 `(((CurTid ** all_selected_task_fields) ** bitmap_bytes) ** shared_fields) ** Atrue`，保留spec_step、实际执行、loads、精确frame与local释放结论。

五store模型只用于搬运任务片段，不是第二次API执行。字节完整权限来自真实入口与执行保持，不从typed loads反推。指针／任务与位图块分离从原有安全条件导出；current块等于目标TCB块的分支仍用ExactBlock，没有新增全局互异前提。CurTid仍为只读半份额；不承诺任意R跨local free保持。完整表不能从两个槽权限或typed loads推出。

## 字面入口与消费

新 `audit/probes/V293JointReturnProbe.v` 重新构造真实入口资源，调用新根一次，不用旧完整返回trace当oracle。目标 `(41,8)` 优先级8→6，但仍等待SEM `(72,5)`；另一任务 `(60,0)` ready且优先级4；current仍60，ready16/0／group1不变，event0/1／group2变64/0／group1；旧priority槽NULL、新槽指向目标；返回0并释放locals。run／ISR／lock为1/1/0。

七个probe根检查实际入口、联合执行返回、当前指针可读与两个任务字段分别可写、错误current／旧任务规范被排除、联合资源投影消费，以及一次位图store后仍联合持有更新后的空间资源。最后一项只证明权限与空间frame，不证明任意改位图仍满足任务状态一致性或完整Inv；若干独立store存在量词不等于任意顺序的执行。

## 前瞻控制与反驳

`protocol.json` 在实现前冻结两个单因素控制，整个目标Proof后缀不变：

| 控制 | 唯一改动 | 可授信用 |
|---|---|---|
| PointerOverlapAllowed | 删除generic联合构造器的当前指针块分离前提 | 拒绝仅说明固定证明依赖该前提；未证明它逻辑上最弱或必要。 |
| StaleJointEvent | 新执行根最终联合event布局改回旧行值 | 拒绝仅针对该固定证明，不给后续机制信用。 |

两项均 `downstream_credit=false`。隔离Positive包含整份候选源，不导入候选自身代替重证。生产、probe和Positive分别独立kernel检查，沿用原白名单。

开发失败候选及日志全部保留。对完整执行上下文的证明搜索，先用-time副本定位，再仅清理局部无关上下文，未改变定理前提；三次运行按已观察到的具体证明搜索位置中断，不是因静默盲目重启。早期helper的imports／implicit参数／get展开问题保留在development日志。新probe的旧进程句柄恢复后不可用，记录产物和七次假设输出但不猜测退出码；正式门禁重新编译并独立检查。

## 验收状态

gate01失败记录保持：生产／17个旧fixture／Positive／新probe均编译通过，两项负控均实际拒绝，但脚本错误地把负控报错行号与原源文件Proof行号比较；删一行前提后两者偏移一行，严格位置断言失败，尚未进入kernel检查。只把行号计算改为使用负控自身快照，保持 `error_line > proof_line` 与全部其他门槛，然后完整重跑gate02；不将gate01改成通过。最终结果以 `audit/logs/stage26-joint-return/gate02/result.json` 为准，gate02已实际退出0：25项均符合预期，200个冻结输入保持；17个旧fixture重编、生产／整源Positive／新probe编译通过，两项负控拒绝，三个模块各自coqchk通过。Pointer控制负控Proof1874／报错1875；Stale控制Proof2084／报错2210。4个生产根及7个probe根的假设并集仅classic、functional_extensionality_dep，旧白名单保持。三个kernel检查分别213.79／229.70／214.83秒。新增6项测试实际全通过。没有当前身份的source-only全仓干净构建记录，不将增量make的nothing-to-be-done当作该证据。

本轮源码追加后，旧964项测试为339失败1错误，共340诊断；原335诊断按kind与test重数全部保留，增加5项：3项旧bitmap源身份／生产快照／负控快照，2项旧API／current-all测试跨Qed扫描后追加证明的调用计数。没有改写旧测试、删除失败或重绑旧报告；不能把全部340诊断统称为快照问题。详见 `diagnostic-source-delta.json`。

新增测试候选实际6项、2失败：一项正确揭示gate01尚未通过；另一项错误要求生产模块重新编译后仍保持旧产物哈希。保留失败，修正本轮新测试的资源边界：835缓存路径全部保留，830个未重建模块产物逐项哈希不变，5个生产产物绑定本次实际coqc／coqchk并记录新哈希；不恢复过期vo冒充当前证明。另增加负控自身Proof行号回归。没有改变Coq结论或旧测试。

最终旧964与全量970项均339失败1错误，340诊断按kind／test重数完全相同，新增6项通过。范围与冻结C只读重验退出0，git diff检查退出0；默认make audit仍退出2（stale function evidence input identity），正式六门94／1／1／1／1／0保持，未晋级覆盖。

## 清理

120项本轮一次性材料共13315110字节（开发临时树29文件、一次性读取视图1文件、17旧fixture及新probe的90个新Coq产物）逐项记录path／category／size／SHA256，全部重核后才执行任何删除，结果全体不存在。开发候选源码与脚本均已逐字保留snapshot。两次gate临时树各12项分别按完整manifest清理。835既有缓存路径全部保留，830个非生产产物哈希保持，5个有意重建的生产产物以本次编译与独立kernel检查为依据保留新身份；全部用户源／凭据／成功失败证据保留。

清理及文档更新后再次实际运行全量970项：仍339失败1错误，与清理前诊断按重数相同，新增6项全部通过。最终完整性核对见 `final-integrity.json`。

## 后续

先为完整priority table取得真实入口空间资源并证明实际执行保持，再联合其余共享结构；随后推进完整Inv、正常调度、其余API／ISR、初始化与顶层GOOD_OS、同程序K1–K4。两阶段目标仍未完成，保持active。入门表格已填，见[中文教程](../docs/开发中/一次返回如何联合指针任务和位图.md)。
