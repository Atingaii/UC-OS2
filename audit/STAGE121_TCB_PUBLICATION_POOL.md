# 第121步：发布体接完整 TCB 字节与计数双向链表

## 目标和当前边界

目标仍为固定配置 uC/OS-II V2.93.01 的源码级 `GOOD_OS` 和同程序 K1–K4，随后再按老师附件推进 uCOS3。本步继续第120步留下的发布段，但**只闭合已进入临界区的实际发布体**；未接原 `encrit1/excrit1`、完整函数体和 `return 0`，不能称为整函数成功或整核完成。

没有修改 C、配置、AST、framework、tactics 或历史证据。六门仍为 `94/1/1/1/1/0`，覆盖信用未提升。

## 本步证明了什么

生产文件：`certiucos/v293/proofs/V293TCBPublicationPool.v`。

1. `V293_tcb_active_payload_layout` 用排列等式核对完整布局：Next、Prev、三个就绪字段和其他字段／填充共同覆盖原节点的56字节，不以只保存链接字段冒充完整节点所有权。
2. `V293_tcb_active_chain n prev head` 是精确长度的有限双向物理链。每个节点有完整类型化 payload、Next 和 Prev；递归保留原尾链及其类型事实，空链要求 NULL。
3. `V293_tcb_publication_pool` 同时持有共享 head、ready group、两行 ready bytes、counter 和长度与 counter 对应的链。`y<2` 保证所选行与 `1-y` 是不同的两行。
4. `prepare` 从真实链表头和完整节点资源导出既有发布体需要的字节视图；`finish` 将原体更新后的字节折回完整新链，旧头 Prev 改为新节点，旧尾链不丢失。
5. `V293_OS_TCBInit_publish_pool_body` 直接组合既有实际 `V293_TCB_publish_body` 的 Hoare 证明；声明只有一个 `InfRules` 结论，没有把发布体正确性再作为 continuation 前提。所选行／group 按原位操作更新，另一行保持不变，counter 与链长度增加1。`n<255` 排除8位计数溢出；不宣称覆盖溢出情形。
6. `V293_tcb_publication_initialized_view` 将前一步真实初始化节点的同一组字节转换为发布输入，不分配新节点、不复制权限。**该视图将部分字段的确切初始值忘却为类型化存在值，不是可逆语义视图。**

入口中断已关闭，`R` 仍需包含 `CurLINV`；没有把关闭中断时私有持有共享池的资源跨过开启中断阶段。

## 具体内存和单因素对照

探针：`audit/probes/V293TCBPublicationPoolProbe.v`。

- 同一物理表示检查四种入口：空／双节点旧链 × 选择 ready row0／row1；字面堆含完整新节点、旧头、旧尾、两行、counter、真实环境绑定、当前任务和调用者 sentinel。
- `PPLiteralInput` 证明这些入口确实可满足；`PPBodyChecked` 在同一实际 AST 上实例化发布体证明，不把空前置或另造 Inv 当实例。
- 对照从同一个完整非空入口出发，先执行真实 `new.Next = old` 的底层 `store`，唯一变化是是否继续执行 `old.Prev = new` 的真实 `store`。所有其他字节及第一次写入不变。
- `PPNormalChainChecked` 证明正常两次写入后的实际堆拥有完整三节点双向链；`PPFinalChainBacklink` 从完整链关系推出旧头的实际 Prev load 必须等于新节点；`PPOmittedBreaksFinalChain` 独立证明省略第二次写入的实际结果不满足该链关系。
- Normal／Omitted 控制源只有 `perform_write` 的 true／false 一处差异。两者先检查共同完整入口与第一次 store，打印 `COMMON_INPUT_CHECKED` 后才检查相同链结论；Normal 通过，Omitted 在该结论处拒绝。拒绝本身不是唯一反例证据，另有上述负向定理。

这是**隔离的两个物理链表写入实验**，不是完整变异 AST 的执行；此实验不改变全局 head、ready 或 count，也不单独验证它们。它们的原顺序和更新由生产发布体 Hoare 证明负责，不能用这一个消融实验给所有下游机制授予信用。

## 验证和清理

全部记录位于 `audit/logs/stage121-tcb-publication-pool/`，终态以 `checkpoint-report.json` 为准。

- 生产及独立探针使用 Coq 8.18.0 完整编译；所有失败尝试、快照和日志保留。开发反馈曾使用临时 `vos/vok` 前缀缓存；该缓存不属于活动工程和最终证据，最终独立全编译与 `coqchk` 不依赖它。
- 对全部新根打印假设；允许项仍限于框架既有的 `classic` 和依赖函数外延性。活动287模块及6个直接探针用 `coqchk` 检查，不等于存在顶层整程序根定理。
- 生产1435个产品、直接探针30个产品保留，旧生产1430个和旧直接探针25个哈希不变。构建是增量检查，不冒充 clean build。
- 新增9项结构测试；清理前后全量1653项的旧423 failures、1 error 保留，失败ID集合与第120步比较，不写“全量通过”。`make audit` 的旧源码证据身份失败及旧 framework 的6行空白问题保留。
- 核对真实上游切片及冻结源码身份；本步没有重放逻辑修补源码树。根 README／状态仅新增前缀，旧正文不改写。
- 清理先列全所有目标的路径、大小、哈希，再对全部目标重核后删除一次性开发缓存、Trust／控制源与产品；恢复原 lia／nia 缓存。保留正式源、所有编译日志／快照、历史文件和交付产品，具体数量见 `cleanup.json`。未执行 Git 提交／推送。

## 尚未完成与下一步

物理链并不是生产任务映射、任务优先级与 ready bitmap 之间的语义不变量；旧节点的字段目前只有类型事实，不能从本步导出它们的调度正确性。第二个 Hook 后的完整节点虽然能转为该输入，仍未接回完整函数体的实际共享池借还。

下一步：在同一个生产 Inv 内实现开启中断入口的动态借池，连接 `encrit1 → 原发布体 → excrit1 → return 0`，并保留七参数／两局部和调用者资源。随后仍需 allocator/token freshness、两 Hook 函数体、标准整函数契约、`Inv/WFIFun`、初始化可达性与顶层 `GOOD_OS`／K1–K4；此前不开展 uCOS3。
