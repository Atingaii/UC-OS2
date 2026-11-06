# 阶段26：完整优先级表入口所有权与两次真实写入保持

## 固定对象与本轮范围

仍为 uC/OS-II V2.93.01，上游 `0c4a48e6fbc6e915714e816196619a5481accf0c`，repaired C SHA256 `74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da`。两类授权修复、配置及信任边界均不变；未改 C/config/port/framework、旧测试、旧门禁、白名单和正式覆盖，未提交或推送。工作树包含大量既有修改，不能全算本轮成果。

`audit/logs/stage26-priority-table/baseline.json` 冻结167活动源、12保护输入、9291历史文件、835既有缓存路径和HEAD。唯一活动源改动为 `V293TaskRecordOwnership.v`：原2212行逐字保持，追加293行至2505行／159232字节，SHA256 `4fa7487a69950b0864d1941abc34297aa8476309b99587ff284df7c9e003e63d`。其他166源不变。

**本轮只完成整表的必要基础，没有完成整表与旧 API 同次返回资源的连接。** 完整TCB/event/链表/分配器、共享Inv、初始化、其余API/ISR、正常无锁调度、GOOD_OS及同程序K1–K4仍未闭合，uCOS3未启动。没有当前身份的 source-only 全仓干净构建。

## 实际完成的证明

- `V293_full_pointer_cell_owned`：从真实四字节完整权限、类型有效值与typed load构造指针空间片段；编码／解码往返显式证明。逻辑上的 `freeb` 用于分离片段，不是额外的程序释放。
- `V293_priority_cells_from_full_bytes`：递归从同一实际内存分离全部指针。用头片段支持集证明尾部读取不变，再把尾部完整权限和loads运至剩余内存；不是拼若干独立存在量词。
- `V293_full_priority_table_entry`：13槽、52字节完整权限、全部typed loads及显式 `Forall` 指针类型前提，得到整表所有权。纯任务到表关系不能自行推出所有槽类型有效。
- `V293_full_priority_table_two_stores`：M1、M2是输入的实际两次store结果，通过确定性与构造结果对齐，归还更新后的全部13槽及任意frame R。只对这两个store保R，不承诺R跨local free。
- `V293_full_priority_table_loads`：从整表空间资源导出13槽读取。
- `V293_full_priority_table_any_slot_store`：每个合法槽可作一次类型正确的写入并保留整表和R；不是任意写保持完整共享Inv。

新增 `V293PriorityTableOwnershipProbe.v` 从真实字面52字节构造入口：p4指向任务60；p8指向任务41、偏移8；p6和其余槽为空。先清p8再写p6，在同一个M2中归还整表。未改p4保持，旧表被排除。任意槽可写分别从共同终态出发，不冒充连续13次写入。

反例另证：半份额表13槽可读但slot0的store失败；旧稀疏fixture只给两个槽完整权限，不能推出整表52字节条件。本探针不证明任务状态或初始化可达；上一检查点的SEM等待任务不会因改优先级自动ready。

## 前瞻控制与对抗审查

原 `protocol.json` 的完整同次API返回主题仍开放；`control-binding.json` 在负控执行前明确绑定本轮实际完成的构造器与two-store根，不改原协议、不追认完整主题已完成。

| 控制 | 单因素变化 | 实际结果及边界 |
|---|---|---|
| ReadOnlyTableBytes | 构造器的W4改为同地址四个半份额字节；保留类型、load和Proof后缀 | coqc退出1；Proof2274，报错2276。证明拒绝只定位此完整权限依赖。 |
| StaleFullTable | 两次store后结论的updated entries改回原entries | coqc退出1；Proof2448，报错2459，真实AfterFinal与旧表不匹配。 |

两项整个Proof后缀保持，`downstream_credit=false`。不从提前拒绝声称后续API或整核机制正确，也不声称固定证明依赖就是逻辑最弱前提。开发期间的imports、编码、get展开和probe候选失败全部保留于development日志／快照，未删除不利结果。

## 验收与未通过项

正式 `gate01/result.json` 实际退出0，26项符合预期，201个冻结输入保持。生产源、18旧fixture、隔离整源Positive和新probe编译通过，两个负控按预期拒绝；生产、probe及Positive各自 `coqchk` 退出0，分别216.96／218.66／217.42秒。6个生产根及6个probe根假设并集仅 `Classical_Prop.classic`、`FunctionalExtensionality.functional_extensionality_dep`，旧白名单未变。临时gate树12项已按manifest清理。

新增6项测试全部通过。旧970项与全量976项均343失败1错误，344诊断按kind／test重数相同。相较上一检查点340诊断全部保留，增加3项旧joint-return源身份／生产记录／负控快照诊断，以及1项旧测试跨Qed扫描到新追加证明的 `exists Mf` 计数诊断；原2212行未变。**不能把全部344诊断统称为快照问题。** 未改旧测试或重绑旧证据，详见 `historical-test-delta-classified.json`。

范围审计与冻结C只读校验退出0；默认 `make audit` 仍退出2：`stale function evidence input identity`。正式六门94／1／1／1／1／0不晋级。最终文档／清理后复验和完整性记录另见本轮 `post-cleanup-all-tests.json`、`test-comparison.json`、`final-integrity.json`；这些文件以实际执行结果为准。

## 清理与后续

一次性开发材料18项及19个probe的95项新Coq产物，共113项／12021123字节。临时源码先保存快照，完整manifest逐项记录path／category／size／SHA256，并在任何删除前全体重核；删除结果全部不存在，开发临时目录已移除。835既有缓存路径保留，其中830个无关产物哈希不变，5个有意重编的生产产物绑定本次真实coqc／coqchk身份；源码、用户数据和全部成功失败证据保留。

下一步在API同一个Mf中取得完整表资源，并从当前指针／任务／位图片段的剩余内存分离它，再真正联合shared_fields；不能拼两个独立exists Mf或两个可能重叠的 `P ** Atrue`。之后继续完整Inv、正常调度、其他API/ISR及初始化，先闭合uCOS2再做uCOS3。两阶段目标保持active。

入门说明与已填表格：[为什么两个优先级槽可写，还不等于整表可写](../docs/开发中/为什么两个优先级槽可写还不等于整表可写.md)。
