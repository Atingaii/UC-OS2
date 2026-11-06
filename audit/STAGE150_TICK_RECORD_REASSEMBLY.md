# 第150步：tick 输出重组规范任务表所有权

## 为什么需要这一步

第149步已经让原 tick 单次循环的实际字段、抽象任务表与 ready bitmap 对应，但不能把两份各自带 `Atrue` 的记录投影直接拼成完整所有权：它们可能占用同一段内存。可读取也不等于拥有可写权限。

本步只补这个连接，不新建执行模型、不改变冻结 C／配置／AST／框架。准确对象仍为 `os_core.c:937–1008` 的 `OSTimeTick` 和已有 `V293OSTimeTick.v`。本步不建立新的 C 前端翻译正确性。

稳定接口是 `V293_tick_wait_iteration_owned_records`。它从一个**联合分离入口**出发，调用第149步原执行接口一次，返回唯一的 `Mf`，同时建立：

1. 原 `V293_tick_iteration` 的实际 `V293_local_steps`。
2. 原 `spec_prim_step` 更新同一任务表槽位；优先级表与 ready bitmap 关系保持。
3. 更新后整个规范任务记录集合的联合所有权。
4. 下一节点指针、新 bitmap、共享抽象字段及任意调用者 `R` 与整个任务记录集合仍以星号分离。

“整个任务记录集合”指 `V293_owned_task_records` 定义的字段，不等于每个 TCB 的所有字段。选中节点的 link、独立 pend 等未被该记录表示吸收的资源留在 `Atrue` 中；没有同时再声明一份重叠的 raw TCB 所有权。

## 最小连接机制

| 接口 | 作用 | 不允许偷换的前提 |
| --- | --- | --- |
| `V293_task_update_enumeration` | 规范 map 枚举等价于更新记录加删除后的其余记录，允许重新排序 | 使用实际有限 map 的唯一性与查找，不假定任意列表没有重复 |
| `V293_owned_task_records_reassemble` | 选中记录与其余记录重组为更新后规范集合 | 必须一开始就在同一个 `record ** (others ** R)` 中 |
| `V293_owned_task_records_focus` | 从规范集合取出任意现存任务，保留剩余集合与 frame | 必须有对应 map lookup；不是新分配权限 |
| `V293_tick_wait_record_after_frame` | 把实际输出字段转换为选中记录，并保留同一 `R` | 不能用第二份 `Atrue` 投影取回 frame |

重用旧 `V293_task_list_member_lookup`，删去重复引理。没有新增 `Inductive` 执行关系、公理或证明洞；生产模块不依赖审计探针。

范围沿用第149步：time／sem／mbox／q／mutex 的未挂起等待、任意 uint32 delay、合法字段边界和当前固定优先级范围。`delay=1` 到期可让任务 ready，但不意味着等待消息成功；独立 pend result 的 API 全链路仍未连接。

## 非空实例与前瞻对照

`V293TimeTickRecordReassemblyProbe.v` 在执行前由 encoded bytes 构造联合入口。两项任务共用物理 block81，偏移分别为8和128；并非靠“两个 block 不等”排除别名。优先级10的信号量等待任务被更新，优先级4的时间等待任务保持 delay5；另有 canary99 和真实下一指针。

该实例没有 idle task，不是初始化可达内核，只验证资源／单次迭代接口可满足。

| 检查 | 不变部分 | 唯一变化或观察 | Coq 结论 |
| --- | --- | --- | --- |
| 两任务联合输出 | 原迭代、两任务入口、同一 `Mf` | 检查规范集合及调用者 frame | 二者联合成立，另一任务 delay 仍为5 |
| 缺失另一任务字节 | 先获得到期实际执行的 `Mf` | 从输出 heap 单独删除另一任务 delay 的首字节 | 完整规范记录所有权不再成立 |
| 重复占用字节 | 同一状态与同一地址 | 假设同一完整 byte cell 可在 `**` 两侧重复拥有 | 更新一侧后两侧分别要求 load5和load4，推出矛盾 |
| 下一节点聚焦 | 同一个联合后置状态 | 取出规范排序中非头节点 Other | 其记录、剩余任务表和 pointer／bitmap／shared／canary frame 仍分离 |
| 调用者及下一指针 | 实际 countdown 单次迭代 | 从联合后置读取 canary 与局部指针 | 分别为99及 Other |

删字节是**实际执行后的关系消融**，不是第二条变异 C 程序执行；重复字节是独立权限反例，不是可达内核状态。没有以入口提前拒绝替代下游机制验证，也没有把聚焦下一任务说成已经执行下一轮。

## 未完成部分与下一步

1. 将原 `V293_tick_while_owned_execution` 的全链 raw 资源与所有节点的记录补充字段连接；避免未来节点的 raw 字段与 canonical 记录重复占用。优先复用该已存在的完整 while 执行，而非新造一条等价执行关系。
2. 原 while 的 idle guard 单独占用 idle 优先级字节；完整任务表若包含 idle，必须拆出并重组该字段，不能把完整 idle 记录再塞进重叠的 frame。
3. 对整条链折叠抽象任务更新与 bitmap 更新，连接同一执行后内存；涵盖 ready、idle、挂起、flags 仍是开放义务。当前 focus 后置不含下一次迭代所需的全部 raw link／pend 字段，不能直接当下一轮入口。
4. 再连接共享时钟、生产 Inv、初始化及 ISR／WFIFun，完成同程序 K1–K4 与源码级 `GOOD_OS` 后，才开始老师要求的 uCOS3。

本步不增加源码函数覆盖信用，六门仍为94/1/1/1/1/0；不提交／推送，总目标保持 active。

## 验证与证据

固定源身份、前瞻协议、全部编译成败快照、实际命令日志及最终只读复核见
`audit/logs/stage150-tick-record-reassembly/`，以该目录 `verification.json`／`checkpoint-report.json` 为准。

| 检查 | 实际结果 |
| --- | --- |
| `make build` | exit 0 |
| 新增身份／接线回归 | 6／6通过；不代替Coq语义证明 |
| `Print Assumptions` | 16根；仅沿用 classic／dependent functional extensionality，无新增公理 |
| 独立 `coqchk` | 318活动模块＋39额外探针，共357个显式目标，exit 0 |
| 全量回归 | 1882项；旧423失败、1错误，失败／错误ID集合与第149步完全相同 |
| `make audit` | exit 2；保留 `stale function evidence input identity` |
| `git diff --check` | exit 2；保留旧 `framework/logic/inferules.v:581–586` 空白；新增文件另查 |

本轮收尾逐一确认8项一次性 Trust 文件／缓存备份后删除，恢复既有 `.lia.cache`／`.nia.cache`；保留源文件、全部成败证据和可复用Coq产物。清理后重新构建及回归，实际结果也纳入最终核对。

旧基线25524个文件逐字节检查；仅追加 README／状态文档、本步活动模块条目及生成的依赖索引。原 C、配置、AST、framework、tactics、旧测试及旧证据均未改写。未消除旧失败，因此不能报告仓库全绿或整核完成。
