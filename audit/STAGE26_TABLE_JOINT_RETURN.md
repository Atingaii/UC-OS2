# 整表同次联合返回审计

## 验证对象与边界

固定 V2.93.01，上游 `0c4a48e6fbc6e915714e816196619a5481accf0c`，既有两类授权修复和固定配置不变。修复后C身份仍为 `74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da`。本轮只追加 `V293TaskRecordOwnership.v` 的420行，不把其他既有工作树改动算作本轮工作。源码2925行／188211字节，SHA256 `8368f6b6099841d30eef1df0c6ef491c758ec4ceb5e75a2a663aafe086dd1394`。

新根 `V293_critical_wait_table_joint_owned_execution` 只覆盖显式前提下的一次等待任务优先级变更返回。它取一次 `V293_critical_event_return_bitmap_owned` 的同一Mf，构造 `((((CurTid ** selected_task_fields) ** bitmap_bytes) ** full_updated_table) ** shared_fields) ** Atrue`。同一真实内存的剩余片段提供表资源；抽象为空的物理片段再与shared_fields组合。五个辅助根分别证明已拥有cells的块支持、当前／任务／位图片段支持、整表加入现有分割、抽象共享字段组合、更新后指针类型合法性；都被最终根直接或间接使用。

入口新增的是52个真实完整权限字节与显式Forall指针值合法性，不从纯表关系或load推权限／类型。所选任务字段并非整个TCB布局；CurTid仍只读半份额；表的frame保持不表示任意写后语义Inv保持，也不承诺任意R跨local free。

## 实际检查

门禁gate01实际完成24项编译／负控后，被deprecated引理名称警告中断严格假设审计，尚未进入coqchk。失败结果、输入及清理manifest逐字保留；仅把新probe的除法界证明改用lia消除警告，未修改旧解析器或白名单。gate02完整重跑。

- [正式门禁结果](logs/stage26-table-joint/gate02/result.json)：27项，202冻结输入；19旧fixture、生产／隔离整源Positive／新probe重编，两个负控按预期失败，生产／Positive／probe各自coqchk通过。
- 六个生产根和六个probe根的实际Assumptions只含classic及functional_extensionality_dep，未修改旧白名单。
- [前瞻协议](logs/stage26-table-joint/protocol.json)与[执行前第二版绑定](logs/stage26-table-joint/control-binding02.json)。第一版绑定保留但未执行；中和指针条件为True，避免仅因少一个intros参数导致拒绝。辅助根拒绝不提供下游机制信用；旧表控制只替换最终joint表。目标Proof至EOF后缀逐字不变。
- 实际入口包含完整表，不调用旧完成轨迹作为oracle。消费者检验13槽各自store及其余联合资源frame、旧槽／新槽／未触碰槽、旧表被排除、当前／任务／位图仍可取用，以及任务仍wait而非rdy。
- [开发失败与成功记录](logs/stage26-table-joint/)完整保留：probe01参数推断错误，probe02／03类型别名rewrite错误；Waiting最小化红／绿用例定位language.priority与msg别名后只展开这两个别名，probe04通过；probe05使用无警告的除法界证明通过。早期helper／root失败快照也保留。
- [测试对照](logs/stage26-table-joint/test-comparison.json)：新6项通过，旧976／全982／清理后982均346失败1错误，347诊断重数一致。[历史差异分类](logs/stage26-table-joint/historical-test-delta-classified.json)记录原344保留、增加3项旧priority-table身份与快照诊断；未改旧断言或重绑旧证据，不把全部失败统称快照问题。

## 完整性和清理

2505行旧前缀、其他166源、12保护输入、9439历史文件和HEAD保持；最终逐项结果见[最终完整性核对](logs/stage26-table-joint/final-integrity.json)。README与VERIFICATION_STATUS仅前置本检查点，旧正文逐字保持。保留835既有缓存路径，830无关产物字节不变；5生产产物记录本次真实编译／内核检查身份，而不是要求它们匹配旧源码缓存。[生产产物绑定](logs/stage26-table-joint/production-artifacts.json)。

按完整manifest全体重核后删除124个一次性开发／probe产物，共12904278字节；源、成功失败证据与既有依赖保留。门禁自己的临时树已独立按manifest清理。[清理计划](logs/stage26-table-joint/cleanup-plan.json)、[清理结果](logs/stage26-table-joint/cleanup-result.json)。

## 仍开放的义务

范围及冻结C只读检查通过。默认make audit仍exit2，原因是stale function evidence input identity；正式六门94／1／1／1／1／0不晋级，没有当前身份source-only全仓干净构建。本返回与正常切换之间的完整写权限交接、完整物理Inv、初始化、正常无锁调度、所有API／ISR、同程序GOOD_OS与K1–K4仍开放；uCOS3第二阶段未开始。两阶段总目标仍活动，本检查点不记整核完成。

下一步先按真实读写／释放集合列出共享不变量缺项，再连接入口、执行与返回，不以不可满足入口、空初始化或新增公理代替义务。中文逐步说明见[整张优先级表如何与任务位图同次归还](../docs/开发中/整张优先级表如何与任务位图同次归还.md)。
