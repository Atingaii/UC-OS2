# 第350步：物理预留槽连接原强就绪返回接口

## 为什么要做

固定`os_task.c:383`先写`OS_TCB_RESERVED`，第392行才调用`OS_TCBInit`；固定`os_core.c:2121`实际将该槽覆盖为新TCB。第349步物理入口要求null，不能把这个不同的堆直接拼接。本步不改固定C、配置、旧证明、原共享谓词或语义。

## 最小连接

- 沿用`V293_priority_hole`：`entries`是逻辑影子，其中选中槽为null，但物理表只拥有其余12槽；选中位置另持真实预留指针。不是让物理预留槽同时成为null。
- `V293_priority_reassemble_frame`只重排现有资源，实际发布后把新指针槽与原hole重组为完整原强表；不复制所有权、不补假设堆。
- `V293_OS_TCBInit_slot_ready_return_under_hooks`复用原任意旧槽的连续初始化／发布／返回执行一次，再用原`V293_init_ready_insert/pack`构造原`V293_ready_payload`。
- 稳定接口`V293_OS_TCBInit_reserved_call_assign_shared_under_hooks`从实参已经求值的`sfexec`入口实际分配九局部、初始化CPU_SR，在同一个`Mr`建立原抽象创建步骤及客户参数实际分配／写入／读取，最后实际执行`err=0`并保留完整物理frame。`clientM`仍是独立客户堆，不冒充内核堆。

## 单因素对照

协议先于源码冻结。字面入口包含优先级12的旧任务记录、优先级11的待初始化TCB、完整其余表槽与哨兵77；真实前缀无hook契约执行到第一hook并实际建立新任务记录。

随后将同一前缀所得堆用作**独立的第一hook返回现场**，正向执行原两hook之间的临界发布语句到第二hook入口，建立完整canonical表、旧／新记录及哨兵。负向只省略发布写入：同一个堆仍读取预留指针，不能满足更新后的原强表。不是入口早拒绝；也不把该独立现场当作第一hook已经实际执行的证据，不授第二hook、返回或commit的闭合可达性信用。

## 明确未完成

- 仍需两个原CPU hook契约；没有编造hook函数体，完整两hook调用入口未构造。
- RESERVED使用ADR0004符号地址，不声称机器地址1或验证前端；ADR0005临界归一化边界保持。
- 此接口局部持完整可写槽，不能代替ADR0009共享池半权限与创建者半权限在临界区重组；完整并发owner／全局ISR不变量仍未连接。
- 真实调用者的预留前缀、栈hook和七实参求值尚未与本接口整体拼接；实参已经求值、当前线程／spec_crt和九块互异新鲜仍是前提。
- 不是完整`OSTaskCreateExt`的TaskSim、OSInit、具体GOOD_OS、同程序K1–K4或uCOS3；不登记`full_target_linked`。总目标保持active，uCOS3等uCOS2整核阶段完成后开始。

## 实测位置

`audit/logs/stage350-reserved-call-shared/verification.json`记录当前实测；编译候选与失败快照全部保留，新增与全量门分开报告，不改旧测试或豁免失败。生产与探针共10根逐项假设检查和递归内核检查；允许集仅原两项。未提交／推送。
