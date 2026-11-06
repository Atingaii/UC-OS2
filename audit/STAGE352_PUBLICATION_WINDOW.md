# 第352步：优先级表发布与就绪位发布之间的真实窗口

## 本步解决什么问题

第351步得到带一个栈hook和两个CPU hook返回契约的创建成功接口，不能由此认定每次退出临界区都满足创建完成后的强关系。第118–130步已经具备owner半权限借出、合并、成功写入和归还等组件，本步不重复登记这些成果。

固定 `os_core.c`（SHA-256 见 `source-dependency.json`）的 `OS_TCBInit` 在2118行调用第一个CPU hook；2121行写优先级表，2122行退出临界区，2124行调用第二个CPU hook；2142–2143行才写就绪group和row。这里存在正常的创建中间状态，不是新增内核Bug，也不改C、配置、AST或既有断言。

## 必须分清的两种关系

- `V293_ready_rel` 内的 `V293_priority_table` 只有“任务→表项”的前向约束。旧任务表保留时，空槽被替换为新TCB指针，**原就绪关系仍然成立**；`V293_creation_old_ready_rel_preserved` 是通用正baseline。不能说原ready关系拒绝这个旧map。
- `V293_init_priority_table` 还有“非空表项→任务”的反向canonical约束。新TCB尚不在旧map时，该约束拒绝已发布的新指针。
- 若把新任务按成功返回时的方式插入map并标为 `rdy`，但仍保留旧bitmap，`V293_bitmap_tasks` 拒绝这个新map：其优先级尚无就绪位。

只对比旧map和标准ready插入map，不排除其他过渡态模型。不能据此声称任意全局不变量都不可行，亦不否定第127步的物理joint pool。

## 稳定接口及物理证据

`V293_OS_TCBInit_publication_window` 复用原 `V293_OS_TCBInit_priority_to_second_hook` 的真实执行：从独立的第一个hook返回现场，经实际临界区、slot写入、退出和实参求值，停在第二个hook的 `sfexec`，不执行任一个hook。

该接口在同一个 `Mf` 保留：

1. 新指针已写入的真实优先级槽；
2. 未修改的两行bitmap和group字节；
3. 已初始化的新旧任务记录、其他frame；
4. 更新map的canonical表关系，以及上述两个各自受限的否定结果；
5. 纯粹设置ready位后的正向关系。最后一项**不是**下游ready写入已执行的证据。

`V293PublicationWindowProbe.v` 从独立编码字节构造非空入口：旧任务优先级12，新任务优先级11；旧rows为0、16，group为2；预留槽持真实RESERVED指针；sentinel为77。真实初始化前缀到首hook，随后把该堆作为**独立的首hook返回入口**运行窗口，不偷换为hook实际返回的证明。

`PWActualWindow` 在同一 `Mf` 读取新slot、两row、group和sentinel，保留 `V293_task_records Mf CIRUpdated`。新旧TCB在同一block的不同offset，不依赖整block互异掩盖别名。

## 单因素对照

前瞻协议 `protocol.json` 和补充baseline协议在结果产生前冻结。固定同一物理更新表、旧bitmap、新旧TCB、sentinel，只改变抽象map中是否插入新ready任务：

| 抽象解释 | 原forward ready关系 | 反向canonical | bitmap一致性 |
| --- | --- | --- | --- |
| 旧map | 成立（正baseline） | 不成立：新指针无对应任务 | 仍是原bitmap关系 |
| 插入新ready任务 | 不成立：bitmap子条件失败 | 成立 | 不成立：优先级11未置位 |
| 新map且纯更新row1为24 | 成立 | 成立 | 成立；未声称物理ready写入执行 |

第三行是纯关系正控制，不是另一项实际执行消融。两项拒绝测试针对不同谓词，不将一个早期拒绝当作其他机制有效的证据。编译失败候选仅为技术失败，全部日志和源码快照保留。

## 未解决边界和下一步

- full writable槽的局部执行尚未与ADR0009并发owner、全局强关系以及各API保持性连接。
- 两个CPU hook、栈hook仍没有实现级闭合；没有把调用当无操作。
- 未提供完整创建函数的TaskSim、冷启动OSInit、具体GOOD_OS、同程序K1–K4；uCOS3未开始。
- 下一步需要表示创建中间态，将已初始化但未就绪的记录／槽与已发布任务区分，再检验两次 `excrit` 能否关闭同一个共享不变量；不能把成功返回的最终态关系直接粘到每个中断开放点。

本步只收窄已测得的集成缺口，不改旧证据或全量验收标准。实测结果以本目录关联的 `audit/logs/stage352-publication-window/verification.json` 为准；局部Coq通过不等于整核或全量测试通过。
