# 第335步：实际TCB字段初始化提供零延时资源

## 为什么补这一段

第334步已经证明实际调度/切换后的一个未到期tick循环步，但链表资源仍是入口fixture，下一ready节点的运行时延时也不能凭空假定。canonical ready记录本身不拥有delay44；“记录对应抽象rdy”与“物理延时槽为零”是两个不同事实。

本步只补可独立核查的最小缺口：沿固定V2.93.01源码模型的18条TCB字段写入，取得实际的delay44=0所有权，再在同一初始化末端堆上执行一次零延时tick iteration。没有修改C、配置、两类授权修复、旧证明、旧测试或历史冻结证据。

## 证明接口和非空实例

| 边界 | 证据 | 具体结果 |
| --- | --- | --- |
| 原始18字段写入 | 复用 `V293_OS_TCBInit_fields_execution` | 旧值可任意；从可写资源导出真实执行，不假设成功store |
| 初始化资源分离 | `V293_initialized_tick_resources` | canonical ready记录7字段、delay44=0、剩余10字段、Next、8个输入槽与原frame均不丢失、不重复占有 |
| 同堆执行接口 | `V293_TCBInit_fields_then_zero_iteration` | 原字段片段终点Mi，同时是后续局部tick片段起点；实际读取、进入临界区、零分支、Next赋值、退出临界区 |
| 正例非空 | `TZactual_init_then_tick` | 复用旧 `InitEntry 11` 有限入口，18个旧字段为Vundef；无额外成功执行/读取前提 |
| 末端资源 | 上述接口返回联合所有权 | scanner变为原Next，delay保持0，canonical ready记录、其他字段/输入/frame保持；除scanner四字节外与Mi逐字节相同 |

保留旧remainder的顺序：只取 `firstn 2 ++ skipn 3` 去掉其中第三项delay44，再把这项单独拥有；不是另建一套TCB布局。指针参数槽被复用为scanner，其他七个参数保留。Next从入口即为显式frame资源，不是执行后补造。

## 事前单因素消融：是否可以省掉运行时零资源

协议 `audit/logs/stage335-tcb-init-tick-zero/protocol.json` 在实现前冻结。这里检验的是资源接口充分性，**不是执行突变初始化器**，也不把提前缺资源拒绝当成后续tick语句正确性的证据。

| 不变量/门 | delay=0候选 | delay=3候选 |
| --- | --- | --- |
| 相同canonical ready记录、priority11、status0、空消息 | 通过完整所有权门 | 同样通过 |
| 相同Next/scanner/canary、写权限、所有其他字节 | 保持 | 保持 |
| 唯一变化：delay44四字节 | 0 | 3 |
| 零延时节点资源门 | `TZzero_gate_passes` | `TZready_record_insufficient` 由实际load矛盾拒绝 |

`TZcandidate_literal` 构造整个有限内存并证明全部槽所有权，`TZcandidate_valid` 对任意delay都成立；`TZsingle_factor_outside` 证明两候选在delay槽之外的所有地址完全一致。候选族只用来反驳“canonical ready记录足以推出delay=0”，不宣称delay=3的候选可由本步初始化轨迹到达。真正的正例执行仍从原 `InitEntry 11` 开始，不从候选族开始。

## 严格边界

- 这是18字段片段，**不是完整OS_TCBInit**、完整任务创建或OSInit全局初始化可达性。
- Next和scanner仍为显式入口资源；本步**不是head/Next的初始化来源**，也没有把第334步的fixture追溯到创建过程。
- 两段执行共享同一Mi，但使用各自续体；不是源码连续调用，**不是合法ISR**，不能伪拼成完整全局轨迹。
- **不是完整OSTimeTick**：没有while guard、全遍历、idle终止、到期唤醒、旧任务恢复、clock/hook/中断返回或缓存同步结论。
- 使用手工源码模型及既有临界区归一化，不是经验证C前端；源码重放核对发行版、配置和两类修复身份，不扩大此信任边界。
- 尚未补齐统一WFInt、任意API/ISR闭包、全局ProgSim、最终GOOD_OS、同程序K1–K4；uCOS3尚未开始，总目标保持active。

## 验证与证据

交付前按反例逐项审查：

| 质疑 | 检验或约束 |
| --- | --- |
| 入口是否偷偷假设成功执行，或没有实际实例？ | 稳定接口只要求环境/值合法与资源；原 `InitLiteralEntry 11` 提供非空实例，成功load/store/轨迹均为结论 |
| 是否从抽象rdy循环推出物理零延时？ | 不做此推导；由18条真实字段写入取得零值；同ready记录但delay3的有限堆给出反例 |
| 提取零槽时是否丢字段或重复权限？ | 原11项remainder只移走delay一项，另外10项和canonical7项、Next、输入/frame在同一分离断言中返回 |
| 单因素对照是否同时修改其他内存？ | `TZsingle_factor_outside` 对任意地址证明，只有delay的四字节可能不同；两个候选的全部资源所有权均构造成立 |
| 负例早拒绝是否证明了后续执行？ | 没有；仅作资源接口充分性反证。后续实际执行由独立的原入口正例证明，不把负例当语句消融 |
| 同堆是否等于完整创建→中断全局轨迹？ | 不等于；明确保留两段不同续体、显式Next/scanner、缺失head/Next来源及合法ISR连接的边界 |
| 是否用了其他版本或前端自动保证？ | 原配置后函数身份逐字节重放；仅手工模型对应，不宣称经验证前端 |

生产文件：`certiucos/v293/proofs/V293TCBInitTickZero.v`；非空实例与对照：`audit/probes/V293TCBInitTickZeroProbe.v`。新增8项回归检查与Coq内核检查分开记录，前者不是后者的替代。

证据目录：`audit/logs/stage335-tcb-init-tick-zero/`。实测结果：

| 检查 | 实测 |
| --- | --- |
| 生产/实例重复编译 | 各两轮PASS，源文件身份前后相同 |
| 增量构建与project-audit | PASS，固定串行构建 |
| 两个原配置后函数源码重放 | PASS：OS_TCBInit、OSTimeTick身份与冻结清单一致 |
| 11根假设检查、递归coqchk | PASS；仅既有classic与函数外延性；895份Coq输入含注册表/临时驱动在检查中保持相同 |
| 新增8项测试 | 两轮均PASS |
| 全量回归 | 两轮均2932项、444失败、1错误；比第334步多8项，全部旧失败/错误身份和顺序相同，无新增失败 |
| make audit | 仍退出2：旧stale function evidence input identity；未改写旧覆盖证据 |
| git diff --check | 仍退出2：旧inferules六处空白，输出与第334步逐字节一致 |

局部证明检查通过，且本步“无新增失败”门通过；**全量回归仍不通过，整核目标未完成**，不把旧444失败/1错误豁免成全量PASS。开发期失败与中断快照全部保留；负例编译本身也通过，不以编译失败充当反例。

逐项留存清理审查后，只删除本步临时Trust驱动/对象和已恢复的缓存备份，共10个文件；4份既有缓存恢复原字节，Makefile保持早于注册表以便下次重生成。306份既有pyc、可复用证明对象、旧源码/测试/证据均保留。未提交/推送。

下一步应沿原OS_TCBInit链表发布语句取得head/Next来源，并在创建/初始化到合法ISR的同一全局轨迹中保留这些资源；不能把本步同堆片段直接替代这条连接。
