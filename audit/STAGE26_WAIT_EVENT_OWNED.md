# 等待事件任务改优先级：一般入口与持有任务表的局部配对

## 目标、固定项和身份

入口是同一原始物理内存M、原一般事件完整返回根的全部资源条件，以及同一抽象tasks的table／ready／事件等待位图关系、实际wait成员、`shared_fields ** R` 与外部抽象帧。不要求执行／store／free／spec_step已完成；从物理新槽NULL和入口表关系推导抽象fresh。

`V293CriticalReturn.v` 原5063行／330,382字节逐字保持；追加359行至5422行／353,188字节，SHA256 `6d9acfd12e10f1428681e37f443d377b50af9b6e3e56ac1a26634d3638bac624`。HEAD仍 `1f57743c638c7e1ccdcc594e51dc90c0c7406789`。活动源仍166；其他165源、12项受保护输入和148项历史测试／报告原样保留。固定C／配置／分析端口／框架／正式证据与覆盖不改，未提交。

## 新接口实际做什么

- `V293_wait_prio_step`：仅改优先级，保留完整wait原因、超时、消息；不是完整API规格。
- `V293_wait_prio_owned_step`：读取真正持有的任务表，构造框架spec_prim_step；保持外部抽象帧、eqdom与当前任务字段。
- `V293_wait_test_from_task`：结合任务指针表的同优先级唯一性排除另一个ready任务，才能推出旧ready位为false；不能只从目标wait直接猜测。
- `V293_event_wait_tasks`：一个等待原因的优先级位图与同一任务表wait成员对应；不是ECB等待队列或完整事件不变量。
- `V293_wait_prio_branch_relations`：推导ready两行不变、任务指针表更新、事件等待位图对应同一更新表。
- `V293_critical_wait_event_owned_execution`：实际应用上述owned原语及原一般事件完整返回根；同一Mf上有return0、caller恢复、locals全部释放、TCB五字段／表迁移、ready不变、事件迁移、EventPtr保持和明确物理frame。最终目标仍为原wait而不为任何rdy成员。共享字段运输只给`fields ** Atrue`，不保留任意物理R。

一般根限制等待原因是同一物理事件地址的sem／q／mbox／mutexsem之一。没有读取或约束物理OSEventType，也没有绑定全部物理TCB状态／超时／消息字段。

## 固定probe与前瞻消融

`audit/probes/V293WaitEventOwnedProbe.v` 固定字面原语、事件关系和一般接口。字面程序沿用既有固定probe；不是门禁运行时从候选生成，也不是第二份独立实现证明。

`expected_wait_event_nonvacuity` 在同一原始M构造全部一般入口条件，实际调用新一般contract，不用旧固定execution witness代替。另有优先级4的ready任务、目标wait8→wait6；ready16/0不变，事件0/1→64/0，最终两组字节均为1。运行1／ISR1／锁0，实际调度调用受阻。抽象current选ready4，而物理SELF来源仍为目标；两者尚未一致，因此这个局部非空见证不能称为完整共享合法性或初始化可达见证。

独立语义定理 `expected_wait_stale_event_rejected` 否定“迁移后事件64/0仍对应原wait8任务表”。这与固定Proof敏感性信用分开。

前瞻协议见本轮`prospective-protocol.json`。隔离正控只导入冻结5063行前缀，不导入候选生产模块，完整编译359行追加部分。两项负控各仅改一个出口因子，保留目标完整Proof：

1. WakeWaiter：最终目标get的状态从原wait改rdy；不改tasks的set、其他出口或Proof。
2. StaleEventRelation：只让最终事件位图关系使用入口tasks而非更新tasks。

只授首次固定Proof依赖拒绝信用，全部`downstream_credit=false`；不是修改C、证明变更命题不可证或验证所有下游机制。

## 开发过程与失败保留

- helpers01及old-probe首试：在依赖仍编译、尚无.vo时提前import，失败；不是语义负控。等待依赖终态后重试成功。
- development01：wait-test引理的tactic分支数不匹配。
- development02：Python生成器的反斜线吞掉换行，将conjunction写坏，产生Coq类型错误。
- development03：修生成器时计数断言失败（预估10、实际9），随后编到未更新文件；不授新尝试成功信用。
- development04：conjunction修正后，ready后置let展开导致rewrite找不到目标。
- development05：仅加fold old，隔离完整新增证明通过；随后生产模块实际coqc通过。
- probe01：依赖旧probe尚未成功生成，缺模块；probe02：使用未导入的tid_eq_dec；probe03：Coq模式分支缺空格。分别修导入顺序、改用TcbMod.eq_dec和合法模式语法，未弱化命题。
- probe04编译期间追加了第三个Print Assumptions，日志只打印前两个根；其事后源码snapshot不视作该次精确输入，不授第三根信用。probe05用固定完整probe重新coqc通过，打印全部三个根；正式门禁另冻结完整输入重新验证。
- 两次负控preflight确实在目标Proof内拒绝，仅作开发定位；最终信用以正式门禁日志为准。

源码与全部成功／失败日志、文本快照保留。

## 验证结果

正式 `gate01/result.json` 的12项实际检查全部通过：生产及四个固定probe共5次coqc，生产／新probe／隔离完整正控共3次coqchk，冻结5063行前缀和完整追加后缀共2次coqc，两项负控实际退出1。176项输入身份保持，门禁临时树已按自身清单清理。三个probe根及三个正控根的实际Assumptions并集仅classic与functional_extensionality_dep；语义否定根只依赖classic。没有新增公理或未完成占位符。

两个负控的目标Proof均在350行开始；WakeWaiter在382行 `apply map_get_set` 因wait与rdy不能统一而首次拒绝；StaleEventRelation在381行 `exact FinalEvent` 因旧表与更新表不能统一而首次拒绝。完整Proof保持，见`negative-first-rejection-review.json`，全部downstream_credit=false。

新增8项局部测试通过。全量861项实际270失败1错误；上一检查点853项为268失败1错误。原269个FAIL／ERROR诊断按重数全部保留，只新增两项旧一般ready检查：一项是报告中的5063行生产源SHA与当前5422行源不同；另一项是旧driver在当前完整后缀生成的负控SHA与冻结历史负控SHA不同。逐条原始trace保存在`added-diagnostic-review.json`，没有改旧测试或历史报告来获得通过。

范围审计、固定源码只读核对、增量make与diff通过；增量只做依赖扫描，`Nothing to be done`，不授当前身份全量source-only干净构建信用。默认make audit仍退出2：正式函数证据身份过期。正式六门仍94／1／1／1／1／0；未重放旧完整函数门禁，也未晋级正式覆盖。

逐路径／类别／大小／SHA确认后，清理50个本轮一次性文件，共14,864,046字节：隔离开发树25个（含保留了文本快照的一次性源码和生成器）、工作树新Coq缓存25个。门禁临时树另有自身清单，另计、不重复计入50个。903个基线缓存路径全部保留，不声称字节不变。源码、probe、测试、文档、成功／失败日志、文本快照、历史证据、依赖与用户数据保留。见`cleanup-result.json`。

## 对抗性复核与剩余义务

- 两条轨迹的局部配对不是前向模拟，未覆盖全部中间交错或完整API规格。
- priority-table只是task→slot关系，不是全部槽位、TCB和ECB的完整双射；位图对应不等于所有TCB合法。
- wait位图没有检验物理OSEventType；ECB抽象等待队列及其他事件原因的一致性尚未接入。
- 物理TCB状态／超时／消息与抽象wait的完整绑定、物理OSTCBCur与abstract_current一致性仍开放；人为SELF见证不能充当合法整核入口。
- 抽象外部帧与显式物理frame分别保持；任意物理R不保持。
- 调度仍为ISR阻塞路径，正常无锁切换、准确当前缓存、函数环境／入口分配、ISR/API保持及初始化仍开放。
- 默认正式证据过期仍失败，不递归重绑历史报告／测试来造通过。本轮不授当前身份全量source-only干净构建或旧完整函数门禁重放信用。
- `GOOD_OS` 与同程序K1–K4未闭合；阶段一未完成，uC/OS-III未启动。

中文入门见[等待任务改优先级为什么不会被唤醒](../docs/开发中/等待任务改优先级为什么不会被唤醒.md)。
