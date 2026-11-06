# 第151步：原完整 tick while 输出联合任务记录所有权

## 1. 本步解决什么

第150步完成单个等待节点的任务记录重组，但尚未执行下一个节点。本步复用第31步的原完整 `swhile` 执行，连接到第134步的规范任务记录所有权。稳定接口为：

`V293TimeTickWhileRecords.V293_tick_while_owned_records`

它从执行前的可写链表字段、bitmap、idle 优先级、任务额外字段及用户 frame 出发，构造原完整 while 的实际执行。输出只有一个 `Mf`：全部规范任务记录、最终指向 idle 的局部指针、bitmap 与用户 frame 都来自这个内存，而非彼此不相交性未知的若干只读投影。

这是**完整 while 的物理执行／任务记录所有权连接**，不是完整 tick 抽象精化，更不是完整 API、生产 Inv 或整核证明。旧共享任务表槽位尚未按整个链更新；本步不声称建立原 `spec_step`。

## 2. 固定对象与不变项

- 固定 uC/OS-II V2.93.01、上游提交及项目授权的两类补丁；不变更 C、配置、既有 AST、框架、tactics、旧测试、审计门槛或旧证据。
- 复用 `V293_tick_while_owned_execution`，不定义新执行关系或新的循环 AST。
- `OSTimeTick` 上游 `os_core.c:937–1008`，函数行哈希 `71149366f28e0e577e51ccecc2f33cc3866766f11ada105332806af4552e8593`；完整身份见本步 `source-identity.json`。
- 教师附件要求先完成 uCOS2 的方法训练，再进行 uCOS3；附件已阅读。当前不能把任何局部进展表述为两个阶段完成。

## 3. 最小连接机制

绑定是既有 raw 节点与 `(status,message)` 的普通二元组，不引入新执行器或状态机。合法绑定限定为：

- ready：实际 delay／status 为零，prio、Y、X、bitY、bitX 与规范记录一致；
- waiting：time／sem／mbox／q／mutex 的未挂起等待，raw delay 与抽象 delay 相同，优先级小于13，且不是 idle 优先级12；
- 既有 uint32、字节、row／bit 边界成立。

对任意有限合法链，在指针键无重复且所有输入字段联合分离的条件下：

1. 原完整 while 逐节点执行，原链 bitmap fold 决定输出 bitmap；
2. 每个执行后 raw 节点与各自额外字段，重组为一份可写规范任务记录；
3. 递归重组规范任务表，并保留尚未处理节点的全部联合资源；
4. idle 的优先级字段既用于原 guard，也属于其规范记录，**只拥有一次**。输入只另给 `tl (V293_record_layout idle 12 rdy message 0)`，循环停止后才与 guard 的那份优先级字段合并；
5. 输出保留局部指针、bitmap 和任意用户 frame；不再同时声称保留与规范记录重叠的完整 raw 链。

规范任务记录不等于整个 TCB：ready 记录不要求 delay／pend／next 等字段全部属于规范断言。额外 raw 字节可归入 `Atrue`，没有把它们复制成第二份所有权。

## 4. 非空入口和前置注册的单因素检查

协议在实现前写入 `audit/logs/stage151-tick-while-records/protocol.json`。探针使用同一物理 block81 中四个不重叠 TCB 区间，入口由真实规范编码字节构造，不由已完成执行倒推。

| 节点 | 起始偏移 | 初始状态 | 实际 while 后 |
| --- | --- | --- | --- |
| 第一个任务 | 8 | 优先级10，sem 等待，delay1 | ready，原生 timeout 分支 |
| 第二个任务 | 128 | 优先级2，time 等待，delay3 | 仍等待，delay2 |
| ready 任务 | 248 | 优先级4，delay0 | 仍 ready |
| idle | 368 | 优先级12，ready | guard 停止，记录保留 |

初始 bitmap 为 group3、low16、high16；最终为 group3、low16、high20。canary 是另一 block90 的整数99。

- `WhileEntry`：在执行之前证明整个分离资源入口可满足。
- `WhileInitialData`：独立检查初始三个 delay 分别为1、3、0，idle 优先级12；旧第二项记录的 delay 确为3。
- `WhileLiteral`：实际原完整 while 返回，最终指针为 idle，且同一个 `Mf` 拥有全表规范记录。
- `WhileOmitSecondControl`：保持同一实际完整执行和 `Mf`，只把第二任务的抽象记录恢复成旧 delay3；真实字段为2，所以记录关系不成立。不是删堆字节、不是入口拒绝，也不是另一次 mutant C 执行。
- `WhileReadyIdleAndFrame`：同一实际输出中检查头任务到期、ready 与 idle 记录、最终指针和 canary99。
- `WhileNoDuplicateIdlePriority`：独立拒绝 idle 优先级同字节两份完整可写权限。若能分别拥有，写一份12→11会与保留的另一份12矛盾。这项权限反例不冒充可满足入口。

## 5. 编译与验证

生产文件：`certiucos/v293/proofs/V293TimeTickWhileRecords.v`；探针：`audit/probes/V293TimeTickWhileRecordsProbe.v`；身份接线测试：`tests/test_tick_while_records.py`。

本步实际结果写入 `audit/logs/stage151-tick-while-records/verification.json`，该文件生成前不视为检查点已冻结。

- 稳定编译快照：生产 `while11`，探针 `probe03`；旧失败 `while01`–`while09` 均保留。`while10` 是链重组中间成功版本。
- 整数上界编译错误仅归一化 `Int.max_unsigned` 表达式解决；投影范围显式化简；分离资源上的列表拼接用既有 `astar_mono` 和 append 引理，不增加公理、弱化前提或修改 tactic。
- 独立 `Print Assumptions` 检查6个生产根与9个探针根；原有假设白名单不扩大。
- 独立 `coqchk` 覆盖319个活动模块与40个额外探针模块，共359个。
- 新增6项身份／接线检查；全量测试预期保留旧423失败／1错误，必须比较失败标识而不仅比较数量。
- `make audit` 仍在旧 `stale function evidence input identity` 退出；`git diff --check` 仍报告旧 `framework/logic/inferules.v:581–586` 空白。不修改这些基线结果制造全绿。
- 清理先核对每项目标，再移除本步一次性 Trust 产物及缓存备份，恢复旧 `.lia.cache`／`.nia.cache`。源码、失败快照、验证日志与可复用 Coq 产物保留。

## 6. 对抗复核和仍开放的义务

- 有限链定理不是只有四项实例；但它需要合法绑定与联合资源，不证明任意内核状态都满足入口。
- `NoDup` 只约束任务指针键；没有据此推导全局优先级唯一性、事件等待位图或抽象 bitmap 一致性。
- 本步未消费／更新共享 `abstcblsid` 槽位，没有原抽象批量 tick 步，也未给生产 Inv 提供完整开闭接口。不能继承第149步单节点抽象步而声称完整 while 精化已经闭合。
- 不覆盖挂起／flags 表示及事件等待关系；抽象 pend 结果、初始化可达性与活动 ISR 安装仍开放。
- 规范记录涵盖的是原定义要求的字段，不是整个 TCB、编译器／ABI／硬件证明。
- `OSTime++`、运行 guard、循环入口赋值、完整 while、退出临界区仍须连接在同一完整函数／ISR上下文，不能把分别存在的内存或轨迹拼称整函数证明。

下一步：把整个链的前后规范记录与共享任务表槽位、原抽象 tick 转移连接，再与共享时钟和原 tick 尾段组合；随后推进生产 Inv／WFIFun、初始化和 `GOOD_OS` 及同程序 K1–K4。六门仍为94/1/1/1/1/0，不增加源码函数完成信用。uCOS3尚未开始，总目标继续 active；本步不提交／推送。
