# 第111步：开启中断的实际TCB调用与失败回滚连接

## 这一步接通了什么

上一步已证明：`OS_TCBInit` 在 `IE=true` 时，能进入临界区读取共享的空闲TCB头；头为NULL则归还资源并返回66。本步把这个标准接口用到实际调用者，而不是直接假定“调用已经执行、err已经等于66”。

新增生产模块 `certiucos/v293/proofs/V293TaskCreateEnabledFailure.v`，稳定接口为 `V293_OSTaskCreateExt_enabled_empty_call_suffix`。它连接：

1. 从七个真实局部变量读取实参并检查类型，经原调用语句调用 `OS_TCBInit`。
2. 用 `calle_rule_lvar` 和真实规格查找，把返回66写入调用者的局部 `err`。
3. 原完整后缀读取 `err`；实际比较决定走失败分支，成功／调度分支的语法没有删除。
4. 真实 `encrit1` 再次进入临界区，从同一个共享不变量**重新借出当前槽位**。
5. 原始赋值把 `OSTCBPrioTbl[prio]` 写为NULL，再以 `excrit1` 归还共享资源，恢复入口的 `IE=true` 及临界栈。
6. 原始 `return err` 返回66；局部参数、全局地址元数据和调用者frame保持。

这是“实际TCB调用＋原完整后缀”的条件Hoare定理，**不是完整 `OSTaskCreateExt` 函数契约**。第109步的预留／Hook片段尚不能直接与本步拼成完整正常前缀；整条路径的资源协议仍须证明。

## 为什么不能假设槽位一直等于RESERVED

退出临界区后，中断或其他执行者可能修改共享状态。不能把之前的 `RESERVED` 物理字节留在开启中断的调用者frame中，再用旧的 `IE=false` 证明套过去。

本步的局部资源池是“只读NULL空闲头＋某个类型正确的当前槽位值＋K”。槽位值是存在量，不固定为RESERVED；真实临界重入时才取得它。退出时用实际NULL写入重新构造同一资源池。调用者在开启中断时不持有这两块字节，返回后也不声称共享槽位仍为NULL。

**关键限制：这个物理池过宽，不能充当生产安全不变量。** 它没有证明槽位属于本次创建者，也没有排除清除已建任务指针。还必须建立预留所有权及并发保持协议，才能把本步提升为生产功能正确性／safety。这里没有通过弱化生产验收门来掩盖该义务，也不增加整函数覆盖信用。

## 同一个规格和不变量的独立检查

`audit/probes/V293TaskCreateEnabledFailureProbe.v` 不导入其他审计探针：

- 构造七实参、err局部、当前任务指针及哨兵的实际字节内存。
- `RBCallerLiteral` 证明调用者前置非空洞；`RBCallerHasNoSharedBytes` 排除头块401和槽位块403的所有字节。
- 实际分离join及 `RBWholeSpatial` 证明调用者与共享资源可以共存；同一个不变量允许NULL及非NULL类型正确槽位，不把两个字面实例说成一次干扰执行。
- 对池的precise、GoodInvAsrt及ISR稳定性给出证明，不新增公理。
- `RBBuilders` 检查原完整TCB函数的七参数／两局部标准 `BuildPreI / BuildRetI`。
- `RBCalleeCheckedSameSpec` 检查原完整TCB函数体；`RBCallerCheckedSameSpec` 检查本步调用＋后缀。两者使用完全相同的有限 `RBSpec` 与 `RBInv`。

这排除了“只有规格查找、没有检查被调用函数”的局部缺口；仍不是 `WFFunEnv / WFIFun` 或初始化可达性证明。本步没有新增该不变量下的字面TCB内部入口证明，不能把第110步不同不变量的入口见证重新贴标签使用。

## 源码身份不变

固定 uC/OS-II V2.93.01，提交 `0c4a48e6fbc6e915714e816196619a5481accf0c`；配置后身份 `74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da`。

| 对象 | 原源码位置 | 函数切片SHA-256 |
| --- | --- | --- |
| OSTaskCreateExt | Source/os_task.c 347–407行 | 7821d8d7f4245bce15ce630e28637bf2a76cccb2f749723a4ecc9fe1959c80f7 |
| OS_TCBInit | Source/os_core.c 2022–2151行 | 2b3efb83723e005c8dbe11603b4d7d1a0abfe110367aa1c38d6bf458e8fa1ee3 |

本轮重算上游checkout的两个切片，均匹配冻结身份。`os_task.c` 整文件因其他函数的授权修复而与逻辑repaired身份不同，不能偷换整文件哈希；本函数切片未变。没有新翻译，没有修改C、配置、框架、原AST或旧证明。临界宏仍处于ADR-0005接受的抽象边界内，不声称已证明具体端口或硬件。

## 单因素物理写入对照

协议在编译前落盘，两组保留同一非NULL输入、指针类型、地址、证明tactic和期望NULL，只改变一行：实际 `store ... Vnull` 或恒等动作 `Some Before`。

两组先完成同一个实际类型化非NULL读取，随后真实写入组通过期望NULL等式，删除写入组仅在最后等式失败。第01／02版在共同输入前遇到求值展开错误，快照和日志保留，仅列为技术尝试，不计语义负例；接受结果由 `controls.json` 指定第03版。

这个对照只说明该次物理NULL写入对观测必要，**不执行整段调用／后缀、不删除encrit／excrit，也不证明所有下游机制或预留所有权**。完整对抗性审查见证据目录的 `adversarial-review.json`。

## 验证状态与后续

本步证据目录：`audit/logs/stage111-taskcreate-enabled-rollback/`。生产proof08、独立probe08及新增六项结构回归已实际通过；全量测试1564项，原有423失败／1错误的ID集合与第110步完全相同。结构测试不代替Coq。

`make build` 通过；`make audit` 仍因原有 `stale function evidence input identity` 退出2；`git diff --check` 仍是原框架第581–586行六处空白问题，输出与第110步逐字一致。不删除旧失败，不重写冻结证据。

独立内核复核及清理的实际结果：

| 检查 | 实测结果 |
| --- | --- |
| 生产定理／独立探针 | proof08／probe08，均exit0 |
| coqchk | 277个活动模块＋1个探针，exit0，约389.8秒 |
| 全部新lemma／theorem假设闭包 | 36根，仅classic与functional_extensionality_dep |
| 旧生产产物 | 1380个全部字节未变；新增5个，合计1385个 |
| 物理store对照 | 第03版实际写入通过，恒等动作仅最终NULL等式失败 |
| 清理 | 完整清单先复核后删除20个本轮临时文件，共531711字节；旧文件零删除，算术缓存恢复 |

清理后的构建及全量测试结果统一见本目录 `checkpoint-report.json`。本检查点仍为进行中；六门保持 **94/1/1/1/1/0**，整核 `GOOD_OS`、同程序K1–K4、生产全局不变量、WFIFun、初始化和非空分配仍开放；uCOS3未开始，总目标active。未提交／推送。

下一步优先解决**同一生产共享池中的预留所有权、跨中断保持及Hook交接**，再把合法NULL分配前缀、实际TCB调用和本后缀接成完整函数契约。不得靠外部Hook改变IE、把旧IE=false契约冒充开启中断路径，或用本步过宽物理池冒充生产安全协议。
