# 从真实 C 访问集合补齐物理不变量：第一步

## 1. 现在在做什么

最终目标仍是固定版本 uC/OS-II V2.93.01 的源码级 `GOOD_OS` 与同程序 K1–K4；之后才进入 uCOS3。本页不是宣布目标完成，而是把下一项证明义务定位到真实字段，避免继续堆积互不相接的局部定理。

上一步已在一次优先级变更返回中联合归还选定任务字段、位图、整张优先级表和抽象共享字段。现在问一个更基本的问题：**下一个真实函数需要的字节，现有断言是否确实拥有？**

## 2. 机器清单怎么来的

运行：

```bash
PYTHONDONTWRITEBYTECODE=1 python3 -B scripts/inventory-v293-physical-access.py
PYTHONDONTWRITEBYTECODE=1 python3 -B -m unittest discover -s tests -p test_physical_access_inventory.py -v
```

结果保存在 `audit/physical-access-inventory.json`。默认命令只检查，不改写证据；`--record` 只能首次创建文件。

生成器复用既有冻结源码重建流程：只在自有临时目录中应用两类授权补丁、验证源码和预处理哈希，核对全部函数体／定位身份。然后用 Clang AST 而不是正则搜索识别成员／全局变量访问，用同一固定 32 位分析配置输出结构布局。临时目录文件先列出大小、SHA256，再全体重核和清理。

本次：**94 个函数、12 类结构、1007 个访问点**；其中 read 554、write 297、read_write 110、address 40、unevaluated 6。它们是语法访问点，不是执行次数、内存字节数或证明覆盖率。`sizeof` 中的 6 个点不需要运行时读取权限。

区分两个容易混淆的例子：

- `p->array[i] = x`：修改数组字段的元素。
- `p->pointer[i] = x`：读取指针字段，再修改其指向的内存；**不是修改指针字段本身**。

清单保留每个点的源码文件、行号、预处理字节区间和表达式。`identity` 保留已有函数体哈希及直接调用清单，便于回到精确版本核查。`csrc/repaired/...` 是临时重建的逻辑路径，不表示仓库新增了一份源码 checkout。

## 3. 已填好的 TCB 对照表

固定配置中 `struct os_tcb` 大小为 56 字节。下表偏移由编译器取得；“拥有”只描述现有 `V293_record_layout`，不是该字段所有语义关系或所有 API 保持已经证明。

| 字段 | 字节偏移 | 当前选定字段断言 | 实际直接访问者举例 |
|---|---:|---|---|
| `OSTCBStkPtr` | 0 | 未拥有 | `OS_TCBInit` |
| `OSTCBExtPtr` | 4 | 未拥有 | `OS_TCBInit` |
| `OSTCBStkBottom` | 8 | 未拥有 | `OS_TCBInit` |
| `OSTCBStkSize` | 12 | 未拥有 | `OS_TCBInit` |
| `OSTCBOpt` | 16 | 未拥有 | `OS_TCBInit` |
| `OSTCBId` | 18 | 未拥有 | `OS_TCBInit` |
| `OSTCBNext` | 20 | 未拥有 | `OSTaskDel`、`OSTimeTick`、`OS_InitTCBList` 等 |
| `OSTCBPrev` | 24 | 未拥有 | `OSTaskDel`、`OS_TCBInit` |
| `OSTCBEventPtr` | 28 | 仅事件 wait 分支拥有；rdy／时间等待没有 | `OSMboxPend`、`OSMutexPend`、`OSMutex_RdyAtPrio` 等 |
| `OSTCBMsg` | 32 | 始终拥有（选定字段） | `OSMboxPend`、`OSQPend`、`OS_EventTaskRdy` 等 |
| `OSTCBFlagNode` | 36 | 未拥有 | `OSTaskDel`、`OS_FlagBlock`、`OS_FlagUnlink` 等 |
| `OSTCBFlagsRdy` | 40 | 未拥有 | `OSFlagPend`、`OSFlagPendGetFlagsRdy`、`OS_FlagTaskRdy` |
| `OSTCBDly` | 44 | 仅 wait 分支拥有；rdy 分支没有 | `OSMboxPend`、`OSMutexPend`、`OSQPend` 等 |
| `OSTCBStat` | 48 | 始终拥有（选定字段） | `OSFlagPend`、`OSMboxPend`、`OSMutexPend` 等 |
| `OSTCBStatPend` | 49 | 仅事件 wait 分支拥有；rdy／时间等待没有 | `OSFlagPend`、`OSMboxPend`、`OSMutexPend` 等 |
| `OSTCBPrio` | 50 | 始终拥有（选定字段） | `OSMutexAccept`、`OSMutexDel`、`OSMutexPend` 等 |
| `OSTCBX` | 51 | 始终拥有（选定字段） | `OSMutexPend`、`OSMutex_RdyAtPrio`、`OSTaskChangePrio` 等 |
| `OSTCBY` | 52 | 始终拥有（选定字段） | `OSMutexPend`、`OSMutex_RdyAtPrio`、`OSTaskChangePrio` 等 |
| `OSTCBBitX` | 53 | 始终拥有（选定字段） | `OSMutexPend`、`OSMutex_RdyAtPrio`、`OSTaskChangePrio` 等 |
| `OSTCBBitY` | 54 | 始终拥有（选定字段） | `OSMutexPend`、`OSMutex_RdyAtPrio`、`OSTaskChangePrio` 等 |
| `OSTCBDelReq` | 55 | 未拥有 | `OSTaskDelReq`、`OS_TCBInit` |

因此，不能仅因名字叫 `owned_task_records` 就把它理解成整块 TCB。除字节权限，还要证明这些字节与任务状态、链表、事件、优先级和空闲池的关系。当前状态字段编码也不能直接覆盖所有挂起组合，不能据此宣布 K1 已闭合。

## 4. 不只看表格：实际的 Coq 反例

打开 `audit/probes/V293PhysicalInvariantGapProbe.v`，重点看两个根：

- `SelectedSharedOwnershipHasActualMissingBytes`：复用已有真实空间构造，断言 `V293_shared_task_records` 成立；同一任务表中确实有一个优先级 4 的 ready 任务，但该任务偏移 44 的延时、偏移 20 的 Next、偏移 49 的 pend 字节读取都返回 `None`。
- `SelectedSharedOwnershipDoesNotImplyReadyDelayReadable`：否定“只要选定共享任务所有权成立，ready 任务延时就一定可读”这个普遍命题。

复现这项空间反例：

```bash
/data/home/lucentzhou/.opam/default/bin/coqc -q -R . CertiOS audit/probes/V293TaskRecordOwnershipProbe.v
/data/home/lucentzhou/.opam/default/bin/coqc -q -R . CertiOS audit/probes/V293PhysicalInvariantGapProbe.v
/data/home/lucentzhou/.opam/default/bin/coqchk -silent -R . CertiOS CertiOS.audit.probes.V293PhysicalInvariantGapProbe
```

这重编两个 probe 并检查其序列化依赖闭包，不是全仓 source-only 干净构建。

这里不是用了矛盾入口或 `init := False`：空间断言有显式的满足实例。它也**不是初始化可达性、`OSTimeTick` 实际执行失败、完整联合表断言的反例，更不是 `GOOD_OS` 的反例**；准确结论只是：这一候选断言本身不足以提供该字段。

## 5. 沿一条真实路径继续读：OSTimeTick

按清单中的 `OSTimeTick` 条目读 C 源码（`os_core.c:937–1008`）。函数先经过 tick hook、在临界区增加 `OSTime`，再执行下面的任务遍历：

1. 读取 `OSRunning`，决定是否遍历任务。
2. 从 `OSTCBList` 出发，读任务优先级，遍历到 idle 边界。
3. **先读取 `OSTCBDly`，再判断它是否非零**。不能说“ready 不需延时字段”，因为程序在决定分支前就要完成这个读取。
4. 延时递减为零时，根据 `OSTCBStat` 更新等待结果、挂起相关状态和就绪位图。
5. 读取 `OSTCBNext`，推进遍历。

所以下一条纵向证明至少需要：

| 程序动作 | 应补的入口资源／关系 | 返回时必须交回 |
|---|---|---|
| 读链表头、Next | 头指针与链节点的可读资源；节点对应任务集合、无非法环和结束条件 | 链表结构保持；不能由任务 map 自动推得 |
| 读每个非 idle 节点的 Dly | 不随 rdy／wait 分支消失的延时字段 | 同一节点更新后的延时资源 |
| 改 Stat、StatPend | 对应字节的完整写权限；状态位／挂起／等待结果关系 | 更新字段及状态关系；不把超时等同于立即 ready |
| 改 ready 位图 | ready 行／组完整写权限，与任务集合的对应关系 | 同次最终内存中的位图及关系 |
| 增加系统时间 | 物理 `OSTime` 写权限及与抽象时间的联系 | 更新后的物理时间和抽象时间 |
| hook／临界边界 | 已接受抽象边界的契约和资源转移 | 约定的保存／恢复；不将声明当无副作用实现 |

先补这条路径必需的资源与关系，再将入口、真实执行和返回连接到同一个不变量。初始化也必须产生这些资源，不能只把入口改强后不再证明它可满足／可达。完整事件、队列、标志、内存分区和其他 API 仍需继续覆盖。

## 6. 再看两条路径，防止误判资源回收和切换

- `OSTaskDel`（修复后 `os_task.c:450–566`）还直接修改 `OSTCBNext`、`OSTCBPrev`、空闲链表头、任务计数等；并调用事件／flag 清理与调度。TCB 放回静态空闲池不等于执行框架 `free`，更不等于当前证明中释放局部变量块。三者不能混写成“已经证明删除释放”。
- `OS_Sched`（`os_core.c:1702–1732`）直接更新 `OSTCBHighRdy` 等，并通过 `OSCtxSw` 边界切换。仅看本函数直接访问表，不能漏掉调用者／被调者和切换边界的资源交接；当前 `CurTid` 半份额不能被直接当作完整写权限。

## 7. 清单的边界与下一步

这是**直接语法访问清单**，没有别名分析、指针指向分析、传递调用效果或路径可行性分析。取地址表示后续可能经指针访问，并不代表字段被当前表达式读写；整个结构复制、显式指针解引用和间接调用另列未决点。相同字段名不区分 live TCB、空闲对象和调用者输出缓冲区。全局初始化器、编译器／ABI／硬件正确性不在本清单结论内。

测试分别中和写访问识别、取地址识别，原夹具的相应预期均能识别变化；只给分类器这两项机制信用，不给下游证明信用。真实源码先暴露了 `for (;;)` AST 空槽导致的错误；增加最小回归后修复，失败日志仍保留。

本轮不修改生产 Coq／C、旧门禁、旧测试、覆盖或假设白名单。`GOOD_OS`、初始化和同程序 K1–K4 未完成；默认审计及已有测试失败保持公开。下一步沿上面的 tick 资源缺项推进，不用再回答练习题。
