# 第128步：同一共享状态接任务创建预留、回滚和完整TCB初始化体

## 前因与本步结果

第127步已从原 `OS_InitMisc` → `OS_InitRdyList` → `OS_InitTCBList` 三次调用的同一份返回内存建立联合物理核心，并消去完整 `OS_TCBInit` 的六项独立借还前提。但任务创建入口还要读取真实 `OSIntNesting`，旧局部后置把这个字节吸收进 `Atrue`，不能事后从中恢复精确的零值。

本步增加唯一必要的资源：真实 `OSIntNesting` 零字节。它与活动任务计数是两个不同的 `Tint8` 槽，不能因为二者初始化都为0就混用。生产文件为 `certiucos/v293/proofs/V293TaskCreateJointShared.v`。

| 稳定接口 | 已连接的原程序行为 | 仍需的前提 |
| --- | --- | --- |
| `V293_OSInit_three_calls_creator_joint` | 三次真实初始化调用，同一 `Mf` 建立扩展核心并保留原caller frame | 实际全局绑定、原始字节所有权、两个真实且不同的Misc槽 |
| `V293_create_joint_initial_enter` | 创建者原 `encrit`，取得所选任意类型化槽及nesting零字节资源 | 合法优先级、caller frame、框架中断深度上界 |
| `V293_OSTaskCreateExt_joint_reservation` | 原RESERVED赋值及 `excrit`；创建者保留半权限，共享池归还同一Inv | NULL分支的已获得资源、caller局部不变量 |
| `V293_OSTaskCreateExt_joint_stack_fragment` | 原预留、退出临界区、真正 `OSTaskStkInit` 调用和返回值写入 | 显式栈Hook规格、参数及资源契约 |
| `V293_OSTaskCreateExt_joint_rollback` | 原 `encrit`／NULL赋值／`excrit`，消耗创建者半权限 | 创建者仍持有预留半权限、caller局部不变量 |
| `V293_OS_TCBInit_creator_joint` | 同一扩展Inv支持原完整 `OS_TCBInit` 函数体，推导全部六项借还 | 两个CPU Hook规格、token freshness、合法参数、返回契约等 |

这些接口使用同一个不依赖所选优先级的 `V293_create_joint_inv`。不是为预留、回滚、分配和发布分别假设四个不变量。任意 `p<13` 与两行发布视图均从原核心派生；没有更改内核C、原AST、框架或权限模型。

## 如何从初始化建立

从原三调用的原始结果中先提取实际nesting槽，再将任务计数槽交给第127步的联合折叠，最后重拼两份资源。显式要求 `tasks<>nesting`，提取nesting后任务计数仍在剩余Misc列表里；不能复制同一字节来满足两个全权限断言。

独立探针 `audit/probes/V293TaskCreateJointSharedProbe.v` 直接使用冻结且未修改的 `V293InitChainProbe` 字面入口：728字节旧TCB、52字节非零优先级表、实际Misc旧值、非空caller及哨兵。任务计数绑定实际1004／块184，nesting绑定实际1002／块182。同一份实际返回内存同时满足执行、扩展核心、所有合法优先级的资源视图及nesting的真实 `load=0`。没有将目标核心或执行结论放到入口假设里。

仍未精确保留的其他Misc／调度字节吸收进 `Atrue`；不能据此宣称完整初始化所有全局语义均已建立。无活动ISR标记限制仍为全false，nesting=0只覆盖合法的非ISR创建上下文；**不是生产全局Inv**。

## 独立物理回滚与单因素对照

另复用第127步独立编码的非空RESERVED字节入口；该内存构造不依赖本步核心。机器检查如下：

1. 同一全权限槽实际拆为owner／pool半权限，再重拼获得完整写权限。
2. 执行真实 `store NULL`，真实 `load` 得到NULL，重新建立原全权限NULL池；所有槽外地址连同权限保持不变。
3. 单因素分支只省略这一次NULL store：起始地址、四个pointer片段、token、权限及槽外内存完全相同；分支执行不提前拒绝，实际load仍为RESERVED而不是NULL。
4. 另有权限控制：只剩共享半权限时仍可读同一RESERVED值，但真实store返回None；不把此早期失败当作省略写入实验或后续Hook正确性的证据。

以上是局部物理写入／权限对照，不是完整创建者、中断交错、调度或非空成功任务创建的执行实例。完整回滚的Hoare接口另外检查原三段语句，不靠单槽实验替代。

## 源码身份、检查与失败留存

前瞻协议在首次生产编译前写入 `audit/logs/stage128-create-joint-shared/protocol.json`。编译的每次尝试保留源码快照、真实子进程退出码和日志；稳定版本由 `stable-compiles.json` 标记，检查点终态以 `checkpoint-report.json` 为准。新增Python回归只检查结构，不替代Coq语义证明。

原 `os_core.c` 与冻结整文件哈希一致。`OSTaskCreateExt` 定位于上游 `os_task.c` 第347–407行：上游整文件和逻辑修补整文件身份本来不同，不能直接比较二者哈希。本步首个检查脚本误作该比较而失败，原脚本快照和失败日志保留；随后分别检查上游文件／冻结修补清单身份，并核对两份已冻结清单记录的该函数原始切片哈希与实际切片一致。没有删除失败或改写旧身份证据，也未声称本步重放修补树、重新运行C前端或自动验证C到AST的对应。

Coq调试还涉及必要的显式导入、列表换序、指针NULL的真实零字节编码和参数推断；未通过版本全部保留，没有补入公理或削弱原函数体。

## 本步实测

| 检查 | 实测结果 | 边界 |
| --- | --- | --- |
| 稳定生产／探针编译 | `proof06`／`probe07`真实退出0 | 全部失败尝试、快照及日志保留 |
| 全活动构建 | 294模块，真实退出0 | 191目标模块＋103框架／策略模块 |
| `Print Assumptions` | 29根检查通过 | 仅既有classic与functional extensionality；不表示开放的函数规格已被实现 |
| 全活动 `coqchk` | 294模块＋14探针，真实退出0 | 不等价于整核目标已闭合 |
| 新增结构回归 | 8／8通过 | 不替代Coq语义证明 |
| 清理前全量回归 | 1717项／423失败／1错误 | 失败与错误ID集合逐项等第127步，没有新增失败 |
| 源码身份复核 | `source-check02`退出0 | 首次错误比较整文件身份的失败仍保留，未重放修补树或C前端 |
| `make audit` | 真实退出2 | 项目依赖检查通过；覆盖检查仍拒绝过期函数证据身份 |

| 清理后全活动构建 | 真实退出0 | 无需重编，原生产产品保留 |
| 清理后全量回归 | 1717项／423失败／1错误 | 与清理前及第127步失败／错误ID集合完全相同 |
| 文本空白检查 | `git diff --check`退出2 | 日志逐字节等第127步，仅既有inferules第581–586行；新增文本另查无尾随空格 |

清理前先登记全部目标的字节数及SHA256，全部复核后才删除本步一次性Trust源／产品6文件，共56213字节；失败快照和日志、1470个生产产品及70个关联探针产品均保留，未删除旧文件，原 `.lia.cache`／`.nia.cache` 已恢复。终态清单由 `verify-checkpoint.py` 独立复核并由 `freeze-checkpoint.py` 冻结，最终结论以 `checkpoint-report.json` 和manifest复核为准；局部检查不改写总目标仍未完成的事实。

## 尚未完成与下一步

本步已经统一这些局部接口的物理共享资源，**尚未把整个 `OSTaskCreateExt` 的九参数／三局部标准契约连接到非空成功分配**。尤其不能直接套用旧空池TCB调用规格：下一步要构造与完整TCB体匹配的 `fpre`／`fpost`，实例化 `call_rule`，再衔接成功／失败返回和调度分支。同一个Inv并不自动等于这些语句已经端到端组合。独立初始化探针的全局名字与完整创建者的全局绑定，也尚未在同一个完整program中连续连接；通用接口允许显式实例化，不代替该连接证明。

- 两个CPU Hook及栈Hook的函数体、WFIFun、allocator token freshness仍开放。
- 空闲／活动／私有节点精确分区及删除保持、全部API保持、活动ISR、任务映射与ready语义尚未闭合。
- 完整 `OSInit` 的交错Hoare证明、剩余初始化与idle/stat创建仍开放。
- 六门94/1/1/1/1/0不提高；旧423失败／1错误与覆盖审计身份问题保留，不宣称全绿。
- 源码级GOOD_OS、同程序K1–K4尚未完成，uCOS3未开始；总目标active，未提交／推送。
