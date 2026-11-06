# 第130步：共享池 OS_TCBInit 接标准函数构造器和真实返回接收变量

## 目标与实际连接

固定 V2.93.01 原七参数、两局部的 `OS_TCBInit` 函数体、C/config/AST、同一个 joint Inv 不变。
新增 `V293TCBSharedContract.v` 将共享池完整体包成 `BuildPreI`／`BuildRetI` 契约，再通过 `calle_rule_lvar` 对接创建者原七个表达式及 `err` 接收变量。
这是保留 GoodI、Fresh 和两项 Hook 查找前提的条件推导，不是完整程序的实际执行或全部前提的联合实例。

- 函数 fpre 只携带全局绑定、抽象操作、中断状态和 owner＋R，不含调用者局部名约束。
- 精确 declaration domain 留在内部函数 frame；由它推出91～96无局部遮蔽，供完整体查找全局变量。
- 内部九个单元全数回收到标准 buildq；不是只证明一段后缀或遗漏局部释放。
- 返回66保持 owner＋R，供失败回滚；返回0只交还R，owner及初始化节点已进入共享池。
- 实际调用者108是栈顶参数，不能与被调者108的TCB局部混淆；调用者七个单元和err单元保留。

稳定接口：`V293_OS_TCBInit_shared_internal_contract`（函数体）和 `V293_TaskCreateExt_TCB_shared_call`（原调用点）。两者采用同一fpre／fpost，仍需在完整program的同一个Spec下连接实现环境。

## 独立检查与单因素对照

`audit/probes/V293TCBSharedContractProbe.v` 直接计算原函数的具体七参数 BuildPreI／BuildRetI；直接展开构造器检查 GoodFunAsrt，不以生产good引理为自身判据；逐分支检查66保留owner、0不额外交还owner、None拒绝，并实例化真实err接收调用。

前瞻协议在首次编译前冻结。类型单因素对照只将top从Vnull改成整数零，程序、规格、formal参数和其他六个值不变：原值类型匹配通过，变体在dl_vl_match及BuildPreI拒绝。这只是参数边界检查，不表示已检查所有下游Hook或发布操作。

## 对抗性复核与限制

不是生产全局Inv，也不是 Hook 函数体／WFIFun 定理。完整体继续显式要求 GoodI、token freshness、两项Hook查找和R的局部不变量条件；**尚未证明这些完整前提联合可满足**。具体builder成功也不等于完整函数前置状态已由生产初始化建立。

Freshness必须是语义状态上的普通Prop蕴涵。不能错误地要求带非空初始化字节的状态entail `[|不别名|]`：框架的纯断言还要求空资源，这将制造新的不可实例化前提。开发中的错误快照保留，最终接口不采用该形式。

最终 Fresh 前件仍未携带真实分配器已知的表成员信息，因此要求比真实路径更强；未证明它对探针的具体 SCReserved 成立。**不能把改成 Prop 就当作新鲜性已经解决**。下一步应在真实分配点保留 NodeMember，从固定标记不在 TCB 表内推出不别名，再与 GoodI、Hook 实现及同一 program 实例联合连接。

完整创建者成功契约、独立初始化和完整创建者在同一program中的连续组合、生产语义Inv、任意活动ISR、Hook实现与最终GOOD_OS／同程序K1–K4仍开放。uCOS3未开始。六门保持94/1/1/1/1/0，不授予额外覆盖信用。旧423失败／1错误与证据身份过期问题不删除、不改写。

## 验证记录

本目录对应日志：`audit/logs/stage130-tcb-shared-contract/`。以最终 `checkpoint-report.json` 和 `verification.json` 的实测为准，不将待运行检查记作通过。源编译失败、源码快照、类型负控制和既有失败集合均保留。

生产源码稳定编译为 proof29，独立探针为 probe02。proof01～28 与 probe01 的技术失败均保留；proof22 因过度展开大不变量而终止，exit=-15，不计通过。信任检查包装脚本首次在启动 Coq 子进程前因探针去重数量断言错误退出；保存 trust-launch-error.json 后将断言纠正为实际16项，未改变证明或放宽假设白名单。

### 本步实测

| 检查 | 结果与边界 |
| --- | --- |
| Coq 8.18 稳定源码／探针编译 | proof29／probe02 均 exit=0，编译前后源码及快照身份一致 |
| 注册后的 make build | exit=0；193目标模块＋103框架／tactics模块 |
| Print Assumptions | 21根；仅 classic 和 functional_extensionality_dep，无新增公理 |
| coqchk | 296活动模块＋16独立探针，exit=0 |
| 新增回归 | 8项通过；不是完整系统端到端测试 |
| 全量回归（清理前） | 1733项，旧423失败／1错误；失败／错误ID集合与第129步一致 |
| 清理后复核 | make build exit=0，新增8项再次通过；全量1733项仍为同一423失败／1错误 |
| 源码身份 | 五个原函数片段、C/config/手工AST身份检查通过；不新增自动前端信用 |
| make audit | exit=2；旧 stale function evidence input identity 保留，不计通过 |
| git diff --check | exit=2；仅既有 inferules.v 空白问题，日志与第129步逐字节相同；本步新增源码／文档无行尾空白 |

最终清理后的构建、回归、清理清单和独立复核结果由本步JSON记录；不通过删除旧失败或改写旧证据制造通过。

清理前逐项登记并复核全部目标的长度与SHA-256，再删除12个本轮一次性文件，共697056字节：临时Trust源码／产物、中间生成片段及已恢复的缓存备份。既有文件未删除，旧lia／nia缓存已恢复；生产与独立探针的可复用产物、全部失败日志／快照保留。
