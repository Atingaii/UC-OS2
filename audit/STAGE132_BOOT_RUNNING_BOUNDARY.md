# 第132步：真实启动初始化与运行期契约的边界

## 为什么先做这一步

第131步已证明具体纯物理 Inv 无法满足 GoodI。直接加上物理 CurTid 也不能修复启动入口：原 C 在创建 idle/stat 任务之前，已把 OSTCBCur 写为 NULL。启动期间没有正在运行的任务，不能要求所有任务创建调用都具备运行期 CurLINV。

本步不修改 C、固定配置、手工AST、GoodI、CurLINV 或 initst，不增加阶段标签或全局不变式。所有旧失败和冻结证据保留。

## 已检查的结论

新增生产文件 `certiucos/v293/proofs/V293BootRunningBoundary.v`，给出五个根：

| 接口 | 结论 |
| --- | --- |
| V293_null_current_no_CurTid | 实际 current 绑定指向 NULL 时，不可能拥有 CurTid 与任意 frame |
| V293_null_current_no_CurLINV | 同一条件排除任意 li、任意 t 的 CurLINV，不只针对空局部不变式 |
| V293_initst_current_read | 对 initst 所有构造器归纳，完整物理内存的 current 必须读出非空 Vptr，且与抽象 curtid 一致 |
| V293_null_current_no_initst | 实际 NULL 排除任意任务环境、I、li、lg 的 initst |
| V293_fields_no_abstract_frame | 四个抽象槽的分离所有权可阻止非空抽象扩展，不需要物理 CurTid；只涉及 GoodI 的一个义务 |

`initst` 递归构造器合入其他 ready 任务内存时，证明通过真实 memory join 与 load_mono 保留当前指针，不把单任务情况冒充全部构造器。

## 从实际执行得到，不只是假设 NULL

探针 `audit/probes/V293BootRunningBoundaryProbe.v` 复用第49步独立字节入口、非空 caller 和原三次调用执行定理；将 ready initializer 的 current 参数绑定到框架真实标识符 `OSTCBCur=60`，指向同一实际块166。原标识符26保留为未使用别名，不宣称完成整个程序的自动重命名。

`BRActualInitialization` 从原字节内存真实执行 OS_InitMisc → OS_InitRdyList → OS_InitTCBList，得到**同一份返回内存 Mf**上的原始资源、联合物理池、current=NULL、OSRunning=0。再由 `BRBootRejectsRunningEntry` 排除 CurLINV 和 initst。不是靠遗漏全局绑定使其平凡为假。

这三次调用只是 OSInit 的已有片段：没有执行两个启动任务的创建，也不是完整 OSInit／OSStart。

## 前瞻单因素对照和抽象所有权检查

协议在本步生产编译前写入 `protocol.json`，其他代码、入口、地址和字段保持不变。

1. `BRCurrentStoreControl` 执行一次真实 store，将同一 current 字节从 NULL 改为固定 Vptr。新内存可分离出两份 CurTid 读份额，并满足既有空 li 的 CurLINV；省略这次 store 的原内存仍排除任意 CurLINV。`BRReachableCurrentStoreControl` 把它接到同一实际初始化返回内存。
2. 正例目标仍是未分配的首个空闲TCB：此检查刻意只隔离指针／局部断言门槛，**不证明目标是已创建的任务**，不代表 OSStart、initst 或完整 GoodI。其他全局字段和执行片段未更改。
3. `BRAbstractSpatial` 直接构造四个不同 singleton 的抽象所有权，不用 no-extension 定理作为自己的构造判据。`BRBootAbstractOwnership` 将其与真实 Mf 的原始资源分离合并，证明不能再加非空抽象 frame，但仍没有 CurLINV。
4. 其中抽象 curtid 是显式 boot placeholder，不是活任务，也不等于物理 current。空任务／事件映射只是 ghost 构造，不声称三次调用已建立事件内存或运行态 ready 语义。此检查仅说明“完整抽象所有权”与“物理当前任务非空”是不同义务；不是生产语义Inv，也不是 GoodI。

## 源码边界与下一步

固定上游 `Source/os_core.c`：OSInit 582–635 在592/594/596行做三次初始化，在621/623行创建 idle/stat；OS_InitMisc 1389–1418 将 OSRunning 置 FALSE，OS_InitRdyList 1434–1449 将 OSTCBCur 置 NULL；OSStart 869–878 选出最高 ready 任务并设置 OSTCBCur，然后进入已接受的 port 抽象边界。

框架 TopRule 的 side_condition 需要 initst，故源码级 GOOD_OS 的起点应连接到具有已创建 ready 任务和真实 current 的运行边界，而非强套到早期三次初始化返回。已有 V293StartCurrent 的实际 OSStart 前缀证明可以复用，但需要先建立其 ready 任务前提。本步不开始汇编、ABI 或硬件证明。

下一步应沿原启动任务创建实际操作语义建立可达状态，避免把依赖运行期 CurLINV 的标准调用规则强套给首个启动任务；再接 OSStart 和带物理／抽象语义关系的可实例化全局Inv。启动／运行的共享资源衔接、完整 GoodI、Hook／WFIFun、活动ISR、GOOD_OS／同程序K1–K4仍未完成。uCOS3未开始，总目标active。六门94/1/1/1/1/0不变，不授予完整函数可调用信用。

## 验证与证据

日志目录：`audit/logs/stage132-boot-running-boundary/`。生产稳定 proof08、探针稳定 probe07；所有技术失败日志／源码快照保留。新增 Python 回归只检查结构和证据身份，Coq 编译、假设闭包和 coqchk 才是本步定理检查。

完整实测以 `checkpoint-report.json` 与 `verification.json` 为准。旧423失败／1错误和 make audit 的 stale function evidence input identity 问题不删除、不放宽。清理只针对逐项确认的一次性 Trust 文件与已恢复缓存备份，保留生产／探针产物和所有失败证据。未提交／推送。

### 本步最终实测

| 检查 | 结果／边界 |
| --- | --- |
| 生产／独立探针编译 | proof08／probe07 均 exit=0，前后源码与快照SHA相同；7次生产、6次探针技术失败保留 |
| 构建／清理后构建 | 均 exit=0；195目标模块＋103框架／tactics模块 |
| Print Assumptions | 16根，仅原有 classic 与 functional_extensionality_dep，无新增公理 |
| coqchk | 298活动模块＋18独立探针，exit=0 |
| 新增回归 | 8项，两次均通过；不替代 Coq 语义证明 |
| 清理前／后全量回归 | 均1749项、423失败／1错误；失败／错误ID集合与第131步完全一致 |
| 源码身份 | OSInit、OSStart、三次初始化五个准确片段、相关C/config/AST保持原身份 |
| make audit | exit=2，既有 stale function evidence input identity；未降低门槛或删除失败 |
| git diff --check | exit=2，仅既有 inferules.v 行尾空白，输出与第131步逐字节相同；本步交付无行尾空白 |
| 旧文件变化 | 仅 README、VERIFICATION_STATUS 的新前缀、_CoqProject 的一行注册与生成依赖表；旧正文、C/config/AST、框架／tactics、旧产物及冻结证据字节不变 |

清理前逐项登记并再次核对全部目标：删除8个一次性 Trust 源码／产物及已恢复的缓存备份，共682150字节。原有 lia／nia 缓存按基线恢复；没有删除既有文件。生产／探针可复用产物和全部失败日志／快照保留。
