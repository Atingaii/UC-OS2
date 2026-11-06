# 第153步：完整 tick while 保持现有 ready／任务／优先级表关系

## 本步解决什么

第152步连接了原完整 while 的实际输出和共享任务表，但还没有说明 ready bitmap 是否与这张表一致。本步复用现有 `V293_ready_rel`／`V293_ready_payload`，将第149步的单节点保持定理提升到整个合法有限链，并在**同一个实际输出内存 Mf** 中封闭任务记录、bitmap和优先级表所有权。不另建平行的不变量或执行关系。

固定目标为 uC/OS-II V2.93.01，提交 `0c4a48e6fbc6e915714e816196619a5481accf0c`。C、配置、冻结 AST、framework、tactics和旧证据不改；不声称重新运行 C 前端。

## 用现有四任务例子理解

四个任务共用同一物理 block 的不同、不重叠偏移；另实际分配13项优先级指针表。入口由具体可写字节构造，再执行原 while，不是假定一个不可满足的前置条件。这只证明入口可满足，不证明由生产初始化可达；沿用的 pend 初值7是用于观察写入的探针字节，不作为生产 pend 枚举状态的可达证据。

| 对象 | 执行前 | 完整 while 执行后 |
| --- | --- | --- |
| 优先级10头任务 | 等信号量，delay=1 | 超时 ready，delay=0 |
| 优先级2第二任务 | 时间等待，delay=3 | 仍等待，delay=2 |
| 优先级4任务 | ready | 不变 |
| 优先级12 idle | ready，链终点 | 不变，不遍历 |
| ready低行 | 16：优先级4 | 16：仍是优先级4 |
| ready高行 | 16：优先级12 | 20：优先级10与12 |
| ready group | 3 | 3 |
| 13项优先级表 | 2／4／10／12项指向对应任务 | 全部实际指针读保持 |
| 当前任务／非空事件表／时钟37／canary99 | 已存在 | 保持 |

超时 ready **不表示收到消息**。冻结 tick 分支写 `OS_STAT_PEND_TO`，并不在此处删除 ECB 等待表；本步没有建立这一事件／pend结果关系。也没有把时钟递增与 while 合成完整函数。

## 证明链与稳定接口

新增 `certiucos/v293/proofs/V293TimeTickReadyChain.v`，稳定接口为 `V293_tick_while_ready_payload`。

1. `V293_tick_binding_ready_rel` 复用第149步 bitmap值、bitmap/task关系及优先级表保持；ready节点不改，等待节点按原倒计时和到期置位计算。
2. `V293_tick_chain_ready_rel` 对任意有限合法链归纳。使用原 `V293_tick_chain_bitmap` 和第152步计算出的任务表，不要求调用方提供正确后态。指针不重复保障后续旧记录仍有效；优先级表关系是额外前提，不能由指针不重复推导优先级唯一。
3. `V293_tick_record_chain_ready_rel` 对接规范旧／新任务表。
4. `V293_tick_while_ready_payload` 调用第152步的原完整 while＋有序抽象任务步；优先级字节只作为不相交 frame 拥有一次，再与同一 Mf 中的记录和 bitmap 联合封闭**既有** ready_payload，并从实际字节导出 ready_loads。

这是无交错片段的端点连接。既有 ready_payload 是有界运行时关系，不等于生产全局 Inv；没有新增 Hoare/API 或 ISR 完成信用。

## 前瞻单因素对照

协议在证明前写入 `audit/logs/stage153-tick-ready-chain/protocol.json`。

- 正例：非空四任务及实际13项指针表的可满足入口，执行原完整 while；同一 Mf 满足新 ready_payload，实际高行读数为20。
- 旧字节解释对照 `RCold_bitmap_control`：保留正确执行和原 Mf，只企图将 bitmap 解释为旧值16。实际高行20与所声称16矛盾；不删堆、不以入口拒绝代替执行后检查。
- 漏置位关系对照 `RComitted_ready_control`：同一正确执行、同一新任务表，仅将高行20换为16；`RCsingle_omitted_bit` 证明13个有效优先级中只差优先级10一位。新表的头任务已 ready，旧 bitmap 因缺此位而不满足 bitmap_tasks。**没有声称改坏的 C 也执行过**；该对照隔离的是执行后关系中的一个 ready 位。
- 独立保持检查：其他共享槽位、ready／idle记录、13项实际优先级指针读与 canary99保持。

## 验证与边界

实际命令、所有失败编译及其源码快照保存在本步日志目录；稳定编译标签、独立假设与 coqchk 检查以 `stable-compiles.json`、`trust.json`、`verification.json` 为准。Python检查只负责身份与接线，不能替代 Coq 语义证明。

本步实测：4个生产根＋9个探针根均编译通过，独立检查321个活动模块＋42个探针模块；`coqchk` 退出0，用时约695秒。假设闭包只有既有 `Classical_Prop.classic` 与 `FunctionalExtensionality.functional_extensionality_dep`。全量构建和新增7项回归通过；1902项全量回归中，旧423失败／1错误的 ID 集合保持原样。清理前先核对8个一次性文件，再删除并恢复原两份缓存；清理后实际重跑构建通过，1902项回归仍是同一旧423失败／1错误。源码、日志、失败快照与可复用 Coq 产物保留。

全量回归必须保留旧423失败／1错误的同一 ID 集合；六门保持94/1/1/1/1/0。旧审计的 stale function evidence input identity 和旧 framework 空白错误不能被本步掩盖。不提交、不推送。

仍开放：挂起／flags及event／pend结果关系，完整 tick 函数与临界出口组合、生产 Inv、初始化 side_condition、活动 ISR、完整 WFIFun、源码级 GOOD_OS及同程序 K1–K4。第一阶段未完成，uCOS3未开始，总目标保持 active。按老师要求，组件或模型证明不得冒充整核实现端到端证明。
