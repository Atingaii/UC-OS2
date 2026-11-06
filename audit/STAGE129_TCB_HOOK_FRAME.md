# 第129步：修正 TCB Hook 的资源边界

## 必须先纠正的历史结论

第122～128步相关完整 `OS_TCBInit` 条件接口把 `V293_tcb_publication_globals ** R` 放进 Hook 资源，要求其满足 `GoodFunAsrt`。实际定义含 `A_notin_lenv`；框架对此返回 False。因此该前提无法实例化，旧条件定理虽然经 Coq 检查，却不能作为可调用整函数契约。**旧报告的“完整体已连接”只能保留为条件推导记录，不能据此授予实际函数连接信用。**

本步不改写旧源码／证据，也不把 coqchk 通过当成“所有前提可实现”。冻结第128步全部证据在允许的根文档前缀更新之外应逐项不变。

## 从原定义定位原因

前瞻协议在 `audit/logs/stage129-tcb-hook-frame/protocol.json`，红色复现为 `rejected01`：原 `GoodFunAsrt(publication_globals)` 构造失败。生产负定理进一步证明原前提的否定，不只观察一次编译报错。

| 隔离对象 | Coq 结论 | 对应判定 |
| --- | --- | --- |
| `A_notin_lenv` | 不满足 `GoodFunAsrt` | 调用者局部环境依赖是拒绝原因 |
| 仅 `Agvarenv` | 满足 | 全局绑定本身不是原因 |
| owner 半权限与 `Aemp` | 满足 | 半权限本身不是原因 |
| owner 与非空 `FPR` | 满足 | 修正后的 GoodFunAsrt 前提有具体构造 |
| 同一 owner／FPR 加旧 publication_globals | 不满足 | 对照不换 owner、权限或 R |

探针直接展开原构造器，不以新正／负定理作为唯一判定器。额外字面内存提供 owner 半权限与 publication_globals 的同状态分离共存；单因素只加入局部变量93绑定，内存、全局环境和 owner 不变，此时同一 caller frame 被拒绝。环境对照不是全函数执行，也没有证明整个完整入口及其所有假设可同时满足。

## 最小修正

新增生产文件 `certiucos/v293/proofs/V293TCBHookFrame.v`，不改框架的 `GoodFunAsrt` 或 `call_rule`：

1. 第一个 Hook 的资源为 `owner ** R`，第二个为 `R`。
2. publication_globals 与原七参数／两局部所需资源留在调用者 `GoodFrm` frame。并未删除访问全局变量时需要的“不被局部变量遮蔽”条件。
3. 原 allocator、18字段写入、第一个 Hook、优先级槽所有权消耗、第二个 Hook、有限发布和 return0／return66 仍连续使用同一份资源。
4. `V293_OS_TCBInit_site_hook_framed` 重接原完整 AST；`V293_OS_TCBInit_creator_joint_hook_framed` 从第128步同一固定 Inv 推导全部六项借还，不额外假设三套互不相干的池。
5. 独立 `HFSpec` 在两个不同函数标识符提供有具体 GoodFunAsrt 构造的 fpre／fpost；两个原 `scall` 经框架调用规则检查，保留非空 FPR、owner（首 Hook）和 caller frame。这不是 Hook 函数体实现或执行验证，也不以两个独立调用定理代替完整函数连接。

C／配置／原 AST／共享 Inv 未改；这里只改变 Hook 的资源边界，未引入新的抽象或公理。

## 验证与证据

本步实测终态见 `checkpoint-report.json`，稳定源快照见 `stable-compiles.json`；编译失败、原负例、命令启动错误均保留。包装脚本的退出值不能代替子进程 JSON 的 `exit`。新增8项 Python 回归只检查结构和证据身份；Coq 与 coqchk 才检查相应证明项。全量回归与旧失败集合比较，不删除旧423失败／1错误，不降低覆盖门槛。



实测：稳定生产证明 `proof03`、独立探针 `probe08` 均退出0；22个根的假设核对及全部295个活动模块＋15个探针的 `coqchk` 通过。实际假设仅有框架既有 `Classical_Prop.classic` 和 `FunctionalExtensionality.functional_extensionality_dep`，未新增公理。1470个旧生产产物及70个旧探针产物哈希不变；本步共1475个生产产物、75个探针产物。增量构建通过，新增8项回归通过。全量1725项保留423失败／1错误，失败及错误ID集合与第128步完全一致；不能报告全量回归通过。

另一次额外函数检查误启动了 `scripts/check-v293-functions.py` 的临时完整重建，并非原定的 `make audit`。确认其进程树后仅停止该检查的叶编译器，检查器退出1并自行清除临时目录；取消记录、失败日志保留，不计为通过，也不声称完成 clean rebuild。原定 `make audit` 独立运行于 `audit02`，仍因旧函数证据输入身份过期退出2。`git diff --check` 仍只报告与第128步完全一致的旧框架空白问题。

## 仍然开放，不能跳过

- 修正的是明确无法成立的 GoodFunAsrt 子前提，**不是所有完整体假设的联合可满足性证明**。
- 非空分配路径的标准 `BuildPreI`／`BuildRetI` 契约及创建者实际带接收变量调用仍未接通。不能直接沿用旧的私有节点成功规格或空闲头为NULL的失败规格。
- Hook 函数体／函数环境 WFIFun、allocator token freshness、真正全局状态分区／任务映射／ready语义、所有生产 API 与中断保持性仍未证明；不是生产全局Inv。
- 同一实际初始化程序与完整创建者的连续组合、活动ISR入口、整核 GOOD_OS 和同程序 K1–K4 仍未完成；uCOS3未开始。
- 六阶段覆盖仍为94／1／1／1／1／0，旧审计的函数证据身份问题保留；总目标 active，未提交／推送。

下一步先用正确的资源边界建立非空路径标准函数契约，局部变量域事实留在调用者 frame；再连接原创建者调用。每一次声称“函数可连接”，都必须同时检查前提可实例化，不能只检查条件定理能编译。
