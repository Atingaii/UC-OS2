# 第146步：两 API 与一个内部函数的共同证明环境

## 本步解决什么

此前各函数有各自的契约，但完整顶层框架需要同一个程序表、规格表、scheduler、Inv 和 LocalInv 上的证明。本步不再增加调度轨迹实例，而是把已有三个函数向该接口连接：

| 函数 | 本步的角色 | 实际连接 |
| --- | --- | --- |
| `OSVersion` | API | 合并 API 表中的真实 `BuildPreA'`／`BuildRetA'`，不是单函数表的构造器 |
| `OSTimeSet` | API | 与 OSVersion 共用 API 表及内部 Spec，复用原临界区／时间共享证明 |
| `OS_SchedNew` | 内部函数 | 从原 WFFunEnv 投影原框架 WFIFun；不假设该函数体正确 |

生产文件：`certiucos/v293/proofs/V293ComponentLink.v`。
独立探针：`audit/probes/V293ComponentLinkProbe.v`。
稳定总接口：`V293_components_checked`。

`V293_component_WFAPI` 对总 API 表中的每个绑定分类，用同一张表的实际构造器等式分别调用两份已有契约。`V293_WFFunEnv_top` 只是删除声明良构性这个额外合取的薄适配，**该适配本身不算新增函数体证明**。

总接口同时给出原框架的 `GoodI`、两 API 的 `WFAPI`、一个内部函数的 `WFIFun` 和 `no_fun_same`。所用 invariant 是已有 `V293_time_shared_inv`，LocalInv 是已有 `V293_time_names_li`；所有函数共用同一个 Spec 和 `V293_scheduler`。另有原 `good_os_pu` 的语法条件及 `pumerge` 中三个实际绑定。

## 排除空表与空前置条件

独立探针将三个 fid 固定为 201／202／200，直接检查合并后确有三个不同的函数体。

不仅检查 builder 可以返回 `Some`，还构造实际状态满足内部 builder 的完整入口断言：保持已有非空 ready 位图／解码表／当前指针／局部 y 内存，给全局环境增加时钟名称绑定，采用**与总接口完全相同的 LinkLI／LinkSpec**。不是用旧 empty LocalInv 的 witness 代替新 LocalInv，也不把 `s |= pre` 当作前提。

这个 witness 是空间可满足性，不是初始化可达性，也没有声称该状态满足完整 `INV`。本步没有另外证明两个 API 的完整入口与初始化状态同时可达。

## 前瞻消融

协议在实现前保存于 `audit/logs/stage146-component-link/protocol.json`。

只把内部调度函数 fid 从独立编号移到 OSVersion 的 fid，其余函数体、API 表和 `pumerge` 规则保持不变。`V293_component_collision_shadows_internal` 在原左优先合并语义下证明：实际查到 OSVersion，而不是调度函数。此消融仅检查**实际符号解析**；没有把入口遮蔽或提前拒绝当作下游调度／返回路径成功。

API 域一致性并不要求两个 fid 不同，因此已删除该引理中的冗余不同名条件。三个目标绑定同时存在才要求 fid 两两不同；该条件保留在实际链接定理中。

## 验证记录与边界

本步有16个新 Coq 根（含局部适配与 witness 辅助引理），6项身份／结构回归。编译试错日志、稳定源码快照、独立假设闭包、coqchk、构建、全量测试和逐文件身份比较均保存到本步日志目录；实际通过状态以该目录 `verification.json` 为准，不能把计划当作结果。

没有修改 C、配置、已有 AST、框架、tactics、旧证据或旧测试。没有为了消除旧423失败／1错误而删除或改写它们；本步要求旧失败 ID 集合及数量不变。`make audit` 的 stale function evidence input identity 是另一个未解决问题，本步不重写旧报告把它变成通过。没有增加函数覆盖信用，六门仍为 `94/1/1/1/1/0`。

**这是三函数组件，不是完整生产程序的 WFIFun，也不是 GOOD_OS。** 原顶层 `verified_os'` 仍需要完整 API／内部函数／ISR 表和真实初始化的 `side_condition`，以及整个任务生命周期 invariant。name-only LocalInv 和时钟 GoodI 不是完整生产 Inv。没有引入假初始化、空 ISR 来拼一个无关的 GOOD_OS，也没有消除 cache 同步缺口或修改端口。

源码对应性仍沿用已有人工 AST／受限前端证据；本步不是新增的完整 C 前端验证，不将三个组件直接记为三个已验证源码函数。同程序 K1–K4 和完整源码级 GOOD_OS 尚未完成，uCOS3 未开始，总目标仍 active。未提交／推送。

## 下一条实际证明链

下一步应继续把真实函数加入同一完整程序环境，并满足 API／ISR 与任务生命周期资源的共同 invariant；不能把本步的一函数 WFIFun 偷换为完整内核的 WFIFun。调度完整函数入口／切换后 invariant、初始化 side_condition 和统一源码身份依然是待闭合义务。
