# 第182步：真实 tick 与调度器共用函数环境，明确 CPU hook 的剩余义务

## 本步实际解决什么

第177步已让三个时间 API 与内部 `OS_SchedNew` 使用同一强就绪不变量，但 tick 的内部调用规格还没有安装在那份函数环境。本步不重复 getter/setter 的有限成功轨迹，也不增加另一种 Inv，而是连接原 tick 与原调度器的 body，精确回答：这个局部函数环境距离 `WFFunEnv` 还缺什么？

新增生产文件 `certiucos/v293/proofs/V293TickFunctionEnvironment.v`，稳定接口：

```
V293_tick_scheduler_environment :
  WFFunEnv program spec scheduler local_inv strong_inv
  <-> V293_tick_hook_remaining port
```

这里的等价式在文件列出的明确条件下成立：tick/sched/hook 标识不同、实际局部变量声明无重名、TCB绑定有效且唯一、idle地址上界、真实caller的全局/局部环境、LocalInv可恢复、frame可用于相应规则等。没有把这些条件说成整核已经满足。探针在旧非空物理 fixture 中实际解掉这些条件，不假设整份 `WFFunEnv`。

## 原函数体、同一环境与边界

- `program` 安装原 `V293_tick_function`、原 `V293_OSSchedNew_function`，第三个入口由真实 CPU hook 的候选 `port : option function` 给出。
- `spec` 安装 tick、调度器与该 hook 的实际规格。tick 和调度器的 Hoare 证明都在这个相同 `spec`、相同 scheduler、相同 `V293_time_ready_inv` 与相同 LocalInv 下成立；不是把不同环境的命题并排放在一起。
- `V293_tick_scheduler_known_bodies` 复用已有两份原 body 契约，证明实际入口、参数/局部声明检查，以及真实 `BuildPreI / BuildRetI` 对应的全部 body 义务。没有新增函数体 Hoare 前提来代替它们。
- `V293_tick_hook_remaining` 必须提供实际 `Tvoid` 函数、参数匹配、合法声明、在**同一个完整局部 map 和 spec** 下对所有真实 builder 结果成立的 body 证明。它不是一个空的签名检查，也没有提供空 hook 实现。
- 反向从 `WFFunEnv` 提取同样的真实 hook 义务；正向只把已证的 tick/sched 与这个明确未解义务组合。故本步是残余义务的精确分解，**不是 hook 已验证或整份环境已无条件闭合**。

固定来源仍为 V2.93.01 锁定源码：`Source/os_core.c` 的 tick 为937–1008行，调度器为1751–1776行。整文件、AST、既有规格哈希及逐字节片段复核见日志目录 `source-check.json / source-recheck.json`；C、配置、AST、既有证明和框架均不改。沿用已有临界操作归一化，不新增 C 到 AST 自动翻译正确性声明。

## 具体实例与单因素对照

探针 `audit/probes/V293TickFunctionEnvironmentProbe.v` 使用内部标识2001/tick、2000/sched、2002/hook，以及201/version、202/settime、203/gettime。标识是局部连接参数，不是最终生产符号表。

| 检查 | 保持不变与实际观察 | 不能推导的结论 |
| --- | --- | --- |
| `ENknown / ENenvironment` | 实例化同一强Inv、同一Spec及真实body，旧frame和环境条件实际解掉 | hook已存在或全部94函数已连接 |
| `ENbuilders / ENtick_body` | 同一program下真实tick builder等于旧SN builder，再从新共同环境接口提取原body证明 | 一次完整ISR执行或所有交错 |
| `ENnonempty` | 直接从旧实际 `BHmemory`、`PCabs/PCcode` 和 `BLallocated` 构造SN入口，不调用新环境主定理 | 该物理fixture也同时满足调度器caller，或hook有可执行实现 |
| `ENapi_same_spec / ENdisjoint` | 三API的 `GoodI / WFAPI` 与内部map使用同一Inv/LocalInv/Spec，实际标识不冲突 | 全局初始化、完整内核环境或最终链接完成 |
| `ENmissing_hook` | 只移除hook入口；Spec和原两body不动；`EqDom`及`WFFunEnv`拒绝 | 下游body语义检查有效；这只是domain层拒绝 |
| `ENwrong_hook_type` | 保留入口，返回类型改为Tint32；任意同一decl/body；`EqDom`明确通过但`WFFunEnv`拒绝 | hook的body本身错误；这里隔离的是签名检查 |
| `ENsame_type_control` | Tvoid入口的domain通过，环境检查仍等价于完整hook残余义务 | 只要签名正确就能通过body验证 |

`ENli` 沿用 name-only LocalInv：从实际全局环境信息证明名字事实，用空足迹断言表达；没有增加一个无关私有byte。它**不是生产任务私有资源 LocalInv**。非空见证只覆盖实际 tick 入口；调度器在同一环境下有条件body契约，但不把不同函数前提的各自可满足性拼成一次整核执行。

## 验证、旧失败与当前状态

逐次 Coq 编译保留所有失败日志、非零退出码及对应源码快照；最后稳定生产和探针源码与各自成功编译快照一致。17根假设检查、两个入口及递归依赖的 `coqchk`、实际输入身份检查以本步 `trust.json / verification.json` 为准；不扩大既有允许假设集合，不宣称重新检查了所有历史入口。

新增5项回归；完整基线2068项，增加后2073项。预期且必须保持原423失败/1错误的**完整ID**不变，不能用总数相同代替ID对照。正文定稿后再跑一次全套。旧审计的 `stale function evidence input identity` 与旧六行空白问题不修写成绿灯；实际命令结果纳入本步记录。

README与状态只前插，项目清单只追加。六门仍为 **94 / 1 / 1 / 1 / 1 / 0**，不把新的条件连接授予完整函数或整核信用。不修改任何旧冻结证据，不提交或推送。

**尚未完成：**真实生产hook/ISR、生产LocalInv、完整函数环境和初始化、全并发抽象simulation、同一最终程序的K1–K4及最终源码级GOOD_OS。因此第一阶段仍进行中，uCOS3尚未开始，总目标保持active。后续应解决真实hook/中断入口与生产资源的连接，而不是再新增相似有限路径。

收尾先逐项登记本步临时Trust驱动及产物、缓存备份与新Python缓存，再恢复原lia/nia缓存、删除确认的一次性文件；所有源码、诊断、日志、冻结证据、可复用Coq产物保留。最终实际清理见 `cleanup.json`。

## 本轮实际观测结果

- 稳定生产第7次、探针第11次编译成功，均与成功源码快照逐字节一致；共18次编译，15次失败诊断完整保留。未改旧证明以适配新接口。
- 17根 `Print Assumptions` 检查通过；两个新入口及递归依赖的 `coqchk` 通过（477.01秒）。检查期间579份Coq输入不变；实际假设仅既有 `Classical_Prop.classic` 和 `FunctionalExtensionality.functional_extensionality_dep`，允许集合未扩大。
- 新增5项回归通过；首轮2073项全量测试为423失败/1错误，完整ID与2068项本轮基线及第181步冻结记录逐项相同。此段定稿后进行第二次全量复测，最终实际结果由 `full-tests-final.json / verification.json` 留证，不以文字代替日志。
- `make build`、项目范围审计通过；`make audit`仍因旧 `stale function evidence input identity` 失败；`git diff --check`仍报告旧 `framework/logic/inferules.v` 581–586六行空白。没有弱化检查、改写身份或删除不利结果。
- 清理采用先清单后删除，只处理本步Trust驱动/产物、已恢复的缓存备份和新Python缓存。保留全部验证材料及生产/探针可复用Coq产物，旧用户数据与缓存不删除。
