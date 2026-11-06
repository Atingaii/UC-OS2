# 第177步：时间 API 与 tick 使用同一个时间／任务／就绪表不变量

## 解决的实际缺口

之前三API组件的 `V293_clock_components_checked` 使用 `V293_time_shared_inv`，tick 使用更强的 `V293_time_ready_inv`。两者不能因名字相近就直接组合：打开后者获得的 TCB、优先级表、就绪位图必须保留并归还。

新增生产文件 `certiucos/v293/proofs/V293TimeReadyAPI.v`，不定义新不变量、不修改 C 或 AST，建立以下稳定接口：

- `V293_TimeGet_ready_api_contract`：真实 `BuildPreA' / BuildRetA'` 和原 `OSTimeGet` body，在已有强不变量下连接。
- `V293_TimeSet_ready_api_contract`：同样连接原 setter，包括 `saved=0`、临界区内物理写入及合法抽象更新。
- **`V293_ready_clock_components_checked`**：原 `OSVersion / OSTimeSet / OSTimeGet` 三个API、原内部 `OSSchedNew`，共用一个 Spec、scheduler、强 Inv 和 name-only LocalInv，闭合 `GoodI / WFAPI / WFIFun / no_fun_same` 这组局部组件义务。不是把三个不同不变量的定理并列放在一起。

getter在临界区内读取并完成抽象读，恢复同一个强Inv后才退出；返回局部快照，不承诺开中断后全局时间仍不变。setter执行物理写入后，通过已有 `V293_time_set_absinfer` 更新抽象时间槽；其余抽象槽及与同一taskmap绑定的ready payload原样保留。没有把payload扔进可随意删除的外部假设。

name-only LocalInv 的 `GoodI` 从原强Inv的 `V293_time_ready_good` 出发，只重证死亡任务归还空足迹的义务。内部调度器复用原来对任意Inv成立的函数证明，不迁移旧发行版内核证明。

## 固定源码与建模边界

先记录实际 `Source/os_time.c` 中 getter 237–250、setter 267–278 行及整文件哈希，见日志目录 `source-check.json`。沿用 `V293TimeAccess.v` 的原函数体、原抽象动作及 ADR0005 的 `encrit/excrit` 归一化；不是新增CPU端口实现，也不是C到AST自动翻译正确性证明。

## 证据和单因素检查

探针 `audit/probes/V293TimeReadyAPIProbe.v`：

| 检查 | 实际证明内容 | 不能据此推导 |
| --- | --- | --- |
| RAcommon_component／RAactual_entries | 同一具体API表和内部Spec、同一TRinv与LocalInv；四个真实函数入口 | 全部94函数、tick/hook/ISR已安装 |
| RAget_builders／RAset_builders | 真实builder成功及新body级契约；任意调用线程、lg、setter数值 | 初始化或一次完整动态执行 |
| RAcore_nonempty | 从旧独立物理TCB／bitmap／table／clock堆得到强共享core，不调用新API主定理 | APIcaller与强core同时分配的完整联合见证 |
| RAclock_control | 只改实际时钟；ready load仍成立，但强core拒绝 | ready检查有效，必须另测 |
| RAready_control | 复用旧冻结store：只改低ready字节16→32，clock仍n、两bitmap非空且group相同，原强SWINV拒绝 | 新API完整trace或新发现的语义反例 |
| RAget_positive／RAget_wrong_return | 同一实际抽象map，合法返回n，单改37→38拒绝；独立实际clock和ready loads | getter实际执行到返回 |
| RAset_preserves_nonclock_slots | 原合法抽象setter步骤保留全部非clock槽 | 物理setter已经执行或退出临界区 |
| RAargument_controls | getter多参数、setter空参数／非整数由真实builder拒绝 | 下游共享资源验证 |

**非空证据有明确边界**：本步独立构造的是原强core的实际物理见证；未新增完整APIcaller与强core的联合分配见证，也未新增完整API执行trace。抽象步骤、物理load和条件Hoare证据不拼接成一次执行。ready负控实例化旧定理，不作为本步新增反例数量。

## 验证与开放义务

逐次编译保留全部源码快照、非零日志和退出码；编译失败只作诊断。`inferules.dladd` 明确限定实际builder使用的定义，避免与导入的同名辅助定义混淆。机器检查结果见 `audit/logs/stage177-time-ready-api/verification.json`；Print Assumptions和递归coqchk仅重检本步两个入口及依赖，不冒称所有旧入口均已重检。

本步没有修改旧证明、测试、冻结证据或coverage identity。README／状态前插，项目清单追加。保留旧全套测试失败、旧审计identity失败及旧六行whitespace问题，不削弱门。

这是把已有三API组件从弱Inv接到tick已使用的强Inv，**不是完整全局函数环境**。tick的lg化hook规格未安装在本步Spec；生产hook／ISR、初始化、完整生产LocalInv、同程序K1–K4和最终GOOD_OS仍开放。六门仍94/1/1/1/1/0，不授予新增无条件整函数信用。第一阶段未完成，uCOS3未开始，总目标active；不提交／推送。

下一步应补联合资源可满足性，继续对齐生产函数环境、tick／hook与中断表，不能再把时间getter／setter使用不同Inv当作本步未解问题。

## 本次已观测的检查结果

- 生产第8次、探针第5次编译通过，源码与各自编译快照完全一致；共13次编译、11次非零诊断全部保留。
- 25根 `Print Assumptions` 通过；两个新入口及递归依赖的 `coqchk` 通过（296.11秒）；569份Coq输入在检查期间不变。实际仅使用既有 `classic` 与 `functional_extensionality_dep`，允许假设集合不扩大。
- 新增5项回归全部通过；完整测试从2043项增至2048项，仍为423失败／1错误，完整失败和错误ID与本步基线、上一步最终记录相同。正文定稿后再跑全套一次，结果逐项纳入 `verification.json`，不以这段文字代替原始日志。
- `make build`、项目范围审计通过；`make audit`仍以旧 `stale function evidence input identity` 失败，`git diff --check`仍报告 `framework/logic/inferules.v` 581–586六行旧空白问题。不修改旧输入身份来制造通过。
- 清理程序逐项确认本步临时Trust检查文件、已恢复的lia／nia缓存备份与一次性生成脚本后删除；所有源码、逐次诊断、日志、快照及可复用Coq产物保留。实际清理结果见 `cleanup.json`；最终核对后冻结独立证据清单。
