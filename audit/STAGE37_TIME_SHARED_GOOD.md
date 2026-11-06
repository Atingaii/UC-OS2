# 第37步：同一个共享时间不变式的 GoodI 与切换保持性

## 本轮实际改变

新增 `certiucos/v293/proofs/V293TimeSharedGood.v`，只追加这一生产模块到 `_CoqProject`。上一轮 `V293TimeShared.v`、getter AST、固定 C／配置／端口、旧证明／测试／证据均保持。`V293_time_switch_core` 等仅为同一断言的重排视图；没有换成另一个更弱的 IRQ Inv。

稳定接口：

- `V293_time_shared_good`：对任意时钟块 bn，证明 **同一个** `V293_time_shared_inv bn` 满足框架 `GoodI`，调度器使用已有 `V293_scheduler`，局部不变式使用显式空 fixture `V293_shared_li`。没有套用旧共享 Inv 的 GoodI。
- `V293_time_owned_switch`：从当前任务指针的写权限及共享字段所有权，**推出存在**实际成功写入的 Mf；在同一个 Mf 重建新任务的 SWINVt，读回新当前任务指针、未变的物理时钟，并核对抽象 current／任务表／事件表／时间四个槽位。入口没有成功 store 或执行 oracle。

具体步骤是：打开原 Inv → 两个 CurTid 读半权限合并 → 保留时钟为真实空间 frame 执行指针 store → 只替换抽象 curtid → 原时钟见证不变地分裂权限并关闭同一个 Inv。不是仅证明“抽象更新时间后还成立”。

## GoodI 的四项义务

| 义务 | 本轮连接 |
| --- | --- |
| 抽象资源穷尽 | 从扩展核心忘掉物理时钟，复用四槽位穷尽证明，不能另拼抽象 frame |
| 当前任务一致 | 物理 CurTid 读取与抽象 curtid 连接到同一 tid |
| 切换后不变式 | 真实指针 store，加上 curtid 更新；时钟字节／ostmid／任务／事件保持。区分旧任务在表与不在表两分支 |
| 调度关系合法性 | 复用已证明 `V293_scheduler_good`；不宣称重新验证了调度选择算法 |

旧任务不在表时，框架还要求合并返回的局部资源。此处 local invariant 是 Aemp，因此证明的是空资源归还分支，**不是完整任务资源所有权／删除生命周期**。

## 独立入口和反向检查

`audit/probes/V293TimeSharedGoodProbe.v` 独立编码时钟块80、当前指针块90及四个抽象槽位；入口指针91，目标92，时钟任意。真正的字节所有权建立非空 SWINVt，独立接口在同一个 Mf 中核对指针变为92、时钟未变。额外实例化旧任务在表／不在表两种任务映射。

这些是空间可满足和保持性检查；**没有声称目标92是这两个字面任务表中的最高就绪任务**。owned-switch 接口允许任意目标，故不能把该实例冒充一次完整调度执行。GoodI 的抽象调度约束仍由其正式义务与已有 GoodSched 处理。没有初始化可达性结论。

在实现前冻结 `audit/logs/stage37-time-shared-good/protocol.json`。两个单因素负控仅改最终接口的一个结论，全部 Proof／不变式／实际 store 保持：

1. 物理时钟最终 n 改成常数1；
2. 抽象当前任务最终新 tid 改成旧 ct。

两者都在同一最终内存读回结论连接处拒绝，实际行号／诊断保存在 gate 的 ablations.json 与日志；只授该连接拒绝信用，不称全部下游机制均被单独检验。负控没有换用缺失 import、解析错误或不一致依赖来制造失败。

## 验证与范围

实际命令、生产／probe 编译、独立 coqchk、Print Assumptions、新测试、全量测试诊断差分、既有源／产物及历史冻结证据重核、清理前后结果，以同目录最终 `final-report.json`／manifest 为准。开发中的失败尝试也保留，不覆盖为成功。

默认 `make audit` 的历史证据身份失败继续保留；六门不晋级，不更改旧测试／检查器／覆盖清单。复用既有生产依赖，**不是全仓 source-only 干净构建**。

本轮并未完成 setter 的物理与抽象时间同步、真实任务资源 local invariant、嵌套 getter 入口、完整 API 生命周期、初始化、所有 ISR safety、最终源码级 GOOD_OS 或同程序 K1–K4；uCOS3 尚未启动。下一步连接 OSTimeSet 在临界区内的真实时钟写入与 ostmid 同步更新，而不是只改物理时间后强行关 Inv。

## 保留的一次正式运行后检查失败

gate01 的六条外部命令实际均达到预期，coqchk 退出0；但 runner 的公理**名称身份**断言退出1：生产因多余显式 Import 将既有 `Classical_Prop.classic` 打印为 `classic`，probe 打印为限定名。没有把这次 runner 记成成功，也没有放宽允许公理集合。删除多余的显式 Import，在证明中使用限定名 `Classical_Prop.classic` 后，使用新目录 gate02 完整重跑；gate01 的代码快照／日志／诊断原样保留。最终结果以 gate02 和 final-report 为准。

## 实际收尾结果

gate02 六条实际命令退出码 `0／0／0／1／1／0`；生产2根／独立6根仅既有 classic 与 functional_extensionality_dep 或闭合，coqchk 两模块通过。新增9测试清理前后全过。全量1090测试实际374失败、1错误；此前373项诊断全部保留，只新增第36步冻结项目身份／精确append两项失败，未修改旧测试／证据。

旧177活动源／885生产依赖逐一不变，新增后178＝75目标＋103框架／tactics，5个新生产产物保留；基线仅4个已声明文档／项目路径前插或追加，缺失0，HEAD不变。第35／36步冻结manifest分别150／117项无漂移，旧lia／nia缓存未变。默认audit仍exit2、六门94／1／1／1／1／0不晋级。

清理前逐项记录并在首次unlink前全量重新核实，删除763项（708软链接、55实文件／2019266字节）及90目录：仅gate01／02四个负控树、两次新鲜C临时物化树和probe5产物。基线删除0，源／全部失败与成功证据／缓存／生产依赖保留；清理后新9测试全过、全量诊断multiset不变。未提交／推送；并非全仓source-only构建。目标仍active，下一步连接setter共享物理／抽象更新。
