# 第33步：真实分配的未初始化扫描单元连接 OSTimeTick 后缀

## 固定对象与本次接口

固定 uC/OS-II V2.93.01，上游 `0c4a48e6fbc6e915714e816196619a5481accf0c`，配置后 `OSTimeTick` 函数体 SHA256 `6103dfdd986ce129a03e1b8919997bea850989041632905f3d0ee0962ae1d251`。保持旧173活动源、C/config/port/framework/tactics、旧测试／门禁／证据／覆盖和 Git HEAD 不变；只追加生产模块登记。

- `V293_tick_uninitialized_suffix_execution`：入口 `ptcb` 为原始可写 `Amapsto ... Vundef`，不要求旧值有效。连接实际临界区时间递增、退出临界区、精确运行标志比较、真实头赋值及整个有限 while；同一个 Mf 连接时间／扫描读回和任务、位图、全局字段及任意分离 R 的归还。没有执行、成功 store 或 guard oracle。初始 IE／控制栈恢复，时间允许32位回绕。
- `V293_tick_scan_allocation`：从明确 fresh／未绑定变量和新环境上的 R，构造实际 `alloc` 与 `salloclv_step`；在同一个 `allocb` 内存建立原始扫描单元和 R，读回 `Vundef`。不将原环境中的任意 R 默认为新环境也成立。

这不是把未初始化值当有效指针。运行分支从头全局字段读取有效指针，真正 store 后才调用已证 while；非运行分支不访问 ptcb，保持原始 Vundef。元级 load 观察不是 C 中主动读取未初始化变量。

## 独立入口与预期

先编码不含扫描单元的全局／六任务／位图／idle／额外frame内存，并从地址清单证明块70新鲜；实际分配扫描单元后作为后缀入口。显式证明 `rule_type_val_match (Tptr ...) Vundef=false`，不能套用旧有效值入口。字面最终任务预期仍复用冻结的六任务结果，不从本次执行函数生成。

| 时间／运行标志 | 扫描单元最终值 | 时间结果 | 六任务／位图 |
| --- | --- | --- | --- |
| UINT_MAX／1 | `Vptr idle` | 回绕0 | B任务3→2，group／row0／row1＝3／4／4 |
| 0／2 | `Vundef` | 1 | 保持初值 |
| UINT_MAX／0 | `Vundef` | 回绕0 | 保持初值 |

通用入口和实际执行对任意32位时间、全部byte运行标志及两个IE值成立，并归还额外99／消息指针。具体可满足不是初始化可达。

## 前瞻负控、失败与审查

`protocol.json` 在实现前登记两项单因素错误结论：仅把运行时最终 idle 改成链头；仅把非运行最终 Vundef 改成 Vnull。AST、入口和所有 Proof 正文保持不变；必须在最终 FinalPointer 连接处拒绝，不据此给 hook、ISR、初始化或 GOOD_OS 信用。

开发各次生产／probe编译均保存源快照、原始日志和实际 Coq 退出码。记录了非export模块名、保留字／scope／binder、fresh真实签名、get投影改写及typed列表不能吞掉raw单元等失败；通过直接导入、按实际签名构造及将raw单元独立作frame修复，不改旧源码／测试／断言范围。详见 `development-diagnosis.json`。开发compile wrapper自身退出不代表Coq成功，实际 verdict以对应status.json为准。

`adversarial-review.json` 明确审查新鲜分配、Vundef/NULL、头赋值、同内存连接、任意R环境变化、顺序执行／交错、hook、完整TCB、初始化、负控与旧失败。

## 严格范围

CPU hook `OS_TIME_TICK_HOOK_EN=1u`／`OPEN_BOUNDARY_CONTRACT` 不变；原AST仍保留调用。本步不证明完整两个局部变量生命周期、cpu_sr初始化／真实hook／free／void return／caller恢复，不证明所有ISR交错、完整共享Inv、初始化、GOOD_OS或同程序K1–K4。uCOS3未启动。复用865既有生产依赖，不是全仓source-only干净构建；不提交／推送。

## 交付与验证记录

- 生产：`certiucos/v293/proofs/V293TimeTickStorage.v`
- 独立入口：`audit/probes/V293TimeTickStorageProbe.v`
- 新测试：`tests/test_time_tick_storage.py`
- 原始证据及最终报告：`audit/logs/stage33-time-tick-storage/`
- 中文连续教程：[从真正未初始化的ptcb单元开始](../docs/开发中/时钟中断如何跳过零延时任务.md#已继续从真正未初始化的-ptcb-单元开始)

正式结果以 `gate01/result.json`、各实际命令日志及最终报告为准；不改旧证据来消除项目追加登记造成的冻结身份失败。默认audit仍因 stale function evidence input identity 退出2，正式六门94／1／1／1／1／0不晋级。清理只删除全体逐项登记并重核的一次性负控树、probe产物和本轮py_compile产生的四份pyc；保留旧缓存、用户数据、源码、可复用生产依赖及全部成功失败证据。

正式 gate01 八条实际命令退出码依次0／0／0／0／0／1／1／0；两项前瞻负控按预期在最终 FinalPointer 连接拒绝，全部Proof正文保持，downstream_credit=false。独立coqchk两模块成功；生产2根和probe6根均只含既有classic／functional_extensionality_dep，无新增公理。183项输入执行前后SHA相同；174活动源＝71目标＋103框架／tactics。新增10项测试全部通过，使用已有证据名拒绝机制，复跑必须另起新名。

清理前全量1054测试366失败1错误；此前365诊断按kind／id重数全部保留，新增恰为stage32的冻结项目输入身份／精确append两项断言，不改历史测试／证据。旧1044测试在实现前已执行，仍为364失败1错误，与上一最终检查点逐项一致。

清理前逐项登记类型／大小／SHA（软链接含目标）及目录成员，在首次unlink前全体重核。实际删除376项（346软链接、30实文件／2431807字节）与39目录，baseline删除0项。四份本轮pyc一并清理，未删除既有tests缓存目录或旧缓存；865旧生产依赖和5个新生产产物、源码、完整成功失败日志及快照均保留。清理后新增10测试仍全部通过，使用独立新名保留清理前／后两份原始结果。

清理后全量1054测试仍366失败1错误；按kind／id重数与清理前完全相同，无清理新增或消失的诊断。新增10项清理前后两次均通过，日志使用不同名称完整保留。最终局部完整性／基线／历史正文／Git HEAD及manifest以 `final-report.json` 和 `final-evidence-manifest.json` 为准。
