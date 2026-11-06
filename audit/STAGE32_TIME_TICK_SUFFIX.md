# 第32步：连接 OSTimeTick 在 hook 返回后的完整后缀

## 本次推进与固定对象

固定 uC/OS-II V2.93.01，上游提交 `0c4a48e6fbc6e915714e816196619a5481accf0c`。`OSTimeTick` 配置后函数体 SHA256 为 `6103dfdd986ce129a03e1b8919997bea850989041632905f3d0ee0962ae1d251`。旧172个活动 Coq 源、C/config/port/framework/tactics、旧测试、门禁、证据、覆盖和 Git HEAD 不改。

新增生产接口 `V293_tick_post_hook_owned_execution`，从分离字段所有权推导：进入临界区、实际读取并写回 `OSTime+1`、退出临界区、实际读取并判断 `OSRunning==1`，条件执行链头赋值和整个有限链 while。执行、最终时间／扫描指针读回、任务／位图／全局字段／任意分离 frame 的归还，连接同一个 Mf；IE和控制栈恢复。没有把执行成功、store 成功或 guard 真值当作入口前提。时间输入为任意32位整数，包括回绕。

`V293_tick_post_hook_exact` 以 `reflexivity` 证明与既有完整 AST 的分解精确一致：`cpu_sr=0; OSTimeTickHook(); 本次后缀`。这不是重新验证 C 前端。

## 为什么没有宣称完整函数

`OS_APP_HOOKS_EN=0` 只关闭应用 hooks；固定配置中 `OS_TIME_TICK_HOOK_EN=1u`，CPU hook `OSTimeTickHook` 仍被调用。冻结清单将它列为 `OPEN_BOUNDARY_CONTRACT`，没有可执行实现。未删除该调用、未伪造空函数、未加入“hook 已成功执行”的前提。

入口还要求局部扫描单元已经含有效 `Vptr`，不是新分配的 `Vundef`；函数前缀、局部分配／释放／返回与初始化可达性尚未连接。非运行路径沿用统一的充分空间前提，并不宣称该前提最小。

证明只构造一条无 ISR 插入的顺序执行，不是所有中断交错下的 safety，不是完整共享 Inv、源码级 GOOD_OS 或同程序 K1–K4。uCOS3 未启动。复用现有编译依赖，不是 source-only 全仓干净构建。

## 独立入口和字面结果

入口独立编码实际内存并证明可满足，不假定执行结果。扫描初值为 idle，与真实任务链头不同，因此必须执行头赋值才能访问链中六个任务。链同时含零延时、未到期及四种到期状态。额外99和消息指针作为 frame 保持。

| 初始 OSTime | OSRunning | 最终 OSTime | B任务 Dly | group／row0／row1 | 扫描 |
| --- | --- | --- | --- | --- | --- |
| 4294967295 | 1 | 0 | 3→2 | 3／4／4 | 先改为链头，再完整扫描到idle |
| 0 | 2 | 1 | 保持3 | 保持0／0／0 | 保持初值，不扫描 |
| 4294967295 | 0 | 0 | 保持3 | 保持0／0／0 | 保持初值，不扫描 |

通用 probe 对所有 `run<256`、任意32位时间及两个初始 IE 值成立；三行是额外明确读回的端点。字面最终任务字段复用已冻结的独立六任务预期，不由本轮执行函数生成。可满足不等于从初始化可达。

开发过程中 `vm_compute; tauto` 对回绕时间的清单成员证明失败。最小复现显示数值均为零，但 `Int.int` 的内部范围证明不同；用已有 `Int.eqm_samerepr` 和模商1证明回绕相等，没有修改字面预期零。失败、诊断和成功快照全部保留，见 `diagnosis.json`。

## 前瞻负控与审查

先记录 `protocol.json`，再写实现。两项单因素负控保持 AST、所有入口前提和所有 Proof 正文：只把最终时间读回改成旧时间；只把运行时最终扫描指针改成旧扫描指针。分别应在 FinalTime／FinalPointer 连接处拒绝；不据此给 hook、初始化、ISR 或 GOOD_OS 任何信用。

`adversarial-review.json` 逐项记录 hook 边界、数值回绕、运行标志精确比较、头赋值、同内存归还、初始化、强前提、交错、源码对应和覆盖边界。正式结果以 `gate01/result.json`、原始命令日志及最终报告为准，不重写历史失败。

## 验证与交付入口

- 生产：`certiucos/v293/proofs/V293TimeTickSuffix.v`
- 独立入口：`audit/probes/V293TimeTickSuffixProbe.v`
- 新回归：`tests/test_time_tick_suffix.py`
- 全部成功／失败证据：`audit/logs/stage32-time-tick-suffix/`
- 面向学习的追加讲解：`docs/开发中/时钟中断如何跳过零延时任务.md`

旧测试因 `_CoqProject` 追加登记而新增两项 stage31 冻结身份／精确 append 诊断；此前363项诊断全部保留，不改旧测试或重绑冻结证据。默认 audit 仍 exit2（`stale function evidence input identity`），正式六门94／1／1／1／1／0不晋级。清理只针对本轮一次性负控树、诊断源和 probe 产物；源码、所有日志快照、旧缓存与可复用生产依赖保留，最终数量以 `cleanup-result.json` 为准。

下一步仍须解决 hook 的真实边界契约，并将前缀、局部资源生命周期和返回连接进同一函数证明；之后才能连接 ISR／共享 Inv／初始化。不能用本次后缀定理替代整核目标。

正式 gate01 实际退出码依次为0／0／0／0／0／1／1／0，两次预期负控拒绝均定位于最终读回连接。独立 coqchk 两模块通过；生产2根（1闭合、1含既有假设）和probe5根（含既有假设）已检查，仅允许classic／functional_extensionality_dep；新增10测试通过。输入182项在正式执行前后SHA一致，173活动源＝70目标＋103框架／tactics。

清理结果：逐项登记并在首次删除前全体重核后，删除378项一次性材料（344软链接、34实文件／2022580字节）与38目录，baseline删除0项。保留860既有生产依赖、5个新生产可复用产物、全部源码与成功／失败证据；既有缓存保留。

清理后全量1044测试：364失败、1错误；诊断按kind／id重数与本轮旧1034测试完全相同，无清理引入的诊断变化。新增10测试清理后仍全部通过。当前 `new-tests.*` 是清理后复跑结果：复用了同名输出，覆盖了本步清理前的该项原始日志（未冻结、未改任何历史证据）；首次10／0／0仅保留终端观测摘要。详见 `test-evidence-provenance.json`。已给本轮测试runner加已有名称拒绝检查，后续必须用新名字，不能声称两份原始日志均保留。Coq各次开发编译、正式门禁与成功／失败快照均保留。
