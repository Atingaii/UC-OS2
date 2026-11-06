# 第333步：显式链表资源、源码head赋值与完整未到期迭代

## 目标与边界

固定目标仍为 uC/OS-II V2.93.01、锁定上游提交及两类授权修复；未改C、配置、历史生产证明、旧测试或冻结证据。

第332步在切换堆上显式准备扫描器，只执行到Next赋值前。本步新增稳定接口 `V293_ready_countdown_linked_iteration`：从同一完整ready_full与显式扫描器/Next所有权，构造实际减一、Next赋值和退出临界区，保持完整就绪资源，恢复原IE及临界栈。前置条件没有成功执行、成功store或预期load；这些均在证明中导出。

**完整ready_full本身不拥有Next**，也不拥有链表头。不能从它无条件推出整个扫描循环。非到期范围为 `2 <= d <= Int.max_unsigned`，不含到期分支。

## 原始资源如何到达入口

- 新实例 `LHsmall` 在客户端入口已经具有head全局槽 `(91,0)` 和旧任务Next槽 `(60,20)`；head指旧任务，Next指原就绪的另一任务。
- `LHge` 从入口起绑定head名称703，`LHresources` 把两槽作为分离frame穿过同一实际全局客户端调用、局部变量分配与延时阻塞。
- 复用 `V293_dly_global_call_ready`，原全局轨迹止于调度器调用前的原cutpoint。没有将第328步的具体末端结果偷换成增强堆，也没有事后向该冻结堆补造已分配字段。
- 随后另证新鲜扫描器块的真实alloc和源码 `ptcb = head` 赋值。右侧读取名称对应的全局槽，并非把预期指针常量当成源码表达式。

这是显式增强初始资源的有界实例，**不是OSInit/TaskCreate的初始化来源证明**。全局前缀、scanner分配/head赋值和单次iteration分别给出真实语义轨迹，未凭资源可组合性把它们伪拼为合法全局中断。

## 正例与事前单因素消融

协议先于实现冻结，见 `audit/logs/stage333-ready-tick-linked-entry/protocol.json`。

| 保持/改变项 | 正例 | 消融 |
| --- | --- | --- |
| 起始堆与head初始化 | 同一 `Mp` | 同一 `Mp` |
| 临界区进入与退出 | 实际执行 | 实际执行 |
| delay非零判断、减一、未到期判断 | 实际执行，3→2 | 原语句不变，实际执行，3→2 |
| 抽象任务表、完整ready_full、分离frame | 更新任务表并闭合 | 同样更新并闭合 |
| 唯一变化：Next赋值 | 原赋值，scanner改指另一任务 | 仅替换为skip，scanner仍指旧任务 |
| 退出后的预期scanner指针门 | 通过 | 晚拒绝 |

消融不是编译失败、入口缺资源或提前拒绝：`LHmutant_late_gate` 构造突变局部片段一直执行到excrit之后，delay2与更新后的完整就绪资源都成立，再用同一scanner槽的不同读取反驳正例终点。不是整ISR突变程序，也不是K1–K4之一。

## 证明文件与复核

- 生产：`certiucos/v293/proofs/V293ReadyTickLinkedEntry.v`，3个公共定理：head赋值、Next赋值、完整未到期iteration。
- 实例与消融：`audit/probes/V293ReadyTickLinkedEntryProbe.v`，12个证明根，包含增强初始堆、实际全局前缀与同输入正反例。
- 新增8项独立Python检查覆盖源码身份、非循环接口、语义连接、资源来源、单因素AST差异、递归信任边界与历史保持；字符串检查不代替Coq内核检查。
- 两文件各重复编译两次；固定来源的OSTimeDly、OS_Sched、OS_SchedNew、OSTimeTick重新物化预处理并核对哈希；增量构建、15根Print Assumptions与递归coqchk、两轮全量测试分别记录，最终实测见本步 `verification.json`。
- 保留开发中的失败snapshot与日志，不把失败改写为成功；不改旧失败测试或放宽全量门禁。

## 本步实测结果

15个证明根的假设仅含既有classic及functional_extensionality_dep；递归coqchk通过（约315秒），891份Coq输入在检查期间保持。两文件各两次稳定编译、增量构建、源码身份重放、项目审计及两轮新增8项检查均通过。

两轮全量均2916项、443失败、1错误；第332步原442失败及1错误的身份/顺序完整保留。新增失败仅为 `test_switched_tick_prefix.SwitchedTickPrefixTests.test_history_and_bounded_completion`：旧测试要求_CoqProject严格等于旧冻结清单，新增注册使其不再相等。没有删除或豁免该测试，无新增失败门禁为false，局部proof checkpoint为true但整体local checkpoint为false。

`make audit`仍因旧function evidence input identity过期而失败；`git diff --check`仍为旧inferules六处空白报告，输出与上步完全相同。保留这些失败，不宣称全量或最终目标通过。

清理前逐项记录了10个本步一次性Trust驱动/对象与缓存备份，删除后恢复并核对4份既有缓存；Makefile保持比_CoqProject旧，下一次build会重新生成，避免漏编。保留306个既有pyc、全部失败开发snapshot/log和可复用证明对象。源码重放临时目录由TemporaryDirectory清理。

## 不得外推的结论与下一步

本步是手工源码模型及既有critical normalization下的一次未到期循环体，**不是合法ISR入口**，**不是完整OSTimeTick调用**。尚未连接while guard、第二节点、idle终点、时钟、hook、ISR进入与返回；不是到期唤醒或旧任务恢复的可达性。示例当前任务尚为旧任务，旧任务仍等待，停在调度调用前；不能当成实际调度完成后可触发的中断。缓存仍为4，尚无缓存同步结论。

下一步必须先把显式head/Next资源纳入可跨现有调度/切换并保持的链表不变量，再连接实际while guard和各节点；不能仅给下一个切片再补一套无来源fixture。到期唤醒、全API/ISR闭包、统一WFInt、初始化、顶层ProgSim、GOOD_OS和同程序K1–K4仍开放。按老师要求，uCOS3在阶段一完成后才开始；不需硬件。总目标保持active，不因本步局部证明确认完成。
