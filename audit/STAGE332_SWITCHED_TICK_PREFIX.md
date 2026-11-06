# 第332步：切换堆扩展上的实际 tick 前缀

## 前因与本步决策

第328步已经得到原始客户端延时、调度并切换到新任务的全局轨迹。第331步在该末端堆上重装了倒计时写入后的完整就绪资源，但它只是store级闭包，不是tick代码执行。

本步补上实际执行接缝：从完整 `V293_ready_full` 和显式扫描器指针所有权，构造原规范化 `V293_tick_iteration` 的进入临界区、延时非零判断、减一及未到期分支的小步执行，停止在读取 `Next` 之前。没有另造较弱不变量。

## 公共接口与非空实例

- 生产文件：`certiucos/v293/proofs/V293SwitchedTickPrefix.v`。
- 稳定接口：`V293_ready_countdown_iteration_prefix`。输入任务表槽、任务查找、完整就绪资源、扫描器指针和 `GoodInvAsrt R`，以及 `2 ≤ d ≤ Int.max_unsigned`；不把成功store、执行或模拟作为输入。
- 输出：实际 `V293_local_steps`、成功写入、原抽象等待一步、更新任务表下同一个完整就绪资源、字段读取，以及延时4字节之外的精确内存保持。辅助状态从 `(enabled,si,ci)` 变成 `(false,si,enabled::ci)`，尚未退出临界区。
- 实例：`audit/probes/V293SwitchedTickPrefixProbe.v` 的 `SPsame_input_ablation`。先调用原 `DGglobal_switch`，在其输出堆 `M` 上分配新鲜扫描器对象，再显式写入旧任务指针，得到共同输入 `Mp`，最后执行原tick片段得到 `Mf`，延时 `3 → 2`。
- `SPsetup` 同时记录实际分配关系、局部分配小步和初始化store。指针初始化只是资源准备，不宣称它就是源码 `ptcb = OSTCBList` 的执行，也没有证明中断从真实全局入口可达。
- `SPobserved` 从完整输出资源读取原counter、guard、canary等frame字段及物理current；抽象curtid仍是新任务。缓存仍为4，而调度high为6，没有缓存同步结论。旧任务仍等待，延时为2。

## 事前单因素消融

冻结协议：`audit/logs/stage332-switched-tick-prefix/protocol.json`。

只把减一赋值替换为 `sskip None`，保留临界区、非零判断、到期判断、跳过的到期分支、`Next` 前的continuation、共同输入 `Mp` 和预期输出任务表 `SCtasks2`。`SPmutant_late_gate` 证明这个突变片段确实执行到同一cutpoint，原完整资源仍保持，但物理延时仍为3，因此不能满足同一个延时2的任务记录关系。

这是实际突变片段执行后的晚对应关系门，不是因早期拒绝就宣称下游机制有效；也不是突变ISR、整程序执行或同程序K1–K4。

## 严格边界与下一步

**这是手工源码模型及临界区规范化下的片段执行，不是经验证前端翻译，不是合法ISR入口，也不是完整OSTimeTick调用。** 原全局轨迹止于 `M`；新分配与资源准备、局部tick执行明确分段，没有伪拼成全局中断轨迹。

本步没有TCB Next所有权或读取，没有扫描循环完成、全局时钟自增、CPU hook、中断返回、到期唤醒或旧任务重新调度。下一步必须从真实入口资源取得扫描器及链表字段，连接原head初始化和遍历，再处理 `1 → 0` 的就绪更新，不能凭空假定Next存在。

完整API闭包、统一WFInt、初始化、全局ProgSim、最终GOOD_OS、同程序K1–K4仍开放；阶段一完成后才开展uCOS3。总目标保持active。

## 验证与历史状态

独立编译、两次稳定重放、逐根假设和递归coqchk、注册工程增量构建、新增8项测试及两轮全量回归分别记录在本步目录，汇总见 `audit/logs/stage332-switched-tick-prefix/verification.json`。局部内核复核不等于全量通过；增量构建不宣称清理后的全新重编。

旧源码、旧测试及冻结证据不改写。新增生产注册可能使旧严格 `_CoqProject` 快照测试增加失败，必须保留实测差异，不以豁免或改旧测试制造通过。总体审计的旧源码身份问题与旧inferules空白问题保持；未提交或推送。

### 本次实测结果

- 9根逐根假设及递归内核复核通过，889个Coq输入在检查期间保持；假设未超出既有经典逻辑与依赖函数外延。
- 两次生产/实例稳定编译、注册工程增量构建、project-audit及两轮新增测试各8项通过。不宣称全新重编。
- 两轮全量各2908项、442失败、1错误。相对第331步新增 `test_switched_countdown_closure.SwitchedCountdownClosureTests.test_history_and_bounded_completion`：其旧严格_CoqProject快照不接受新生产注册。原441失败和1错误的身份及顺序保持，无新增错误。
- `local_proof_checkpoint_passed=true`，但 `full_regression_delta_gate_passed=false`、`local_checkpoint_passed=false`、`full_target_complete=false`。没有删除旧测试、豁免新增失败或重写冻结证据。
- make audit仍因旧函数证据身份过期失败；git diff --check仍是原6处inferules空白问题。
- 清理前逐项留存审查，删除10个本轮临时信任驱动/对象及缓存备份，恢复4份原缓存；306个既有pyc、旧数据、全部失败日志和可复用证明对象保留。源码重放临时目录由TemporaryDirectory自动移除。

### 反向核对

1. 成功执行是否被当作输入而循环论证？否：公共接口从所有权构造store和执行，字段地址/读取/减法分别由原语义计算证明。
2. 是否把资源准备冒充合法中断入口？否：全局轨迹、扫描器准备、局部轨迹分段列出；未连接源码head赋值或ISR入口。
3. 消融是否只在早期失败？否：同一个Mp上的突变片段实际走过临界入口和判断，到同一cutpoint后才由物理延时3与预期2矛盾拒绝。该证据只覆盖这个片段。
4. 是否把局部成功推广到唤醒或整核？否：范围排除到期、Next、重调度、全局模拟和最终GOOD_OS；全量新增失败仍使门禁为false。
