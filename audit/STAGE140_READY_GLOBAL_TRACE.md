# 第140步：将连续调度片段提升到原全局任务执行

## 本步的实质进展

第139步只有 `cstepstar + lpstep` 混合执行。本步复用 Coq 标准 `clos_refl_trans_1n`，将同一源码片段和真实切换接为**原 lpstep 的连续闭包**；没有另造执行规则，没有修改 C、配置、既有 AST、framework 或 tactics，也不是 C 修复。

固定目标仍为 uC/OS-II V2.93.01，提交 `0c4a48e6fbc6e915714e816196619a5481accf0c`。沿用 `Source/os_core.c` 第1702行起、两次锁定检查后的原 `OS_Sched` 片段：调用 `OS_SchedNew`、目标赋值、原优先级字节比较、计数器自增和 `OS_TASK_SW`。只声称既有手工 AST 对应，不声称自动 C 前端。

## 接口与执行身份

生产文件 `certiucos/v293/proofs/V293ReadyGlobalTrace.v` 有5个证明根，稳定提升接口是 `V293_csteps_global`：

- 输入一条实际 `cstepstar`、外层 OS 函数绑定、初始 `goodks` 和当前任务辅助状态映射。
- 使用原 `cstep_cont_locality` 保留同一个合法外层 `kcall`；从绑定与 `goodks` **推导每步 InOS**，不是让调用者逐步提供分类 oracle，也没有伪造 `kint`。
- 每个源步骤经原 `ostc_step / inapi_step / pt_step` 提升。`ltstep_goodks` 保持 continuation 条件；任务代码表与 OS 局部环境映射同步更新，其余任务投影满足原 `Steq`。
- `clientst` 在整个闭包中保持同一参数。没有用 client step 将应写 OS 内存的数据写入客户端内存。

`V293_global_steps` 只是原 `lpstep` 的标准自反传递闭包，不增加迁移。`V293_enclose` 和 `V293_global_at` 分别是 continuation 附加和全局映射嵌入，删除任一就不能表述／连接本步原框架步骤；没有引入新调度器或一套平行执行语义。

探针 `audit/probes/V293ReadyGlobalTraceProbe.v` 有5个证明根：

1. `GSsource_tail` 在同一非空 ready＋waiting、实际 TCB／位图／优先级表／lookup／canary 内存中运行第139步生产接口，原调用、分配、返回、释放、目标赋值和尾段仍是同一执行。
2. `GSglobal_source` 将两条真实字节分支逐步提升为连续全局执行。相等分支计数器仍为 UINT32_MAX；不等分支实际回绕为零。
3. `GSglobal_switch` 把上述确切代码和同一 Mtail 内存接到原 `pswitch_step`，闭包从原片段入口一直到实际 current 指针写入及 ghost current 切换；其他任务代码保持。这里不再是混合执行。
4. `GSglobal_no_switch` 检查 Ready／cache=4 的自然一致入口，原分支不切换，计数器不变。
5. `GSbinding_only_control` 检查下述单因素对照。

**程序范围必须区分：**编号112是带准确片段体 `STbody` 的 enclosing fragment fixture，不是完整 `OS_Sched`，不是生产程序最终函数绑定。它为原框架的 OS 分类提供可检查的真实程序绑定，但没有证明这一入口可由初始化或完整调用到达。编号107仍执行原 `OS_SchedNew` 体。通用提升定理可复用于后续完整函数，不给 fixture 整函数信用。

## 事先约定的单因素对照

只删除外层112绑定：其余函数绑定、代码、continuation、内存、权限和字节均保持。正例 `GSpo` 与对照 `RCprogram` 在所有非112函数上相等；对照仍有原片段的完整 `cstepstar`，但相同入口不再满足 `InOS`。这隔离了外层 OS 绑定的分类作用，而非把“源码可执行”当作“能写 OS 全局状态”。

负结果只证明分类失败，**不是 stuckness 定理**，也没有声称排除了全部其他 `lpstep` 或 client step；没有把共同提前拒绝当作所有下游机制通过。

## 仍保留的反例与边界

`GSglobal_switch` 在这条连续全局轨迹末尾仍证明：实际 current 已指向优先级4的 Ready，cache 仍为6，且 `V293_current_task ... Ready 6` 不成立。原 `pswitch_step` 不写 `OSPrioCur`；不通过改优先级判断或删除一致性需求绕过它。

有限 ready Inv 保留不等于缓存一致性或生产全局语义 Inv 已完成。切换后探针的空间断言仍以原调用者局部环境表达，不能冒充已建立新 current 的完整 `CurLINV`；实际全局任务环境与辅助状态由原规则保留／选择。其他任务代码保持也不是跨任务恢复的私有资源稳定性证明。

本步是**存在性、无交错**的片段轨迹，不是所有交错或所有分配选择，不是初始化可达性。中断／锁定 guards、临界区进出、任务恢复、Hook／栈、完整 API／ISR、`WFIFun`、完整 `OS_Sched`、`GOOD_OS` 和同程序 `K1–K4` 仍开放。**uCOS3 未开始**，总目标 active；六门保持 `94/1/1/1/1/0`。

## 验证与收尾

证据目录：`audit/logs/stage140-ready-global-trace/`。实际结果以 `trust.json`、`verification.json` 和 `checkpoint-report.json` 为准，未运行或未通过不能记作通过。

- 生产／探针的独立编译日志和每次源码快照保留，包括失败尝试；`stable-compiles.json` 指向稳定版本。
- 对全部10个新根逐项 `Print Assumptions`，并对306个活动模块及26个额外探针运行 `coqchk`；检查假设不扩大既有白名单。
- 8项新增结构／证据身份回归；全量预期1813项，保留旧423失败／1错误，比较精确失败 ID 集合和错误 ID，不仅比较数量。旧过期身份提前拒绝不证明后续门禁通过；本步语义信用来自独立 Coq 检查。
- 保留 `make audit` 的旧证据身份过期失败及 `framework/logic/inferules.v` 581–586 的旧空白失败；不修饰成绿灯。
- 清理前逐项核对一次性 Trust 产品和缓存备份；恢复既有 lia／nia 缓存，仅删除本步一次性材料。保留源码、可复用产品、失败日志、快照及冻结证据。

下一步将这一提升接口接入完整调度函数的 guards／临界区上下文，并继续处理源码级 `OSPrioCur` 同步边界，不把片段 fixture 当作最终端口实现。未提交／推送；历史冻结证据不改写。
