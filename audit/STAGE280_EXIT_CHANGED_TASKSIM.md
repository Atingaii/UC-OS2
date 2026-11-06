# 第280步：把原 TaskSim 接到优先级比较之前

## 当前结论

`V293_exit_changed_TaskSim` 从 `OSPrioHighRdy != OSPrioCur` 的比较语句开始，执行 changed 分支中的计数更新和 trace 的既有 skip 解释，然后复用279的缓存复制、278的 switch 和277的 pending 返回 TaskSim。公开接口只要求环境绑定、任务事实和分离资源，不要求调用者先给执行结果、store 成功或尾部 TaskSim。计数器为任意 `int32`，没有“不溢出”前提。

**这是局部模拟的起点向前推进，不是完整调用入口 TaskSim。GOOD_OS 未闭合，同程序 K1–K4 未闭合，uCOS3 未开始。** 目标继续 active，不提交或推送当前混合工作区。

生产文件：`certiucos/v293/proofs/V293ExitChangedTaskSim.v`（7个内部引理、1个公开定理）。独立见证及控制：`audit/probes/V293ExitChangedTaskSimProbe.v`（9个检查根）。实测和重放脚本在 `audit/logs/stage280-exit-changed-tasksim/`。

## 源码身份和抽象边界

沿用固定 V2.93.01、固定配置及两类授权修复；本步不修改 C、AST、配置或框架。真实源码为 `os_core.c:693–736`，比较在710行，切换计数在714行，trace 在721行，切换调用在723行；逐行锚点与8项文件哈希存入 `source-identity.json`。这里没有重新预处理源码。

handoff 使用 ADR-0010 已接受的调用点解释，不是原始外部声明 `OSIntCtxSw` 的实现精化；trace 的 skip 也是既有配置模型，不是新增假设某个任意 hook 无效。

## 证明链为什么不是一条选定 trace 的包装

| 环节 | 已证明的内容 | 不夸大的边界 |
| --- | --- | --- |
| 表达式步骤 | 对 `estepstar` 逐步归纳；每一步对任意兼容外部 frame 成立，保持内存并证明步骤确定性 | 不是把一个完整终止 trace 直接当作 TaskSim |
| 条件选择 | 求值并选择真实 `sif` 分支；一般内部桥支持真假两支 | 公开资源接口本步只覆盖 `nh <> nc` |
| 计数赋值 | 从所有权构造真实32位 store；写步证明 `store_mono`、`join_store_join` 和唯一性；写前后满足 CurLINV | 内部延续桥有 store/TaskSim 前提，但公开入口自行解除这些义务 |
| 后续连接 | 计数新值进入 storage，与279资源接口连接，不绕过缓存复制或 switch | 弱 storage 不承诺返回后仍能读到特定计数值 |
| 空前提排除 | 原完整分配调用实际达到比较切点；在同一达到堆分离资源并实例化公开 TaskSim | 前缀目前是执行 trace，不是前缀 TaskSim |

资源布局：saved(bs) 私有；saved98 与 RCframe 外部。任务子堆同时拥有 SWINVt、cache94=6、high91=4、target93、counter95 和其余 storage。分离后抽象外部 frame 为空，未把外部保存区转成任务 LINV。

本步 storage 列表是 `cache, high, counter, rest`；279实例曾把 counter 放在其 rest 中。这里只实例化既有 storage 家族，**没有证明列表置换下 Inv 的等价**，不据此自动转换其他已证明实例。

## 独立非空见证

`ECbody_prefix` 保留原保存、running 检查、入临界、嵌套/锁检查和调度 helper 的实际步骤，但在比较之前停下；不是从“handoff 已可达”倒推比较可达。

`ECfixed_prefix` 在原分配调用中产生该切点，counter 仍为 `Int.mone`，尚未更新。`ECactual_changed` 将它接回同一 `FWtasks/FWos` 的真实全局调用前缀，并在同一 M 上证明 `ECpacket`、保存区值、cache=6、counter=0xffffffff。`ECpacket` 明确把全堆分成任务与外部资源，TaskSim 用的是该任务子堆，不是另造一个相似快照。`ECnonvacuous` 用两次 fresh-block 存在性证明提供 br/bs，而非假设前提有实例。

## 前瞻控制和局部消融

协议先冻结在 `protocol.json` 与 `protocol.sha256`，未随证明结果改写。本步协议完成标志仅指该文件中的5项窄检查，不继承279未完成的完整消融义务，也不表示整核任务完成。

1. **回绕**：`ECactual_wrap_and_ablation` 从上述原调用实际达到的同一比较堆 M 开始，执行原 changed 后缀直到 handoff 入口，证明 counter 从 `0xffffffff` 变成 `0`。没有额外不溢出限制。
2. **单因素局部执行消融**：保持同一个 M、环境、比较表达式、比较为真、handoff 和 continuation 不变，只删除 changed 后缀中的 increment 语句。真实小步执行仍到达 handoff，内存保持为 M，因此 counter 仍为 `0xffffffff`。观测边界在 handoff 入口，尚未执行缓存复制。这是局部后缀消融，不是完整入口程序的执行消融，也不替其他机制做必要性背书；没有改动冻结 AST。
3. **等分支控制**：`ECequal_priorities` 从原环境绑定、两个相等的字节读取及 `n<256` 构造比较结果，证明原 `ECbranch` 到 SKIP 时内存不变，故不执行计数更新。它不是原 changed 调用的 equal 分支可达见证，也不是该分支的完整资源返回 TaskSim。

## 核查与失败保留

- 两个新文件各稳定编译两遍，源哈希一致；逐根 `Print Assumptions` 和递归 `coqchk` 的最终结果见 `trust.json`，不能用静态测试代替 Coq 内核检查。
- 既有1639项输入仅允许文档前缀、工程登记和生成依赖文件变化；所有其他旧源码、旧测试及279冻结材料逐项比对。
- 全量测试的失败/错误 ID 及顺序与279比较，不因新增局部证明删除旧失败。`make audit` 的旧证据身份失败、旧框架空白问题也保留，不改门槛制造通过。
- 开发中的 production01–16、probe01–11 快照和日志全部保留。probe03的拼写、04的 allocb 长度类型、05/06/07分离策略选错上下文、08隐式状态未实例化、09关键字冲突均按实际日志保留；成功不覆盖失败。
- 逐项清理仅针对本步一次性 Trust 检查产物和两份缓存备份；恢复既有 lia/nia 缓存，保留正式 Coq 产物、验证日志、快照和306项既有 bytecode。

## 下一条未闭合链

接着应将比较之前的调度 helper 和外层 guard 从“存在真实 trace”升级成对任意兼容 frame 的 TaskSim，并给等分支接上返回资源。仍须保持以下限制可见：si=nil、ISR 全清、空 LINV、有限 caller；generic 保存栈顶并不意味着真实完整调用的 true 栈顶已可达。

切换后的 cache=4 而旧任务 blocked 的强 current guard 缺口仍存在；本步只使用弱 storage，未宣称修复该强不变式。没有证明旧任务的全局切回可达性、任意中断交错、初始化可达性、WFInt/WFIFun 或完整共享循环。上述缺口和源码级 GOOD_OS、同程序 K1–K4 是后续工作；不能以本步17个根通过替代整核结果。
