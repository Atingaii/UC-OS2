# 第295步：可调度的 OSIntExit 完整调用共用同一 sched 规格

## 1. 这次消除了什么缺口

第289步的 changed 分支使用 `sched ;; END None`，第294步的最高优先级仍是当前任务分支却使用 `END None`。两者都能各自模拟，并不代表上层可以用同一个 API 规格调用它们。

本步公开接口为 `V293_exit_dispatch_client_call_TaskSim`。调用者提供原有 `V293_exit_active_resource`，不再提供 `V293_highest_ready tasks t` 或其否定；证明内部作分类：

| 实际情形 | 低层执行 | 同一个高层 API |
| --- | --- | --- |
| 当前任务已是最高就绪任务 | fresh saved 分配/初始化、running、临界段、递减/双 guard、真实 helper、target 更新、优先级相等、退出/释放/返回 | 实际 `spec_sched_step` 消费 self-sched，状态不变，再退出 API |
| 另一个任务应当运行 | 既有第289步完整调用，含真实 helper 和切换后缀 | 同一个 `sched ;; END None`，复用既有 changed 模拟 |

**仅统一 enabled dispatch：running=1、入口 nesting 为0或1、lock=0。不是统一 OSIntExit 所有分支。** quiet、nested、locked 分支仍待接到表达 guard 的统一规格中，不能无条件执行 `sched`。

## 2. 为什么这不是把 no-op 当作假设

生产文件：`certiucos/v293/proofs/V293ExitDispatchCallTaskSim.v`。

- `V293_exit_active_abstract_current` 从已有空间资源打开 `SWINVt`，得到真正的抽象 `curtid`，而不是把物理 `CurTid` 偷换成抽象字段。
- `V293_self_sched_skip` 直接使用框架 `spec_sched_step`、`spec_seq_step2`、`spec_seq_step1` 和 `hapiexit_step`。对任意可分离抽象 frame 保持完整 `OO` 不变；不是把 sched 语法替换为 SKIP。
- `V293_self_sched_nil_call_bridge` 匹配两层第一个客户端步骤后，进入同一个 API，执行上述抽象步骤，再接第294步已经证明的低层完整入口。
- `V293_exit_self_sched_client_call_TaskSim` 内部构造 continuation，不把它留给公开调用者。
- 唯一公开 `Theorem` 为 `V293_exit_dispatch_client_call_TaskSim`。两层都从相同 `scall` 出发，没有 store/load/eval/fresh/cstep 执行结果前提，也没有下游 TaskSim 前提。

没有新增资源定义、调度器定义或第二套 ready 模型。资源、AST、scheduler、后置均沿用活动工程。后置是原 storage 家族 `RDYINV` 加空 `LINV`，**不是 Post=True**，也不表示所有旧字节逐个保持不变。

## 3. 非空实例和预先固定的单因素对照

探针：`audit/probes/V293ExitDispatchCallTaskSimProbe.v`。

正向完整调用复用此前已独立构造的两个非空堆，不复制一套同义堆模型：

- `DCsame_nonempty_client_call`：`ECmemory n`，当前任务 Ready、优先级4。
- `DCchanged_nonempty_client_call`：`ACmemory n`，当前任务 Waiting、优先级6。
- 两者使用完全相同的 `RCprogram`、`ACpo`、`CCspec`，均覆盖任意 `n<=1` 和 `ip`。各堆没有预分配 saved，完整资源分别由既有 `ECbase`、`ACbase` 构造。两堆之间不声称单因素。

对照在实施前写入 `protocol.json`：仅将**抽象 curtid** 从 Ready 改为 Waiting，其他抽象字段及 scheduler 不变。

- `DCcurrent_single_factor` 证明只有该字段不同。
- `DCself_sched_step` 证明 Ready 状态有真实保持状态的 sched 步骤。
- `DCself_sched_requires_highest` 反推任何这种步骤都必须选择当前的最高就绪任务。
- `DCwaiting_no_self_sched` 证明 Waiting 状态没有该 no-op 步骤。
- `DCself_sched_skip_with_frame` 实例化任意可分离 frame 的正向多步归约。

这**不是完整调用执行消融**。只改抽象 current 而不改物理 current 会破坏入口耦合，因此负向对照仅说明抽象单步的条件必要性，不冒充合法完整调用的反例，更不证明所有下游机制都必要。

## 4. 固定输入、验证与失败保留

源码仍是 V2.93.01 `0c4a48e6fbc6e915714e816196619a5481accf0c` 加两项授权修复；`source-identity.json` 保留 OSIntExit 精确源码哈希与行定位。没有修改 C、配置、AST、framework 或旧 gate。

- 生产5个根，探针7个根；每份最终源各连续两次相同 SHA 编译。
- 所有12个根逐一 `Print Assumptions`，递归 `coqchk` 检查依赖。以 `trust.json` 为实测，不用静态关键词代替内核检查。
- `make build`、project audit、新测试、全测试和原审计分别记录实际退出码。
- 全测试与第294步比较 failure/error 的完整 ID 和顺序，不删旧失败、不调整旧门槛。
- 开发失败快照全部保留：生产01/02缺直接导入；探针01因 subst 消去绑定名，02/03因未显式转换 get 表达式。探针03是重复失败运行，不是第二次成功。
- 第294步原检查点在本步开始前通过；完成后原只读脚本预期拒绝新的 project 追加，不修改旧脚本让它放行。
- 本步基线保留2384项旧文件；仅允许 README/status 前插、project 追加和生成依赖文件四项变化。旧失败保留，最终汇总见 `audit/logs/stage295-exit-dispatch-call/verification.json`。

实测结果：

| 检查 | 结果 |
| --- | --- |
| 生产/探针最终源码各两次串行编译 | 全部 exit 0，SHA 分别相同 |
| 12个根 assumptions | 仅既有 classic 与 dependent functional extensionality |
| 递归 coqchk | exit 0，约535秒 |
| make build / project audit | 均 exit 0；369个活动 V293 文件、103个框架/策略文件 |
| 新测试 | 5/5通过 |
| 全测试 | 2641项；原有434个失败、1个错误，ID和顺序与第294步完全相同 |
| make audit | 原有 stale function evidence input identity，exit 2 |
| git diff --check | 原有 inferules.v 581–586行空白，exit 2；本步交付静态空白检查单独通过 |
| 旧检查点 | 准确拒绝本次 project 追加；不改旧脚本 |
| 清理 | 逐项核验后删除本步8项一次性材料；缓存恢复、306个既有pyc不变 |

## 5. 尚未完成与下一步

保留 IE=false、si=nil、ISR 全清、空 LINV 的限制；强 current guard 缺口没有闭合。不是 WFIFun/WFInt，不是整个 `GOOD_OS`，不是同程序 K1–K4 回归完成，uCOS3 未开始。下一步应把 quiet/nested/locked 的条件语义纳入同一 API，而不是继续维护互不兼容的分支绑定；再处理一般中断上下文与整核连接。

验证材料、构建出的证明依赖和旧缓存保留；只清理本步一次性 Trust 六项与两个缓存备份，并恢复原缓存字节。未提交/推送，最终目标保持 active。
