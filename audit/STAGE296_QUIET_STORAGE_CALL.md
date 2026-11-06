# 第296步：不运行分支接到可调度分支的同一存储不变量

## 本步解决的问题

第291步 quiet 调用把 running 放在 storage 列表首位；第295步 enabled 调用把 running 放在 current/high/counter、decoder 和两个 guard 之后。分离合取可以逻辑重排，但 `Inv` 并不会因此自动成为同一个 Coq 值，原两个 TaskSim 不能假装已使用同一个不变量。

新增公开接口 `V293_exit_quiet_storage_client_call_TaskSim` 支持任意 `prefix`、`suffix`，将 running 放在 `prefix ++ running :: suffix` 中。输入仍复用既有 `V293_exit_quiet_resource`，没有新 ready 模型或 Inv 定义；后置仍是原 storage 家族 `RDYINV` 加空 `LINV`，不是 Post=True。

| 连接点 | 实际义务 |
| --- | --- |
| `V293_storage_insert` | 从 running 单元和其余 storage 的所有权构造指定位置的 storage；真实分离合取重排，不假设 Inv 逻辑等价就等于 Coq 相等 |
| `V293_quiet_storage_reclose` | 保留 ready 记录、target 指针、current 和全部剩余 storage 的所有权，重新关闭同一家族 Core |
| body / entry | 真实 fresh saved 分配、写零、running false 分支、释放和返回；复用既有单步、分配及返回引理 |
| public client call | 高低两层均从相同 scall 开始；内部构造后续模拟，无执行结果或下游 TaskSim 前提 |

生产文件：`certiucos/v293/proofs/V293ExitQuietStorageCallTaskSim.v`。

## 非空实例与单因素对照

探针：`audit/probes/V293ExitQuietStorageCallTaskSimProbe.v`。

- 原输入直接用 `ACmemory n`、`ACbase`；没有另造一份相似但无法比较的堆。
- `QSrunning_single_factor_complete_call` 对任意 `n<256` 和 `ip` 构造一次真实 store：仅将 `(152,0)` 的 running 从1改0；证明其余所有地址逐一不变。抽象 task/event/time/current 状态、低层 `RCprogram`、`ACpo` 和初始中断上下文不变。
- 两侧 running 判断分别是 true / false；新堆的完整 quiet 调用构造在同一个定理内，不只是局部 guard 结果，也不向调用者索取新堆或 TaskSim。
- `QSsame_invariant` 证明新调用所用的 Inv **恰好等于**既有 `ACinv`。decoder、current/high/counter、nesting/lock 所有权均保留在该 storage 中，没有隐藏地删掉。
- 没有预分配 saved。其全部 fresh 分配后继由入口证明覆盖。

`RDYINV` 后置只承诺已有不变量；上述“其他地址不变”结论比较的是进入调用前的两份输入，不是另行新增的逐字节返回值关系。

这是**完整输入单因素对照**，不是证明两个分支共用同一个 API：quiet 保持 `QCspec` 的 `END None`，原 enabled 分支保持 `CCspec` 的 `sched ;; END None`。也不是固定完整 API 下的端到端负向执行消融；它不证明每个后缀机制都必要。`n=2..255` 时原 running=1 输入也不属于第295步 enabled 的 `n<=1` 范围，不能声称该范围两侧均有 enabled 完整调用。

## 为什么不直接放宽规格

当前 `absdataid` 只有任务表、事件表、时间和 current；没有 running、nesting、lock 字段。把规格改成“END 与 sched 可任选”会丢失 guard 对功能行为的约束。本步不引入 `spec_choice`，不改 API、框架、C、配置、AST、current guard 或旧 gate，仅消除一个实际阻碍上层组合的资源位置差异。

## 验证、失败与材料

源码仍为 V2.93.01 `0c4a48e6fbc6e915714e816196619a5481accf0c` 加两项授权修复。OSIntExit 源码位于 `Source/os_core.c:693-736`；精确输入哈希及行定位见本步 `source-identity.json`。

- 实施前已记录 protocol、2390项旧输入及306个既有 pyc 基线。
- 生产5个根、探针4个根；每份最终源各两次相同 SHA 串行编译。
- 9个根逐个 `Print Assumptions`，递归 coqchk；不是仅检查源码里有没有禁用关键字。
- 失败快照全部保留：生产01缺直接导入，02全局资源引理需显式推断参数；探针01/02列表记号冲突，03缺直接导入，04生成文本的合取符号错误。探针05先通过，移除不需要的旧 dispatch 探针导入后06/07再次通过。没有重写失败日志。
- 回归比较第295步的完整 failure/error ID 及顺序；旧失败保留，不改变旧测试门槛。
- 本步不重写第295步封存材料；其原检查点会准确拒绝本步 `_CoqProject` 追加。

最终实测见 `audit/logs/stage296-quiet-storage-call/verification.json`：

| 检查 | 实测 |
| --- | --- |
| 生产与探针最终源各两次串行编译 | 均 exit 0，相应 SHA 不变 |
| 9个根 assumptions / 递归 coqchk | 仅既有 classic 与 dependent functional extensionality；coqchk exit 0，约554秒 |
| make build / project audit | 均 exit 0；370个活动 V293 文件、103个框架/策略文件 |
| 新测试 | 5/5通过；另4项结构检查也通过 |
| 全测试 | 2646项，434个失败、1个错误；完整 ID 及顺序与第295步相同 |
| make audit | exit 2，原有 stale function evidence input identity |
| git diff --check | exit 2，原有 inferules.v 581–586行空白；本步交付文件静态检查通过 |
| 原检查点 | 准确拒绝新增 project 项；旧脚本不改 |
| 清理 | 删除核验过的本步8项一次性文件，旧缓存字节恢复，306个既有 pyc 不变 |

## 仍未完成

限定 IE=false、si=nil、ISR 全清、空 LINV；不是统一 OSIntExit 规格，不是 WFIFun/WFInt，不是 GOOD_OS 或同程序 K1–K4 闭合；强 current guard 缺口不变，uCOS3 未开始。

下一步应把 locked/nested 的完整调用接入同一 canonical storage，再解决 guard 在固定抽象接口中的表达与整核连接。不能以 resource 统一替代 API 统一，也不能以一个函数的局部 TaskSim 替代顶层证明。

最终目标 active，未提交/推送。收尾逐项核验后，只删除本步 Trust 六项和两个缓存备份；恢复旧缓存字节，保留源文件、既有缓存、依赖及验证/交付材料。
