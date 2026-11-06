# 第313步：切换后被选任务的原框架 TaskSim

## 1. 本步推进到哪里

上一阶段已从原 `pint` 连接同程序中断前缀与物理切换，但被选任务仍停在 `CSready`。本步不更换程序、语义或内存：从实际切换的后置所有权构造原框架 `TaskSim`，再让这个非空任务执行三条原低层／高层规则。

现在连接的是：

原 `pint` → EOI／Enter／normalized Exit／缓存拷贝 → 原物理切换 → 常量求值 → 位取反 → 语句 continuation 消去。

这不是整个 handler 的高低层模拟，也不是 `GOOD_OS`。新增的共归纳结论覆盖指定纯标量代码形状的**全部原任务步**；全局中断注入、任意应用任务和切出任务恢复不在该结论内。

## 2. 最小稳定接口

生产文件：`certiucos/v293/proofs/V293SelectedScalarTaskSim.v`。

- `V293_scalar_client_state` 只描述四种代码形状：常量＋一元表达式 continuation、该一元运算前的值、运算后的值以及终止代码。它不定义新的执行关系。
- `V293_scalar_client_cstep` 穷尽原 `cstep`，证明形状闭包、内存不变及对程序表的独立性；事件／API排除与abort匹配仍使用原规则。
- `V293_scalar_client_TaskSim` 通过原 `task_sim` 的七项义务直接共归纳构造 `TaskSim`，没有把“已存在后继TaskSim”当作输入。
- `V293_scalar_current_TaskSim` 从真实 current-core 资源分出共享 `INV`、当前任务的 `RDYINV ** LINV` 与外部 `R`，输出覆盖输入内存／抽象状态的四条 `join` 和被选任务的 `TaskSim`。

共享、任务、外部堆没有被混成一份：`R` 留在外部，不塞进任务局部不变式。该接口仍要求全清ISR、辅助栈界限、代码形状和当前core所有权；它没有证明这些前提从内核初始化成立。

形状族允许任意一元操作／值，可能包含按原语义无法继续求值的组合；此时证明的是低高层abort匹配，不是“整个形状族永不abort”。非空实例采用可执行的32位值，三步执行另有直接见证。`TaskSim` 与全局safety不能混同。

## 3. 同一实际切换后继堆

实例：`audit/probes/V293SelectedScalarTaskSimProbe.v`。

`SCcompleted_simulation` 调用已有 `BGprepare` 构造真实入口／全局前缀，再调用原 `V293_control_switch_forward`，保留同一 `Mf` 的后置资源 `After`。不是从末端可读事实反向恢复可写所有权。

`SCafter_core` 展开被选任务的原 `SWINVt`，从目标指针单元构造真实全局环境绑定的dispatch-cell，再取得当前最高就绪core。局部环境和辅助状态取被选任务的真实投影，而非切出任务的CPU局部环境。`SCpartition` 将该core交给生产接口。

| 对象 | 本步的明确结果 |
| --- | --- |
| 被选任务 | 原 `OwnershipReady`，优先级4；没有把阻塞任务改成ready |
| 被选代码 | 原 `CSready`，不是 `SKIP` 代替品 |
| 被选环境／辅助状态 | `emp`、`(true,nil,nil)`，与原全局投影一致 |
| 共享资源 | `satp ... (INV SCinv)`，来自同一 `Mf` 的实际资源分区 |
| 任务资源 | `satp ... (RDYINV SCinv Ready ** LINV shared_li Ready nil)` |
| 外部资源 | 控制字节1／0／0、缓存4及原有 `Atrue` 剩余帧 |
| 切出任务 | `Waiting` 的非空 `BGcaller`、原表达式和中断continuation保持 |
| CPU局部单元 | 仍在旧剩余帧中，未恢复独立所有权；不能从 `Atrue` 加读取事实推出可写／可释放权 |

`TaskSim` 的任务堆是分出的 `Mt`，不是整个OS堆。实际三步使用原框架独立的 `clientst`（`SCclient` 的client-memory为 `emp`）；共享OS堆仍是 `Mf`。纯标量代码不读写这两类内存，不能据此推论访问共享内存的应用任务也自动成立。

## 4. 真正执行三步，而不是零步闭包

`SCthree_steps` 同时给出三条原 `lpstep` 和三条原 `hpstep`：

1. `ec32_step`：常量7变为值7。
2. `evuop_step`：按原活动语义得到 `Int.not (Int.repr 7)`。
3. `svseq_step`：消去 `kseq (sskip None) kstop`，到 `SCend`。

每一对相邻代码都证明不相等。`SCfull_client_run` 把三条低层步接在同一真实切换后，保留切点的 `SCpacket Mf`、最终被选代码以及切出任务保存上下文。该packet描述切点 `CSready` 的模拟接口，不被误称为任意最终全局状态的 `ProgSim`。

### 被编译器发现并保留的语义误读

曾将 `framework/model/opsem.v:247` 的恒零 `uop_eval` 当作活动定义；它实际上位于注释内。`probe-15` 使用原 `evuop_step` 时拒绝了这个错误后继。活动定义是 `framework/model/memory.v` 中的 `uop_eval`／`negint`，`negation` 对应 `Int.not`。

纠错先记录于 `semantic-correction.json`，然后修正新实例期望；旧protocol、失败日志和源码快照原样保留。没有改框架来适应错误期望，也不把该实例包装成完整C算术正确性证明。

## 5. 单因素观察与对抗式复核

观察对照方案在运行前冻结。两份测试都先获得完整前缀／切换、共享与任务资源分区、原 `TaskSim` 和三步低高层执行。唯一差别是最终期待的切出caller：真实 `BGcaller` 改为空 `emp`。基线通过，变体在最后使用 `Saved` 时失败；诊断仍含 `Full`、`Low`、`High`、`Shared`、`External`、`Task`、`L1`、`H1`。

这检查的是完成后的精确上下文观察，不是删除程序机制的实验，不能证明每一层机制都不可删除。

| 审稿式质疑 | 本步证据或明确限制 |
| --- | --- |
| 又假设一个TaskSim而没有证明 | 生产接口直接构造原七义务，实例没有saved-TaskSim输入 |
| 共享INV只是无法实例化的空洞 | 同一真实切换后的资源经partition得到可满足见证 |
| 用不相干堆拼接 | `After`、core、partition、packet和后续执行均连接同一 `Mf` |
| client什么也没有做 | 三步原低高层规则、相邻代码不等，以及完整低层轨迹拼接 |
| 偷换被选任务环境 | 使用原投影中的 `emp`／`true,nil,nil`，旧caller单独保留 |
| 一元运算解释凭印象 | 原编译失败反例保留；按活动定义修正，不改语义 |
| 纯client可推导全局安全 | 不成立；pint交错、handler统一模拟和初始化仍开放 |
| 任意形状都保证不abort | 不成立；一般接口保留原abort匹配，具体可执行实例另有三步见证 |
| 可以继续释放旧CPU单元 | 不成立；所有权仍未跨干扰恢复，本步不作此声明 |

## 6. 验证与后续

| 检查 | 实测结果 |
| --- | --- |
| 生产接口／非空实例 | 各两次稳定编译通过，两次源码身份相同 |
| 递归信任复核 | 18个根通过；`coqchk` 退出0，424.245秒；仅原有经典逻辑／函数外延性假设 |
| 构建／项目注册审计 | `make build JOBS=1` 通过；387个活动V293文件、103个框架／策略文件 |
| 新增回归 | 8项全部通过 |
| 完整回归 | 2760项，437失败、1错误；与第312步全部失败／错误ID及顺序相同，没有新增失败 |
| 完成后单因素观察 | 原caller通过；改为空caller的变体在最后 `Saved` 处失败，分区／TaskSim／执行见证仍在 |
| 旧覆盖审计 | `stale function evidence input identity` 仍导致退出2；不重写旧证据制造通过 |
| 旧空白检查 | `inferules.v` 第581–586行六处仍在，日志与第312步原字节相同 |
| 清理 | 逐一确认后移除18个一次性文件；恢复原根缓存字节，保留306个原pyc及交付／复核材料 |

本步日志、各次失败／成功源码快照、稳定编译、递归信任检查、回归与清理记录均保留在 `audit/logs/stage313-selected-client-simulation/`。最终数字以 `verification.json` 为准，交付字节身份见 `checkpoint-evidence-manifest.json`。

下一步不是继续堆叠有限trace包装：需把被选任务接口接入原全局模拟的后继义务，补统一handler／控制状态接口，并处理切出任务恢复的 `excrit`／返回／`exint` 及CPU资源保持。随后仍需缓存／lookup关系的初始化与全程序保持、初始化与各功能族纵向连接。

最终验收仍是固定 uCOS-II V2.93.01 源码级 `GOOD_OS` 与同程序 K1–K4，完成后才进入教师要求的uCOS3。当前仍未完成整核目标；不进行Git提交或推送。
