# 第289步：把客户端调用接入 OSIntExit 活跃路径证明

## 一、接上了哪一段

第288步仅从 `sfexec` 函数入口建立 TaskSim，尚未完成计划中的客户端 `scall` 门槛。本步新增唯一生产接口 `V293_exit_client_call_TaskSim`，高低两层都从同一个 `scall f nil` 开始：

| 层级 | 客户端步骤 | 入口以后的证明 |
| --- | --- | --- |
| 低层实现 | `scall → sfexec`，不改变任务状态，更新客户端环境映射 | 第288步实际分配 saved、写零、running 判断、临界段、helper、目标更新、切换与恢复后返回 |
| 高层规格 | 同样先 `scall → sfexec` | 根据显式 API 绑定进入 `hapi (sched;; END None)` |

公开定理内部推导上一轮的 API-entry TaskSim，不把它作为调用者要证明的 continuation 前提；最终后置仍是 `RDYINV G t ** LINV ...`，不是 Post=True。公开前提只保留实际函数/API/scheduler 绑定、资源及当前分支条件；不要求执行轨迹、分配/求值/存储结果或 `InOS scall`。

`scall` 的客户端步骤不查函数表。到 `sfexec` 以后，低层才查实际 OS 函数，高层则查抽象 API。正因这两种入口不能混同，本步匹配高低层的客户端步骤，而没有修改框架 `InOS` 分类。七类 TaskSim 义务均通过原构造子证明；没有假定客户端环境一定存在来跳过 abort 情形。

## 二、如何确认不是空洞组合

独立探针 `CCnonempty_client_call` 复用第288步已经构造的非空 `ACmemory n` 与 `ACbase`：完整任务记录、decoder、running 和两个 guard 均在；没有预分配 saved。固定 `CCspec` 和 `V293_scheduler`，覆盖 n=0/1，证明实际 RDYINV 后置。所有合法 fresh saved 分配由原 API-entry 证明覆盖。

`CCactual_client_low_step` 另外给出有效客户端环境下真实 `ltstep` 的后继；`CCclient_step_unchanged` 给出同一堆上的具体 `cstep`。不通过给客户端调用添加不成立的 `InOS` 前提制造证明。

## 三、预先确定的单因素对照

协议在实现前固定：只删除抽象 API 表中函数 114（OSIntExit）的绑定。

- `CCbinding_single_factor` 证明 `CCspec` 与原 API 空表 `GHspec` 只差这一项；scheduler、interrupt spec 和所有其他 API 项相同。
- 相同低层程序、客户端代码与堆仍然有上述客户端后继。
- 有绑定时，`CCabstract_entry` 构造高层 API 入口步骤。
- 无绑定且同一 `RCprogram` 没有该函数时，`CCmissing_binding_no_high_step` 排除该 `sfexec` 的所有高层 `htstep` 后继。

**这是局部 API-entry 对照，不是完整调用执行消融。** 它只解释这一绑定对入口连接的作用，不推断所有下游机制的必要性或整个系统的进展性质。没有改写第288步被冻结的未通过门槛；本步自己的 matching-client-call 主门槛另行检查。

## 四、证据与范围

生产文件 `certiucos/v293/proofs/V293ExitClientCallTaskSim.v` 加入 `_CoqProject`；探针不加入生产清单。两份文件均串行重复编译，逐根假设检查与递归 `coqchk` 的原始结果见 `audit/logs/stage289-exit-client-call/`。失败的编译尝试和源码快照也保留。实测数量、回归差异和清理以 `verification.json`、`checkpoint.py` 为准；文本结构测试不代替 Coq kernel 检查。

固定 C、配置、AST、框架与 ADR-0010 不变。这是已有源码级边界归一化上的客户端入口证明，不是外部端口实现 refinement。覆盖仍限于 running=1、nesting=0/1、lock=0、需要切换的分支。一般 nesting、等优先级、其他 running 值未覆盖；IE=false、si=nil、ISR 全清、空 LINV、强 current guard 缺口保留。

这不是 WFIFun/WFInt，不是 GOOD_OS，也未闭合同程序 K1–K4；uCOS3 未开始。旧失败保留，目标 active，本步未提交/推送。

### 本步实测结果

| 检查 | 实测 |
| --- | --- |
| 两份 Coq 源文件重复编译 | 各两次通过，源码哈希一致 |
| 逐根假设与递归 `coqchk` | 15 个根通过；仅既有经典逻辑与函数外延性假设 |
| 生产构建、项目审计 | 通过；项目审计计数为 363 个活动证明文件及 103 个框架文件，不等于函数覆盖数 |
| 新增 Python 回归 | 5 项全部通过，清理后复验仍通过 |
| Python 全量回归 | 2611 项；434 个失败、1 个错误，与第288步失败/错误标识及顺序完全一致 |
| 全量覆盖审计 | 未通过，保留既有函数证据身份过期问题 |
| 清理 | 逐项确认后移除 8 个一次性文件，恢复原数学缓存，306 个既有 Python 字节码不变 |

保留 24 次编译尝试的原始结果和对应源码快照，包括失败尝试；未通过重写旧证据或弱化检查来制造全量通过。机器可复验入口为本步 `checkpoint.py`。

## 五、下一步

客户端入口缺口已由本步局部定理补上，不能因此把整个 OSIntExit 或整核标为完成。接下来优先复用同一资源不变量处理不切换的等优先级分支与一般 nesting 的提前返回，再统一函数规格；继续保留上述中断/局部不变量和 current guard 的未闭合义务，最后才能进入 WFIFun 与整核连接。
