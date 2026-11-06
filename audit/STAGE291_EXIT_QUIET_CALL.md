# 第291步：running=0 的完整客户端调用

## 先用 C 代码理解

固定 V2.93.01 的 `os_core.c:693-736` 中，`cpu_sr=0` 在外层判断之前执行。
当 `OSRunning=0`，`if (OSRunning == OS_TRUE)` 为假，因此不会进入临界段、递减 nesting、读取调度锁、调用 scheduler helper 或切换任务；函数直接返回。
但“没有调度”不等于“什么都没做”：局部变量仍须分配、初始化，返回时还须释放，恢复调用者环境并保持不变量。

本步依次把这些步骤连接起来，而不是把返回结果当作前提。高、低两层从相同的客户端 `scall f nil` 开始，最终后置仍是原 storage 家族的 `RDYINV`，不是 Post=True。

## 稳定接口

- 生产：`certiucos/v293/proofs/V293ExitQuietCallTaskSim.v`。
- 唯一公开接口：`V293_exit_quiet_client_call_TaskSim`。
- 前提：真实函数绑定、分支专用 `END None` API 绑定、合法客户端尾部、全清 ISR、`IE=false`、`si=nil`、saved/running 标识符不同、running 的全局类型绑定与字节0所有权，以及原 ready-storage 核心和 `CurTid`。
- 不要求预分配 saved，不要求给出 execution、store/load/eval 结果或下游 `TaskSim`。
- 入口覆盖实际分配规则的全部 fresh Tint32 局部选择；从空间所有权内部构造 saved 写零、读取 running、false guard、释放和返回。
- 原 AST、C、配置、framework 与 ADR-0010 均不变。解释的是既有 boundary AST；不是端口函数体 refinement 或已验证 C 前端。

新资源只把 running0 的 typed owned cell 与既有核心分开；返回时重新合入同一 `ready_storage_inv` 家族的 storage 列表，保留目标指针、就绪记录和当前任务抽象字段。它不是第289/290步资源列表的等价性定理。

## 非空实例与对照

`audit/probes/V293ExitQuietCallTaskSimProbe.v` 的 `QCmemory` 由原 `RTfull OwnershipWaiting`、目标指针和 running0 字节组成；所有分离关系和原 `RDYINV` 后置在 Coq 中证明。

这是独立构造的非空 quiet 堆，不声称它与旧 `ACmemory` 字节相同。没有预分配 saved，没有 nesting/lock cell 或 decoder；程序中没有 helper 绑定。因为 false 分支不会访问它们，不应把它们作为这条分支的额外公开前提。它们仍存在于未修改的函数 AST 中。

前瞻协议只规定单因素局部对照：同一 QC 堆仅把 `(152,0)` 的 running 字节0写成1，证明 guard 从 false 变成 true，同时每个其他地址保持不变。不是完整调用执行消融，也没有证明 running=1 那边能在缺少 nesting/lock/decoder/helper 的 QC 堆上完成，更不由早期拒绝推论所有下游机制正确或必要。

## 验证入口与历史证据

协议、全部失败/成功编译快照、重复编译、逐根 assumptions、递归 coqchk、构建与回归原始输出均放在 `audit/logs/stage291-exit-quiet-call/`。最终数值以 `verification.json` 为准。

继承的 `source-identity.json` 保留历史字段，其旧 function/scope/verified_entry 描述不作本步覆盖依据；本步以 `source-identity-scope.json` 的 OSIntExit 693–736 行锚点和 running0 分支描述为准，固定源码哈希仍独立核对，未重跑预处理器。

第290步封存 writer 竞态的首次失败 manifest、checkpoint01–04 及恢复证据均原字节保留。本步以前一阶段的 `checkpoint-evidence-manifest-final.json` 为准，不改旧失败、不改旧门槛。旧检查点因 `_CoqProject` 追加新生产文件而拒绝当前状态，是如实记录的历史 gate 结果，不据此覆盖冻结报告。

旧失败保留；本步 Python 结构测试只核对接口和证据，不替代 Coq kernel。整个仓库仍未全绿。

## 尚未完成

- 仅覆盖 `running=0`、禁用中断、空 ISR 栈及空 LINV；不是所有 running 值或任意中断状态。
- 锁阻塞、等优先级分支及统一 OSIntExit spec/资源接口尚待连接。强 current guard 缺口不变。
- `WFIFun`、`WFInt`、同程序 K1–K4 与最终 `GOOD_OS` 未闭合，uCOS3 未开始。
- 整体目标仍 active；没有提交或推送这批历史工作区改动。

下一步先连接活跃但调度锁阻塞的完整调用，再处理等优先级并统一分支，不能把分支定理数量当作整核完成度。
