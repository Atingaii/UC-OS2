# 第288步：OSIntExit 活跃路径接入 API 入口

## 一、这一步做了什么

此前第287步从临界段开始证明。这一步将其向前连接到既有边界归一化 AST 的 `sfexec` API 入口：

`sfexec → 切换局部环境 → 分配 saved → saved=0 → running 判断 → 临界段 → nesting/lock → helper → 目标更新 → 切换与恢复后返回`。

生产接口为 `V293_exit_active_call_TaskSim`，位于 `certiucos/v293/proofs/V293ExitActiveCallTaskSim.v`。该文件只暴露一个 `Theorem`；其余引理用于内部组合。最终后置为 `RDYINV G t ** LINV ...`，不是 Post=True。

公开接口不要求调用者提供执行轨迹、分配/写入/读取/求值结果，也没有函数体或 dispatch 的 TaskSim continuation 前提。局部分配覆盖所有合法 fresh block，不固定某个地址。`running`、两个 guard 与完整 decoder 的存储资源进入最终 G；storage 不承诺任意兼容共享归还后的原值不变。

## 二、原计划没有全部完成

原先冻结的 `protocol.json` 要求从客户端 `scall` 起步；本步**未满足这个主门槛**，没有改写计划降低门槛。

框架区分客户端 `scall` 与 OS 的 `sfexec`。现有 OS 小步组合桥要求 `InOS`，不能直接用于带 skip-client 尾部的客户端调用。探针 `ACclient_call_not_OS` 证明该具体类入口不属于 `InOS`，防止加入矛盾前提获得空洞结果。这不等于证明客户端调用永远不能组合，只说明不能套用当前 OS 小步桥。

因此，本步建立的是 **API 入口 TaskSim**，不是客户端 `scall` 完整调用 TaskSim。机器报告必须保留 `protocol_fully_completed=false`、`client_scall_TaskSim=false`。下一步需要匹配高低层客户端调用步骤与 API 入口，而非修改框架分类。

## 三、证据与对照

- `ACbase` 构造独立完整资源堆：有 running/guard/decoder/任务记录，没有预分配 saved 单元。
- `ACnonempty_API_entry` 固定真实 scheduler spec，为 `n=0/1` 实例化上述接口，后置为 RDYINV；不要求未证明的 scheduler 等式。
- `ACfresh_exists` 证明新堆存在合法分配位置。
- `ACsaved_initialization_control`：同一新分配 raw Tint32 堆，仅省略写零这一因素；原始 load 为 Vundef，实际 store 后 load 为零，其他块保持相同。**这是局部初始化对照，不是完整调用执行消融**，不据此推断全部下游机制有效。
- 每份生产/探针文件串行重复编译两次；逐根 `Print Assumptions` 和递归 `coqchk` 结果见 `audit/logs/stage288-exit-active-call/`。原始失败尝试和源码快照保留。
- 最终实测数量、全量回归差异、清理及冻结检查以该目录 `verification.json` 和 `checkpoint.py` 为准；结构测试本身不替代 Coq 语义证明。

## 四、范围没有扩大

固定 C、配置、AST、框架和 ADR-0010 均未修改。沿用 ADR-0010 已接受的调用点归一化，不是外部端口实现 refinement。当前仅覆盖 running=1、nesting=0/1、lock=0 且需要切换的分支；其他 running 值、等优先级和一般 nesting 分支未覆盖。

IE=false、si=nil、ISR 全清、空 LINV、强 current guard 缺口仍在。不是无条件 WFIFun/WFInt，不是 GOOD_OS，也没有闭合同程序 K1–K4；uCOS3 未开始。全仓库旧失败仍保留，目标 active，本步不提交/推送。
