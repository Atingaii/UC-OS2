# 第196步：OSIntExit 最后一层中断的真实调度执行

## 1. 本步连接的断点

第195步证明的是嵌套层数至少为2时，完整抽象函数调用的分配、递减、临界状态恢复与返回。本步不重复该路径，而连接最后一层 `1→0` 后实际进入调度器的中段：

```
OSIntNesting--
→ 读取更新后的 OSIntNesting == 0
→ 读取 OSLockNesting == 0
→ OS_SchedNew() 的真实调用、局部分配、计算、返回释放
→ OSTCBHighRdy = OSTCBPrioTbl[OSPrioHighRdy]
→ 停在原 OSPrioHighRdy != OSPrioCur 判断
```

生产唯一上层接口：
`V293_OSIntExit_dispatch_prefix_execution`，文件
`certiucos/v293/proofs/V293OSIntExitDispatchExecution.v`。

## 2. 前提与实际得到的结论

前提是实际函数 lookup、全局/局部绑定、非空 ready/task/table 不变量、可读解码表、high/target/nesting/lock 的可写资源和可保留 frame。**不要求调用方提供整个语句、callee、分配或存储已经执行的证明。** nesting 入口为1、lock为0；不固定当前优先级，也不在主接口中假定优先级比较结果。

证明内部从资源构造真实 `store`，复用已证 `V293_ready_dispatch_call`，而不是重新定义一个空调度器。结论包括同一连续 `cstepstar`、更新后的 high/target、仍有效的 ready/task 资源、nesting=0/lock=0、真实分配块的释放，以及字节 frame。

frame 的确切范围是：排除 target **整个块**、high 所在单字节、nesting 所在单字节。没有声称更强的全堆单字节更新等式或任何别名条件下都不变。

## 3. 事前冻结的对照与独立正控

`audit/logs/stage196-interrupt-dispatch-execution/protocol.json` 在新 Coq 文件之前冻结。入口空间资源独立构造，没有从成功 trace 倒推入口。

| 对照 | 保持不变 | 唯一改变 | 机器证明的观察 |
| --- | --- | --- | --- |
| 最后一层正控 | 非空 task/ready/table、真实 callee、计数器19、canary99 | nesting=1 | 实际调度到 priority4、目标为 ready TCB |
| 嵌套对照 | 同一个程序与其他物理字节 | nesting 字节1→2 | 真实递减为1后结束；high仍88、目标仍旧waiting、计数器仍19 |
| 删除递减 | 同一份 nesting=1 物理输入、同一 callee | 仅去掉 decrement、执行原 guards | 实际选择 skip；high与目标不更新 |
| 优先级比较 | ready/table/tasks/nesting/lock/counter/canary、相同调度前缀 | current 字节4→6 | 原比较由 false 变 true，控制流真正到各自分支 |
| 同优先级结束 | current=4，与选中值相同 | 无额外改变 | 完整中段执行到 skip；目标已更新，counter19/canary99不变 |

`DXcurrent_only` 和 `DXnesting_only` 是除指定一个地址外的**全堆逐字节等式**，不是只检查几个相同 load。此输入对照等式不等于生产接口的全堆更新方程。

同优先级正控实际走完中段；早期 guards 跳过不被算作下游 callee 正确的证据。different-priority 对照仅执行到原 true 分支入口，**没有执行 counter++ 或 OSIntCtxSw**。fixture 的 switch 函数确实没有定义；因此不能把 true 分支入口当作实际切换完成。

## 4. 可信度与可重复验证

证据目录：`audit/logs/stage196-interrupt-dispatch-execution/`。

- `source-check.json` / `source-recheck.json`：临时重建授权修复源码，对 OSIntExit 与 OS_SchedNew 的配置后函数体、源行、配置及哈希分别核对，退出时删除临时源码目录。
- `body*.json/log/v.snapshot.txt`、`probe*.json/log/v.snapshot.txt`：逐次编译源码和真实退出码，失败也保留。稳定身份由 `stable-compiles.json` 指定。
- `trust.json` / `assumptions-by-root.json`：本步生产及 probe 的26根逐根 `Print Assumptions`，并递归 `coqchk` 两个入口；只接受原信任集合。
- `full-tests*.json`：两轮全量2144项，保留旧423失败、1错误及原有序ID。新增5项结构回归不替代 Coq 语义证明，不声称严格语义TDD。
- `build.json` / `project-audit.json`：成功；`audit.json` 保留旧源码证据身份过期失败；`whitespace.json` 保留旧 framework 空白失败，不放宽验收门。
- `baseline.json` / `verification.json` / 最终 manifest：逐哈希核对旧33047文件；只允许文档前插、工程清单追加和构建依赖文件变化。新可复用 Coq 产物保留，一次性信任驱动及缓存备份经登记后清理；原算术缓存恢复。

## 5. 未覆盖的范围与下一步

本步仍是 ADR-0005 显式临界宏抽象下的**局部、不交错中段**。没有把它接成 nesting=1 的完整 OSIntExit 调用入口、临界区与返回。GE/fixture 是独立存在见证，不是初始化可达性证明；current=6 对照不声称对应当前TCB的一致性。

尚未证明真实任务切换、原端口语义保持、生产 ISR/LocalInv、完整 WFFunEnv、初始化与模拟，也没有整核 GOOD_OS。coverage 六门仍为 `94 / 1 / 1 / 1 / 1 / 0`。不将本步登记成新增函数全覆盖。

下一步优先把已执行的同优先级中段接回完整抽象函数调用（分配、进入/退出临界区、返回释放）；真正切换分支须另用框架接受的任务切换边界连接，不能用 identity callee 冒充。第一阶段 GOOD_OS 与 K1–K4 同程序回归闭合前不启动 uCOS3。
