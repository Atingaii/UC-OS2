# 第221步：就绪共享不变式与中断入口／返回 builders

## 这一步在补什么

第220步已有同一个 ready/TCB/storage Inv 下的退出函数证明和函数环境，但“函数正确”不等于“整个中断正确”。真实 ISR 还要从中断入口提供的资源走到函数调用，并在结束时满足中断返回的资源要求。本步只补这个包装的两端，不假设中间调用的前置条件已经成立。

固定 C/config/AST、`INUM=2`、框架、tactics 和全部旧证明保持不变。四个配置后 C 函数仍按源码哈希核对；没有新增源码补丁。

## 可以怎样理解

| 对象 | 直观意义 | 本步结果 |
| --- | --- | --- |
| `BuildintPre` | 框架为中断入口生成的真实资源清单 | 展开它，取得当前 ISR 位、栈、关中断状态、ready/TCB/物理存储和线程资源 |
| `eoi` | 仅清除当前中断位的原语 | 用原 `eoi_ieoff_rule` 证明；incoming ISR 全 clear 时得到全 clear 的结果 |
| `SWINV` | 可供调用／切换边界使用的共享不变式 | 在同一 Inv 下重新关闭，不替换成另一个更弱的 Inv |
| `IRINV` | 中断返回需要的不变式 | 从完成资源、非空 ISR 栈与 `SWINV` 构造，保留线程资源 |
| `BuildintRet` / `exint` | 真实返回资源清单和返回原语 | 用原 `iret_rule` 连接；没有假设整个 ISR 已正确 |

原框架 `starinv_noisr I low 0` **仍包含 low 这一项**，不是空区间。因此向量0也包含索引0处的 ready core。本步按这个定义证明，未改框架或人为排除向量0。

## 文件与稳定接口

- `certiucos/v293/proofs/V293InterruptReadyBoundary.v`
  - `V293_irq_ready_builder_resources`：真实入口资源展开。
  - `V293_irq_ready_eoi_closed`：入口 builder → 实际 EOI → 同一共享 Inv。
  - `V293_irq_ready_return_resources`：完成资源 → 真实返回断言。
  - `V293_irq_ready_exint`：真实返回 builder 与原返回规则连接。
- `audit/probes/V293InterruptReadyBoundaryProbe.v`
  - `IQbuilders_nonempty` / `IQreturn_builder`：两端断言满足实例。
  - `IQactual_endpoints`：合法向量0的两条分开的实际 Hoare 判断。
  - `IQsingle_bit_control`：单个 incoming 位变化的代数对照。
- `tests/test_interrupt_ready_boundary.py`：5项结构回归；不把字符串检查称为语义测试或语义 TDD。
- `audit/logs/stage221-interrupt-builder-boundary/`：协议、失败快照、编译、假设、递归内核检查、构建、全量回归、旧文件字节保护、清理和冻结证据。

## 为什么不是“空成立”

实例复用 `PPnonempty` 已有真实前缀产生的物理堆，包含真实 `V293_tcb_type` 的任务记录、ready 资源与 dispatch/control 存储；从该堆分离共享资源与当前线程只读份额。再通过已证明的断言稳定性调整局部环境与辅助状态，构造两端 builder 的满足状态。

这证明的是**断言有满足实例**。它没有给出从初始化到 ISR 的可达执行，也没有把两端实例连接成同一条完整 ISR 执行。实例的中断抽象规格选用 `spec_done None`；不能把这个选择冒充生产 ISR 的抽象行为规格。

## 单因素对照与范围

只把 incoming ISR 的向量1从 false 改成 true，其他位保持不变；当前处理的向量固定为0。0、1均合法，因为原框架 `INUM=2`。EOI 清向量0后，向量1仍为 true，所以不能推出全 clear。

这是 ISR 位更新的代数／边界对照，**不是两份完整函数或 ISR 执行**。它说明本证明的全 clear 假设不能直接删除；不说明所有嵌套 ISR 都不正确，也不替代同程序 K1–K4。

## 验证与保留的失败

最终实测数值见本目录 `verification.json`，可用 `recheck-checkpoint.py` 只读核验冻结证据。新模块全部18根逐根检查假设，并对两个入口模块及递归依赖运行 `coqchk`；保持已有假设白名单，不新增公理。

全量回归的历史基线为2264项、423失败、1错误；新5项加入后为2269项。失败与错误的旧 ID、顺序必须完全相同，不能称全量绿。既有 `make audit` 的 stale function evidence 错误，以及旧 `inferules.v` 空白差异继续保留，不重写旧证据制造通过。

## 接下来从哪里开始

先读 `V293_irq_ready_eoi_closed` 的结论：它提供“共享资源已关闭”的边界，而不是 `OSIntExit` 的完整动态前置。下一步要在同一个 Inv、同一个 Spec 中连接原 ISR 的 `OSIntEnter`／`OSIntExit` 调用，逐项从实际资源和控制字段推出 callee 前置，尤其是运行状态、嵌套计数、锁、lookup 和不同优先级的条件。缺少的语义必须证明，不能直接增加“callee 前置成立”的假设。

完成这些后仍需生产 ISR 规格、`WFInt`、其余 API、初始化、源码级 `GOOD_OS` 和同程序 K1–K4。然后才进入老师要求的 uCOS3。当前六门覆盖仍为 **94/1/1/1/1/0**，总目标保持 **active**；未提交或推送。
