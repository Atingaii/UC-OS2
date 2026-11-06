# 第148步：OSTimeTick 的共享时钟递增

## 本步解决什么

此前已有原 `OSTimeTick` 的物理执行：局部分配、CPU hook 边界、临界区、任务链表循环以及返回释放。但这些执行结论没有把 `OSTime++` 与抽象状态 `ostmid` 连接起来。仅证明物理变量加一，不足以说明 getter、setter 和 tick 使用同一个抽象时钟。

本步保持 C、配置、已有 AST、框架和旧证据不变，新增 `V293TimeTickShared.v`，复用 getter/setter 的 `V293_time_shared_inv`。

## 稳定接口

| 接口 | 已证明内容 | 仍需调用方提供 |
| --- | --- | --- |
| `V293_tick_clock_write` | 原 `now = now + 1` 的 Hoare 规则，物理写入后推进原 `spec_prim_step`，重新建立共享 core | core 所有权、全局名字绑定、`NoAbs li`、`CurLINV` frame |
| `V293_tick_clock_with_tail` | 原右结合的 `encrit; increment; excrit; tail`，不替换 AST | clear IRQ、合法中断栈界、独立 tail 证明 |
| `V293_tick_clock_disabled` | IE=false 时真实压栈、写入、弹栈 | 显式持有 core；不是从 ISR 可达性自动获得 |
| `V293_tick_stopped_shared_suffix` | `OSRunning != 1` 时原完整 post-hook 尾段；原 while 分支保留但不执行 | 可读取 guard 字节、共享 Inv、名字与局部 frame |

写入规则从已有计数器所有权规则推出实际表达式求值和 store，不把它们作为接口前提。时钟类型为32位无符号整数；不增加“未溢出”前提，包含最大值回绕至0。抽象步只替换 `ostmid`，其余抽象槽原样保持。

`V293_tick_clock_action` 是时钟组件动作，不是整个任务唤醒／ISR 规格；不能因定义了动作就认为整核抽象 tick 已接通。

## 单因素消融

协议在证明前记录于 `logs/stage148-tick-shared-clock/protocol.json`。

1. **省略抽象更新**：同一非空输入内存、同一原赋值、同一执行后内存 `Mf`。两侧物理读取均为38；抽象时钟仍37的一侧不能满足共享 core，更新为38的一侧可以。负例不是入口早拒绝，也没有删除实际物理写入。
2. **错误结果**：初始抽象时钟仍37，只把候选结果38改为39。原 `spec_step` 拒绝39；同一输入允许38。
3. **回绕**：单独检查最大无符号值加一后的抽象步，不以范围假设排除边界。

空间实例含真实 current 指针与4字节时钟，TCB/ECB 表为空；它是局部非空可满足性和写入消融，不是完整初始化或活跃任务入口。

## 检查与证据

- `audit/probes/V293TimeTickSharedProbe.v`：实际执行、物理／抽象一致性、错误候选、frame 及回绕检查。
- `logs/stage148-tick-shared-clock/`：每次成功和失败编译都保留源码快照与退出码。
- `trust.json`：独立 `Print Assumptions` 与 `coqchk` 实际结果。
- `checkpoint-report.json`、`verification.json`：最终只读核验结果。没有这些成功记录时，不把本页的检查计划当成已经通过。
- Python 新测试只核对身份和接线，不冒充 Coq 语义证明；原失败集合另行比较，旧证据不改写。

本次实际检查：16个新根的假设闭包通过，独立 `coqchk` 检查316个活动模块＋35个额外探针模块通过；使用的经典逻辑和函数外延性假设不超出原允许集合。构建及6项新增测试通过；全套1870项仍为原423失败／1错误，失败项身份集合相同。`make audit` 仍因旧 `stale function evidence input identity` 退出2，`git diff --check` 仍报告旧 `inferules.v:581–586` 空白，不记为通过。

27061份旧文件身份复核只允许新增说明前缀、工程清单追加及生成的依赖清单变化。清理前逐一核对8个目标，只删除本任务一次性 Trust 产品及两份缓存备份，恢复原缓存；保留所有成功／失败快照、日志与可复用 Coq 编译产品。

## 明确边界与下一步

这仍不是整个 `OSTimeTick` 的 `WFAPI/WFIFun`。CPU hook、运行中任务的倒计时／唤醒及其抽象任务表和 ready bitmap 更新、活动 ISR 安装与退出，尚未接入生产全局 Inv。临界区退出后允许其他任务更新时钟，不能把出口的物理值固定为当前 tick 的结果。

源码函数六门信用仍为 `94 / 1 / 1 / 1 / 1 / 0`；本步不新增函数覆盖信用。完整生产 `Inv/WFIFun`、初始化、源码级 `GOOD_OS` 与同程序 K1–K4 仍开放，uCOS3 不提前启动，总目标保持 active。

下一步优先把原任务链表循环的倒计时／超时操作连接抽象任务状态和 ready bitmap，再合并完整 tick 生命周期，而不是继续把独立执行实例记成整函数完成。
