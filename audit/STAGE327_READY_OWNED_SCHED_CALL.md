# 第327步：联合就绪资源穿过真实调度调用

## 这一步解决什么

第326步已把原始客户端的常量延时调用接到调度入口，并在阻塞后的同一堆拥有完整任务记录、就绪位图、优先级表和共享字段。此前已有末端切换的可达轨迹，但“能执行到这里”和“执行过程中联合资源保持完整”不是同一个结论。

本步只补后者的一段：从真实 `OS_Sched` 调用进入，实际分配并初始化 CPU 保存槽、进入临界区、通过两个零嵌套判断、调用 `OS_SchedNew`、释放其局部 y 并返回、发布目标 TCB、比较优先级并更新切换计数器，止于 switch-or-skip 边界。没有重复运行延时阻塞前缀，也没有改 C 源码或扩大授权修复范围。

## 稳定接口及其真实前提

- 生产文件：`certiucos/v293/proofs/V293ReadyOwnedSchedCall.v`。
- 上层稳定接口：`V293_owned_sched_call`。
- 输入是程序绑定、全局字段绑定、lookup 字节读取、联合 `V293_ready_full` 与拥有写权限的调度字段／frame，不是预先成功的执行、store 或 `SWINVt`。
- 当前任务不必仍为 ready：延时后它可以已经阻塞，非空就绪表中的其他任务仍可被选择。
- 输入明确要求 `GoodInvAsrt R`，才允许 frame 穿过实际 lenv、IE 和临界栈变化；不声称任意辅助状态敏感的断言都能被运输。
- 入口为无中断执行、空 ISR 栈，临界进入后 IE=false。由这些真实侧条件建立 flags，再闭合 `SWINVt`；不是无条件把 `ready_full` 改名为切换不变量。

输出在同一最终堆联合拥有 `SWINVt`、最高优先级字段、仍为旧值的当前优先级缓存、更新后的计数器、目标 TCB、CPU 保存槽、两个 guard 和 frame。优先级表只在 `ready_full` 中拥有一份，不能再把它复制进残余资源。

辅助 y 的释放见证是 `free Tint8 byblock My = Some Mh` 和 `get Mh (byblock,0) = None`，准确位于 helper 返回边界 **Mh**。这不是最终 Mf 整个 byblock 的 fresh 定理。调度器 CPU 保存槽仍在调用栈上，具有四字节写权限，尚未释放。

## 双任务实例如何连接原全局调用

`audit/probes/V293ReadyOwnedSchedCallProbe.v` 的 `DOglobal_sched` 没有执行前提，对任意计数器与两种初始 IE，从第326步的同一原始客户端调用继续到原全局 `DXrun` 的实际 switch 前位置。

实例从阻塞后的任务表与选择关系推导出优先级6／`OwnershipWaiting`，不是把该选择作为外部 oracle 输入。旧任务优先级4已经等待3个 tick，不能再冒充 ready。末端拥有：

| 项目 | 实际结果 |
| --- | --- |
| 当前 TCB | 仍为原阻塞任务；本步尚未 switch |
| 最高就绪优先级 | 6 |
| 已发布目标 | `OwnershipWaiting` |
| 当前优先级缓存 | 仍为4，未声称同步 |
| 切换计数器 | 模 2^32 的 c+1，最大值加一为0 |
| 原参数、局部 y、CPU 保存槽、canary | 同一资源中保留；canary=99 |
| CPU 权限 | 原延时 CPU 槽与新调度 CPU 槽均有四字节写权限 |

`DOcontinuation` 仅用于局部 helper 前缀；全局延时外层通过 `V293_local_steps_global` 正确包入。不能把局部 continuation 冒充已经包含外层调用的完整全局栈。

## 事前固定的单因素对照

协议：`audit/logs/stage327-ready-owned-sched-call/protocol.json`，SHA-256 为 `b0cb6670fec4745387c7f8786e8eada5873732b639706d58132cf3601a24061b`。

`DOlate_ablation` 保留同一实际执行、最终堆、联合资源、helper 释放见证、CPU 权限和 canary，**只在末端计数观察门**把期望值从实际 c+1 换回旧 c。正确观察成立，旧值观察被拒绝；`DOcounter_changes` 对所有32位值排除 c+1=c，包含回绕。

这检验的是晚期观察门，不是修改程序后的完整执行，也不是删除真实 increment 后程序仍能跑通的证据。不能据此推出每个下游机制都已独立通过消融。另删除了未被证明使用的 `GRest` 中间断言；稳定编译和递归内核复核检验简化后的最终文件。

## 如何复核与阅读结果

1. `source-replay.json`：按冻结源码重新物化、预处理并核对三个实际 C 函数。
2. `stable-production-{1,2}.json`、`stable-probe-{1,2}.json`：最终源码各独立编译两遍，记录前后身份。
3. `trust.json`、`assumptions-by-root.json`：13个新证明根的依赖和递归 `coqchk`，只接受项目既有经典逻辑与函数外延依赖。
4. `new-tests-02.*`、`full-tests-02.*`、`build.*`、`project-audit.*`：最终回归；首次测试也保留。Python 测试检查身份与连线，不替代 Coq 语义证明。本步新测试按“基线前缀保留且本模块唯一注册”检查项目清单，允许未来继续追加，不重复上一阶段严格快照相等的问题。
5. `verification.json`：本步最终实测总表。全量2868项中439失败、1错误：旧438失败与1错误的 ID 及顺序保留，新增一项为第326步历史身份测试在第141行严格比较旧 `_CoqProject`，因此拒绝本步尾部新增模块。该旧测试原样保留，**全量回归及无新增失败门禁均未通过**，不把已定位原因当成豁免。`make audit` 的旧证据身份过期与 `git diff --check` 的旧六处空白也照实保留。
6. `cleanup-review.json`、`cleanup.json`：逐项确认后只删除一次性信任检查产物和已恢复的缓存备份；失败快照、旧材料、可复用 Coq 对象保留。恢复旧 Makefile 缓存字节后另将其时间戳设为早于项目清单，确保下一次 `make build` 会重新生成而不会漏编新模块；见 `makefile-timestamp-restoration.*`。

## 尚未完成与下一步

这是有限、无交错的真实调用前缀及联合资源结论，**不是完整 API**，**不是全局记录不变量**，**不是全局 ProgSim**，**不是 GOOD_OS**；没有把函数六阶段覆盖升级为完整函数证明。

下一步应让这份联合资源实际跨过原 switch，并处理旧任务恢复、临界区退出和 return；不能只复用历史切换可达性就声称所有权已跨界。优先级缓存同步、统一 WFInt、初始化、同程序 K1–K4 和最终源码级 GOOD_OS 仍开放；阶段一完成后才按老师要求开始 uCOS3。两阶段总目标保持 active。
