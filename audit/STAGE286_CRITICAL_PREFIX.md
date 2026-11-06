# 第286步：临界原语、饱和递减与双 guard 接入 TaskSim

## 本步结果与准确起点

唯一生产公开接口为 `V293_exit_critical_prefix_TaskSim`，证明块为：

`encrit; (OSIntNesting 饱和递减; nesting/lock 双 guard; dispatch)`。

这里的 `encrit` 是框架的真实临界原语，使用它的实际 `loststep`，不是把它当作
不改变辅助状态的普通 C 小步；入口已关闭中断，压入的保存值为 `false`。
生产证明逐一承担 TaskSim 的七类义务，涵盖任意兼容外部 frame。
源码定位为固定 V2.93.01 的 `os_core.c:702–707`；C、配置、AST、框架和
ADR-0010 均未修改。它不另行证明 C 端口函数与临界原语的 refinement。

该块是局部组合接口，不是原完整函数的入口或全部语句结合方式。
**公开接口仍有 dispatch TaskSim continuation 前提，尚未与第285步 helper 后缀整合。**
不能把继续执行的假设当作已经证明了调度和切换。

## 如何推出读、写与 guard

接口要求两个 typed owned 字节单元：`nesting=n`、`lock=0`，其中 `n<=1`；
其余资源 `R` 满足 `GoodInvAsrt R` 并蕴含物理 `CurTid`。
不要求调用者提供 load/store 成功或执行轨迹。

- `n=0`：正数判断为假，不发生写入，两个零判断成立；
- `n=1`：由完整所有权构造实际 store，把 nesting 写成0，保留 lock 与其余资源，
  再由更新后的所有权推导两个零判断；
- `encrit` 保持内存、中断寄存器与抽象状态，并将 `false` 压入临界保存栈；
- `GoodInvAsrt R` 用于跨辅助栈改变搬运资源。没有把整个 `SWINVt` 宣称为 Good。

七类模拟义务来自生产定理；实际执行对照不替代模拟证明。
范围不包括 `n>=2`、lock 非零的提前返回分支，也不包括一般中断开启状态。

## 非空实例与单因素执行对照

`audit/probes/V293ExitCriticalPrefixProbe.v` 使用两个真实字节和一个半权限当前指针
构成非空物理堆，共6字节。`EPnonempty_prefix` 对 `n=0/1` 实例化公开定理。
其中 `EPdispatch` 实际证明 `sret`、空局部释放、回到 client 的 TaskSim，
不是把 dispatch TaskSim 当作实例的假设。

**实例使用 synthetic sret dispatch 和 Post=True，只证明前缀接口非空。**
它不是原 helper/switch 后缀，不是原完整活跃调用可达性，也不证明内核后置性质。

`EPsingle_decrement_control` 在同一初始堆、环境、continuation、双 guard 和 dispatch 下，
只删除 `V293_OSIntExit_decrement`，比较框架真实 `cstepstar`：

| 初始 nesting | 原递减与双 guard | 只删除递减 |
| --- | --- | --- |
| 1 | 真正 store 为0，选择 dispatch | 原堆仍为1，选择跳过分支 |
| 0 | 无写入、原堆到 dispatch | 同一原堆到 dispatch |

这是局部递减/guard 的单因素执行消融，不是完整外层调用执行消融，
也不单独证明 lock、helper、计数或 switch 的必要性。
`EPencrit_frame` 另在任意物理堆上给出真实临界原语执行，
全后继和任意 frame 的模拟由生产桥承担。

## 验证与证据

前瞻协议、源码身份、所有成功/失败编译快照、稳定编译、逐根假设和递归 coqchk，
位于 `audit/logs/stage286-critical-prefix/`；最终实测以 `verification.json` 为准。
允许基础仍仅既有 classic 与 dependent functional extensionality，无新增公理或占位。
Probe 编译期间的缺类型注解、非 export 导入不可见和分支元变量问题的失败均保留。

正式全测在恢复本步开始时的既有 `.lia.cache/.nia.cache` 后运行，
按第285步正式结果核对旧失败身份和顺序，不删除不利结果或放宽检查。
README 与 VERIFICATION_STATUS 仅前插，旧历史字节与旧冻结证据保留；未提交/推送。

## 距离最终目标还差什么

- 将本接口的资源与第285步 helper 调用后缀合并，消去 dispatch continuation；
- 补原外层 running 判断、saved 局部分配、端口临界调用、等优先级和提前返回分支；
- 保留完整 unmap 所有权，证明原完整调用的同一非空入口 TaskSim；
- `si=nil`、ISR 全清、空 LINV、强 current guard 缺口及 ADR-0010 边界不变；
- 不是无条件 WFInt/WFIFun，GOOD_OS 与同程序 K1–K4 未闭合，uCOS3 未开始。

最终目标仍是先完成固定 uCOS2 的整核证明，再按老师要求做 uCOS3；目标 active。
下一步应优先合并前缀与后缀的资源接口，而不是继续增加只有执行轨迹的替代结果。
