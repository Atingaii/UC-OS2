# 第311步：实际中断 builder 的调度分支连接任务切换

## 1. 本步解决什么问题

上一阶段的原物理切换／高层调度匹配，需要调用者提供切换前资源。本步让实际、未加 quiet 过滤的 `BuildintPre` 产生这些资源，执行同一个程序的 EOI、Enter、normalized Exit 和缓存拷贝，再将**同一后继堆**交给原切换规则。

不新增内核行为、过渡语义或调度算法，不改 C／配置／原 builder。固定源码身份和两类授权修复保持不变。

## 2. 逐步理解这条链

| 步骤 | 做了什么 | 可检查的观察 |
| --- | --- | --- |
| handler-entry | 原 builder 拥有 ready／TCB／storage 资源，running=1、nesting=0、lock=0 | 控制捕获来自同一个输入堆 |
| EOI、Enter | 清除当前 ISR 并执行完整 Enter 调用 | nesting 从0变为1；非 nesting 块的字节保持 |
| Exit | 实际执行 normalized Exit 和 `OSSchedNew` | 选中最高就绪任务，nesting回到0，目标指针写入实际内存 |
| handoff | 执行源码边界已采用的优先级缓存拷贝 | 原缓存6变为新优先级4，不把旧值假装成新值 |
| switch切点 | 将该后继堆装入实际非空任务／环境／辅助状态映射 | 原 `lpstep` 更新物理当前指针；原 `hpstep` 更新抽象 `curtid` |
| 终态观察 | 读取切换后的同一内存和抽象状态 | 二者都为最高就绪任务；三个控制字节仍是1、0、0 |

非空实例中，当前为 `OwnershipWaiting`（优先级6、阻塞），最高就绪为 `OwnershipReady`（优先级4）。没有将“仍在等待消息的任务”改成 ready；切换的是另一个已经就绪的任务。

## 3. 稳定接口及真实前提

生产文件：`certiucos/v293/proofs/V293InterruptBuilderDispatchSwitch.v`。

上层接口：`V293_builder_dispatch_prefix`。它不接收执行轨迹作为前提，而从实际 builder、程序函数绑定、输入控制捕获、任务／就绪条件和两个显式数据关系，构造有限局部执行。前缀终点是原 `switch target`，保留完整 `excrit`／`sret`／Exit调用／`exint` continuation、保存的 CPU 局部环境和临界状态。

两个数据关系不能隐藏：

1. 输入优先级缓存与当前任务的真实优先级一致。
2. 输入256个 unmap 查表项符合 `V293_ready_lookup`。

旧 storage invariant 只保证类型和可写所有权，不保证以上数值关系。本步将这两个前提放在**输入堆**；通过 Enter 的实际字节帧传到后继堆，不在执行后重新任选缓存或查表内容。这些关系的初始化及全程序保持仍待证明。

辅助资源桥 `V293_builder_dispatch_resources` 从真实 storage 单元提取写权限，将同一全局环境中的命名目标单元落实为物理地址，并恢复原 `SWINVt`。没有将控制字节塞入旧四键抽象状态。

## 4. 非空实例如何防止“换堆”

实例：`audit/probes/V293InterruptBuilderDispatchSwitchProbe.v`。

- `BDprepare` 从原 `QJentry_nonempty` 提取 builder 子堆 `M`，保留它与完整 canonical 堆的 `join`。
- 不能直接把完整 fixture 的缓存／查表读取当成 `M` 的读取。`BDsubheap_read` 先由 `M` 的真实 typed storage 所有权读出值，再用 `load_mem_mono` 提升到完整堆，利用读取唯一性确定原值。256项由数组成员与 storage 聚焦证明逐项覆盖。
- 原 shared core 占有全部抽象键，证明抽象帧为空；因此同一输入抽象状态确实是 `RIabstract OwnershipWaiting`，不是另给的抽象 oracle。
- `BDcompleted_match` 先获得该实际局部前缀，再调用第310步 `V293_control_switch_forward`。低层切换使用 `BDglobal`，其 OS 函数单元仍是前缀的 `RDprogram`。
- 同一 `Ms` 作为切换输入，同一 `Mf` 用于物理指针、缓存及控制读回；就绪任务代码保持，切出任务保存 `BDK`，辅助栈保留 `[0]` 和 `[false]`。

这里是**有限局部 handler 前缀 + 最终全局切点匹配**。尚未把整段前缀提升为全局 handler trace，未证明任意全局交错安全；不得合称完整 handler simulation。

## 5. 单因素观察对照

方案事先记录于 `audit/logs/stage311-builder-dispatch-switch/ablation-protocol.json`。

先由 `BDcompleted_match` 获得实际 builder 前缀、低层切换、高层切换及终态读取。两份测试只把最终期望的抽象当前任务从 `OwnershipReady` 改成 `OwnershipWaiting`；程序、执行见证、内存、证明脚本都不变。

基线编译通过，变体在最后的 `exact Observed` 处失败，错误上下文保留已完成的 Prefix／Low／High／Physical／Cache／Captured／All。它验证的是“完成轨迹后的精确终态观察”，**不是程序机制删除实验**，也不能证明所有潜在错误都能检出。

## 6. 对抗式复核与界限

| 质疑 | 本步处理 | 仍开放的部分 |
| --- | --- | --- |
| builder 是否经过 quiet 过滤而避开调度？ | 主接口使用未过滤 `BuildintPre`，输入控制为1、0、0 | 其他输入分支复用已有结果，并未升级为全程序覆盖 |
| 是否偷偷要求一条执行轨迹？ | 主接口构造实际 EOI／Enter／Exit／copy；非空实例无执行前提 | 有限执行存在性不推出所有交错安全 |
| 是否直接借用了另一实例的后继堆？ | 子堆读取、same-P 前缀和末端切换在同一见证上连接 | 未证明整段前缀的全局映射提升 |
| typed storage 是否被当成缓存一致性？ | 两个数值耦合义务显式列在输入前提 | 初始化及各 API／ISR 的关系保持 |
| 是否更换调度算法或补一条新切换语义？ | 复用原 `lpstep`／`hpstep` 和固定 scheduler | 统一控制状态接口及框架健全性 |
| 观察变体是否只在早期检查被拒？ | 失败定位在真实轨迹完成后的最终观察 | 不是完整错误模型或程序删除消融 |
| 是否完成了中断返回或后继模拟？ | 明示终点是 switch 切点及其一步后继，保留原 continuation | 后继 `ProgSim`、`excrit`／返回与统一 `TaskSim` |
| 是否算整核验证或 uCOS3 成果？ | 不算；不设置 `full_target_linked` | `GOOD_OS`、同程序K1–K4完成后才进入uCOS3 |

## 7. 验证记录

所有命令、成功与失败日志、源码快照、递归信任复核和历史身份检查放在 `audit/logs/stage311-builder-dispatch-switch/`。最终数字以该目录的 `verification.json` 为准，不覆盖旧失败记录。

| 验证项 | 实测结果 |
| --- | --- |
| 生产源码与非空实例 | 各连续编译两次通过，源码身份不变 |
| 递归信任复核 | 11个根通过 `Print Assumptions` 与递归 `coqchk`；仅使用既有经典逻辑／函数外延性 |
| 增量构建 | `make build` 通过 |
| 项目范围检查 | 385个活动V293文件、103个framework／tactic文件，通过 |
| 新增回归 | 7项全部通过 |
| 完整回归 | 2745项，437失败、1错误；与第310步的失败／错误ID及顺序完全一致，无新增失败 |
| 终态单因素观察 | 基线通过；变体在完成轨迹后的最终观察处失败 |
| 既有审计 | `make audit` 仍因旧 `stale function evidence input identity` 退出2，不记为通过 |
| 既有空白检查 | 六处inferules尾随空白，退出2；输出与第310步逐字节相同 |

完整回归用时约92.92秒；递归 `coqchk` 用时约416.34秒。上述局部通过不抵消既有失败，也不授予任何函数 `full_target_linked` 资格。

## 8. 接下来应做什么

优先把这条同程序的局部执行链提升到含真实中断保存上下文的全局任务映射，并连接切换后 continuation；然后在统一控制状态接口上证明全交错模拟。并行的证明义务（非本步完成）包括缓存／lookup关系的初始化与保持、完整初始化和功能族纵向连接。

最终目标没有变化：先完成同一固定程序的 uCOS-II V2.93.01 `GOOD_OS` 与同程序K1–K4，再按教师附件进入uCOS3。当前没有提交或推送 Git。
