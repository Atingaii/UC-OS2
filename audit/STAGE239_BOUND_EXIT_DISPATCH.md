# 第239步：同一地址绑定 LocalInv 下的实际换任务 dispatch

## 1. 为什么接着做这一步

上一步把 `running/nesting/lock` 的地址绑定纳入候选 `LocalInv`，连接了真实 `BuildintPre → EOI → OSIntEnter`。但原 Exit 的换任务证明写死了旧 `V293_shared_li`。仅把新 LocalInv 放在 Enter 的规格里，不能据此断言 Exit 或整套中断环境也能工作。

本步不改 C、配置、AST、框架、旧证明或 ready/TCB/storage Inv；只重证依赖 LocalInv 的调用与换任务链，连接同一候选 LocalInv 下的实际 changed dispatch。主文件：

- `certiucos/v293/proofs/V293OSIntExitLocalDispatch.v`
- `audit/probes/V293OSIntExitLocalDispatchProbe.v`
- `tests/test_osintexit_local_dispatch.py`

## 2. 先看代码实际做什么

这里的 dispatch 是 Exit 已判断应调度之后的一段真实 AST，不是一个假定正确的抽象跳转：

1. 调用原 `OS_SchedNew` 本体，读取位图并写最高就绪优先级。
2. 从原优先级指针表取目标 TCB。
3. 比较最高就绪优先级与当前优先级。此定理处理二者不同的 changed 分支。
4. 增加切换计数器，把最高就绪优先级复制到当前优先级。
5. 关闭原 ready/TCB/storage Inv，应用框架的真实 `switch_rule`。

后置是被切出线程将来恢复时的 `SWINVt` 断言，不应读成“切换瞬间仍在执行旧线程”。

## 3. 新证明接了哪些接口

| 接口 | 证明内容 | 不能推导什么 |
|---|---|---|
| `V293_OSSched_local_storage_prefix_returned` | 对满足 `GoodLInvAsrt` 的任意 `li`，真实调度前缀返回并保留同一 `p_local li tid nil` | 不证明任意 `li` 都能完成后续 switch |
| `V293_local_exit_changed_tail` | 真实 counter++ / copy / switch；从保留的私有绑定取得当前线程 LocalInv | 不自动产生所需 LocalInv |
| `V293_OSIntExit_local_dispatch` | 连接上述前后缀 | 显式要求 LocalInv 可由保留资源取得，且可遗忘为旧共享 LocalInv；不是无条件运输规则 |
| `V293_exit_bound_body_lend` | 从原真实 bodydata 已有的物理资源与地址绑定建立新 dispatch 前置 | 不额外给全局绑定 frame，也不假设中间 Hoare 三元组 |
| `V293_OSIntExit_bound_dispatch` | 为第238步的具体地址绑定 LocalInv 消去上述两条蕴含义务，完成实际 changed dispatch | 不是整个 Exit 本体或 builders |
| `V293_exit_bound_dispatch_current` | 恢复后由保留绑定与当前线程标识恢复 `CurLINV` | 不是完整 ISR 返回 |

具体 bound 接口只保留原位图/TCB/类型关系、字节界限、changed 条件、frame 合法性和被调用函数的精确规格查找；没有把目标 Hoare 结论作为前提。

## 4. 地址绑定与内存值不要混淆

`LocalInv` 保存的是全局环境中三个名字对应的地址和类型，不是 running/nesting/lock 的值。值及内存权限仍由原 storage Inv 管理。地址绑定不拥有堆或抽象状态，即零资源足迹，**不等于逻辑上的 Aemp**：错误绑定仍会使它为假。

所以可以从同一个全局环境重复观察地址绑定，不是在复制可写内存权限。本步 `V293_bound_dispatch_add_globals` 单独证明这种重复观察；`V293_bound_dispatch_forget` 也只遗忘具体零资源绑定的逻辑条件，不声称任意拥有资源的 LocalInv 都能遗忘。

## 5. 防止空前置、循环证明和错误归因

- `LDbody_lend` 从原 `JBdata` 借用，不另造一套空间资源来迎合定理。
- `LDnonempty` 对任意切换计数器/后续抽象操作/临界栈给出同一个状态：原 typed bodydata 与新 dispatch 前置同时成立；并证明最高就绪线程不是当前等待线程。这不是初始化可达，也不是一条从启动到此处的执行轨迹。
- `LDactual_dispatch` 对真实 AST、独立写出的字面后置作实例检查；后置不是从目标定理打印或读取后自动生成的。
- `LDsame_local_invariant` 证明这里与 Enter 使用相同 LocalInv；`LDsame_scheduler_body` 证明调用的仍是原函数体。`LDscheduler_environment` 只是该调度函数的单函数环境，不是整个中断三函数环境。
- 第238步“同一物理堆、只改 running 全局绑定”的负对照原证据不变。它不是两次完整执行，只说明 builder 能区分错误绑定，不能替代本步对 dispatch 的独立 Hoare 与内核检查。

## 6. 来源、验证与不变项

先冻结协议，再编写本步模块。四个固定配置后函数 `OSIntEnter/OSIntExit/OS_SchedNew/OS_Sched` 从锁定源码重建并比对精确定义哈希。日志和逐次失败的源码快照均保留在 `audit/logs/stage239-bound-exit-dispatch/`。

实际最终结果见该目录 `verification.json`，其中保留全构建、逐根 `Print Assumptions`、递归 `coqchk`、新测试及全量测试的输出与身份。Python 检查只检查接口形状/来源/证据，不冒充语义测试或测试先行开发。

旧423失败、1错误必须保持原有顺序和身份；旧 `make audit` 的函数证据身份过期、旧 whitespace 六行问题不通过改门槛掩盖。六门仍为 `94/1/1/1/1/0`。

## 7. 当前边界与下一步

**旧三函数环境未迁移。** 本步不是整个 Exit，本体入口、其余分支、通用 builders、共同函数环境还需逐层接入同一个 LocalInv；之后才能讨论与 Enter、`iret` 的连续连接。

因此这不是 `WFInt`，不是 `GOOD_OS`，不完成同程序 K1–K4。候选地址绑定 LocalInv 也不等于生产 ISR 的最终全部不变量：lookup 内容、current/TCB 对应、实际中断规格以及初始化可达仍需处理。uCOS3 未开始，不提交、不推送。

学习顺序：先看本页第2节的真实执行顺序，再看 probe 的 `LDnonempty` 与 `LDactual_dispatch`，最后回到生产文件的 `V293_exit_bound_body_lend` 和 `V293_OSIntExit_bound_dispatch`。先区分“前置有实例”“该片段被证明”“整个系统闭合”这三件事，再继续整体 Exit。
