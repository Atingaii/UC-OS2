# 第262步：完整 OSIntExit 非调度函数路径接入原 ProgSim

## 这一步实际推进了什么

第261步只从 running 判断之后的临界区开始。本步把固定 V2.93.01 的显式归一化函数从已求值调用入口接通：

`sfexec → 函数查找 → 任意 fresh Tint32 分配 → saved := 0 → running 判断 → 非调度临界区（如需） → 实际 sret/free/freeend → caller`。

生产稳定接口 `V293_exit_quiet_call_progsim` 只保留**最终 caller 端点模拟**，没有把初始化后、running 后、任意分配后的函数体模拟作为公开前提。`V293_saved_exec_entry_progsim` 覆盖每一个合法分配后继，不靠选择一个有利地址消除非确定性。一般 `scall` 接口还需要原 `InOS` caller 上下文。

固定源码：`csrc/upstream/v2.93.01/checkout/Source/os_core.c:693–736`，SHA-256 `96eef5dc1a519887499cffd8f9a6c8873b96978ed9646c42e52eb6992422fea5`。8项源码／配置身份和原行锚点由 source-identity.json 复核；没有修改 C、配置、AST、框架、Inv、LI 或 BDspec，也没有刷新旧函数覆盖证据。

## 真实入口界限：先记录修订，再实现

原 `InOS` 直接识别有绑定的 `sfexec`，但 `scall + kstop` 不因此成为 OS 代码。不能为终止 caller 伪造该前提。原 protocol.json 保持不变；实现接口调整前冻结的 protocol-amendment.json 明确：

- 生产接受 `sfexec`，或者带原 OS caller 上下文的 `scall`。
- 无 ProgSim 前提的独立实例用 `sfexec + kstop`，确实经过函数查找、分配、整个原函数体和返回释放。
- 不声称独立证明了任意 client 的 `scall → sfexec` 分类桥接。生产条件分支能处理已有 OS caller 的实际 `scall`。

这不是缩短函数体、改框架或把完整目标改成局部目标；它是保留原入口分类限制。完整函数的所有调度分支仍未闭合。

## 前提与精确结果

- 入口 IE=false，保留任意中断栈／临界栈后缀；沿用 ADR-0005 / ADR-0010 显式源码级抽象。`saved := 0` 是实际 Tint32 物理写入，不是读取硬件 IE 的证明。
- running 是合法字节。`run != 1` 时跳过临界区并返回完整原堆，不要求 nesting／lock 的读取义务。
- `run = 1` 时，要求原饱和减一后的调度禁用条件：`2 <= nesting` 或 lock 非零。只有 `pred nesting = 0` 时才要求 lock 绑定与加载。
- 减一操作、实际 guard、临界原语与释放仍走原 cstep/lpstep/ProgSim，包含全部后继、输出及异常义务，不另定义替代模拟关系。
- `V293_saved_free_write_byte` 和 `V293_saved_free_decrement` 在物理堆上证明不同块的字节更新与四字节释放可交换。任意 fresh saved 块释放后，整堆与分配选择无关；其他任务、caller 局部环境、辅助映射和保存栈恢复。
- 生产最终 caller 后续 ProgSim 仍是公开条件，不能宣称任意 client 已验证。

## 独立非空实例与单因素对照

`QPtyped` 通过真实 allocation/store 所有权规则在既有非空堆上增加独立 running 字节，保留 nesting、lock、ready 空间资源、TCB 指针、计数器及原 frame。这里证明的是同一物理堆的 typed 空间所有权；typed 结论用既有 CG 环境，不冒充已在新全局函数环境下建立完整 Inv。原 typed high=88 超过配置最低优先级12，不能作初始化可达证据。

`QPcomplete_quiet_simulation` / `QPstopped_and_running` 无 ProgSim 前提，独立通过原终止 caller 规则关闭后置端点。两者函数、入口、caller、任务、栈和其他堆字节相同，只改变 running 地址的一个字节：

| 输入／观测 | stopped | running |
| --- | --- | --- |
| running 字节 | 0 | 1 |
| 实际 running 表达式 | false | true |
| nesting 初值 | 2 | 2 |
| 生产接口对应返回堆的 nesting | 2 | 1 |
| 独立完整函数路径 ProgSim | 无前提建立 | 无前提建立 |

`QPrunning_only_changed` 证明其他全部地址不变；`QPrunning_flag_changes` 证明该字节确实不同；`QPguard_control` 检查实际原表达式；`QPguard_changes_return` 检查生产接口指定的完整返回堆。**这里没有另建完整有限返回 trace 定理**，不把最终堆函数的计算等同于独立 trace。实际程序连接由覆盖全部后继的生产 ProgSim 证明承担。

`QPsaved_choice_independent` 对任意 fresh saved 块直接给出实际 store 与 free 结果，不只检查选定地址；`QPnonvacuous` 从有限内存存在 fresh 块和独立 typed 空间见证排除不一致前提。第261步的栈原语对照不是本步完整变异程序的执行消融，不重复授信。

## 审查后仍保留的限制

不是完整 OSIntExit 所有路径，不是完整中断返回，不是 `WFInt`，不是 `GOOD_OS`；K1–K4 未闭合，uCOS3 未开始，未提交／推送。尤其调度切换后旧任务仍可能挂起，不能把它的 excrit/return 接到新任务上。IE=true 可中断区间、任意暂停 client、全局函数环境和初始化仍开放。

下一条主线是把已建立的真实调度前缀与原旧任务恢复契约连接，再合并非调度与调度分支；不能用这份非调度完整函数路径证明替代整核验收。

检查材料：`audit/logs/stage262-exit-quiet-call-progsim/`；所有编译失败快照保留，其中 probe06 的重型自动化在约31秒后终止，随后改为定向证明，不改写该失败。

## 实测结果

| 检查 | 结果 |
| --- | --- |
| 稳定编译 | 生产 prod20/prod21、实例 probe12/probe13；每对源码哈希相同 |
| 信任检查 | 11个生产根、10个实例根；递归 coqchk 通过，约532秒；749项输入未改 |
| 假设 | 仅既有 classic 与 functional_extensionality_dep |
| 构建／静态边界 | 通过；338个活动 V293 Coq 文件 |
| 新增回归 | 5项全部通过 |
| 全量测试 | 2475项；428个失败、1个错误；相对261步失败／错误 ID 及相对顺序不变 |
| make audit | 退出2：旧函数证据输入身份过期，未刷新旧门 |
| git diff --check | 退出2：既有 inferules.v:581–586 六行空白，未改框架 |
| 旧输入 | 1745项只有4项允许的文档／构建元数据变化 |

前一检查点在前向元数据登记后的拒绝保留，旧 manifest 未改。依赖只增新模块3行，旧字节不变。历史覆盖94/1/1/1/1/0未重新验收。清理前逐路径、字节、SHA确认，删除8项一次性信任产物与已恢复的缓存备份，共710959字节；保留源码、日志、全部失败和可复用 Coq 产物。

只读复查：`python3 -B audit/logs/stage262-exit-quiet-call-progsim/checkpoint.py`。本步是局部检查点，不是全仓通过。
