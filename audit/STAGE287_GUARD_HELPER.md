# 第287步：原临界代码接通 helper 与需要切换的后缀

## 这一步解决什么

第286步只有临界原语和 nesting/lock 前缀，接口要求外部提供 dispatch TaskSim continuation；第285步从 helper 调用开始证明后缀。本步将两者在**相同资源布局和真实语句 continuation** 下连接，消去这个前提。

唯一公开生产接口是 `V293_exit_guard_helper_TaskSim`，位于 `certiucos/v293/proofs/V293ExitGuardHelperTaskSim.v`。它只以资源、绑定、任务关系和调度器身份为输入，不要求 TaskSim、执行、load/store 或求值结果作为前提。它证明从原 `encrit; (nesting_dispatch; excrit)` 到已有抽象调度/返回接口的模拟。

## 怎么理解证明链

1. 初始拥有 nesting=n（n=0 或1）、lock=0 两个可写字节，以及完整 ready/helper 资源。
2. 真实 `encrit` 将辅助栈从 ci 改成 false::ci。不能把整个 SWINVt 当成 Good；用已有 `V293_ready_critical_stack` 只搬动临界栈，其余状态不变。
3. 原递减代码将 nesting 保持为0或从1写成0。双 guard 随后进入真实 dispatch。
4. 两层原 `sseq` 产生与第285步相同的 continuation，并没有更改 AST 的结合次序。
5. 两个 guard 的完整所有权转成 existential-value storage，并装入 helper frame。没有删掉物理字节或把它们丢到外部 frame。
6. 复用真实 OS_SchedNew 调用、目标更新、比较、计数、handoff/switch 和 pending 返回证明，最终 RDYINV 的 storage 清单含这两个 guard。

storage 只保证类型匹配的可写存储，不在任意兼容资源归还后保证 guard 值仍为0。本步没有证明不同 storage 列表排列下的 invariant 等价。

## 非空实例与消融

`audit/probes/V293ExitGuardHelperProbe.v` 构造完整 unmap 表、ready/任务资源、输出单元以及额外150/151块 guard。`GHbase` 给出实际资源见证；`GHinstantiated_critical_cut` 固定实际 scheduler spec，覆盖 n=0/1，不留 getsched 等式前提，后置条件是真实 RDYINV，不是 Post=True。

`GHoriginal_critical_shape` 以定义等式核对该 critical block 确为原 boundary body 中的子表达式；它不证明外层入口可达性。新堆不是旧完整调用 trace 的同一个堆，不能替换那份旧证据的身份。

前瞻协议 `audit/logs/stage287-guard-helper/protocol.json` 在实现前固定。单因素权限对照保持地址、初值1、读值1和写值0不变，仅取消 guard 完整写权限：两种权限均可读取，只有完整权限能递减写入。**这只是局部 store 权限对照，不是完整调用执行消融**；不据此推断所有后续机制有效。

## 检查与未完成项

两份新文件各连续编译两次；对全部新证明根逐项打印 assumptions，并递归 coqchk。原始成功和失败编译快照均保留。准确次数、退出码和全套回归身份比较以 `audit/logs/stage287-guard-helper/verification.json` 为准。可只读复验：

```bash
python3 -B audit/logs/stage287-guard-helper/checkpoint.py
```

实测：4次稳定编译成功；10个证明根 assumptions 检查及递归 coqchk 通过（549.90秒）；make build、项目审计和5项新回归通过。全套2601项仍有434失败、1错误，旧失败/错误身份及顺序与第286步完全相同。make audit 仍因 stale function evidence input identity 失败；git diff --check 仍报告旧 framework/logic/inferules.v:581–586 行尾空白。没有修改这些旧证据或失败门槛。

清理前逐项记录后，仅移除本步8项一次性检查模块/缓存备份；保留证明产物与日志，恢复既有缓存，306份既有 Python bytecode 未变。

这仍不是原完整活跃调用入口 TaskSim：外层 saved 写入、running guard、调用分配尚待连接；只覆盖 n<=1、lock=0 且当前任务并非最高 ready 的需要切换分支。等优先级分支、一般 nesting 分支、WFIFun/WFInt 未闭合。si=nil、ISR 全清、空 LINV、强 current guard 缺口及 ADR-0010 边界不变。

GOOD_OS 与同程序 K1–K4 未完成，uCOS3 未开始。旧全仓库失败不隐藏、不删改。本步没有提交或推送。下一步向真实外层入口推进，而不是继续把条件性局部证明记成整函数完成。
