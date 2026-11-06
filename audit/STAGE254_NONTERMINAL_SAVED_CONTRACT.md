# 第254步：独立建立未结束 client 的恢复契约

## 这次补上什么

第253步完成了切换后的资源分配，但暂停任务的 `TaskSim` 仍是显式前提。本步不是把前提换个名字：对原语言中的两条 skip 序列及其两个后继，独立构造原 `TaskSim`，再将真实切换产生的就绪资源交给这个已证明的契约。

生产模块 `certiucos/v293/proofs/V293ClientSkipTaskSim.v` 的稳定应用入口为 `V293_current_skip_resume`。它不再接收 Saved／TaskSim 假设，但限定为该有限纯 client 及初始任务现场 `ie=true, si=nil, cs=nil`。目标私有资源仍必须满足真实 `LINV li t init_lg`，并与共享资源分离；不是用空私有资源假设覆盖所有应用。

### 证明如何连接

1. 明确原代码的三个控制状态：序列、第一条 skip 后续体、最终 skip。穷尽原 `cstep` 后继，证明内存不变、后继闭包以及任意程序环境中的同一步匹配。
2. 在原 `ltstep` 与 `htstep` 之间建立匹配；同时排除两层输出事件与高层 API 步。反向匹配用于异常义务，不把“某一条执行能走”当作全部执行不会出错。
3. 以 guarded cofix 构造原 `task_sim`，完整保留七项义务。终止后置条件是实际 `InitTaskSt li t`，不是任意放宽为 True 的后置条件；switch、stkinit、free 分支由原语法排除。
4. 用原 `crt_init`，从任意合法目标私有 LINV、分离性及原 RDYINV 建立 InitTaskSt；再得 CurLINV 与 TaskSim。生产 `V293_skip_client_saved` 因而无需预先假设 saved TaskSim。
5. 复用第253步新 GHinv 的资源转移，将这个已证明的 saved contract 接到 `V293_current_skip_resume`，保留物理／抽象 merge 和目标私有 frame 分离性。

异常分支没有宣称任意外部 client 环境都能前进：若原低层因不匹配的环境而停住，证明以反向匹配建立原高层异常。此分支也是原模拟定义的一部分，不能删去。

## 实际见证与单因素对照

`audit/probes/V293ClientSkipTaskSimProbe.v` 沿用真实 typed 堆、current-priority 复制和原物理 `lpstep`。复制与 switch 点均保留 `CGpending`。

- `CSactual_resume` 调用上述稳定生产接口；同时返回物理／抽象资源总量、新 GHinv 的 INV/RDYINV、目标私有 LINV、InitTaskSt、CurLINV 和 TaskSim。目标代码尚未结束，中断开启。
- 此见证中的目标私有 memory／abstract frame 为 emp／emp，使用原 `V293_shared_li`；生产接口本身允许任意满足 LINV 的私有资源。
- `JHprivate` 保留的是**旧当前任务**的资源，变量命名为 `OldPrivateM`；它不是目标的私有 LINV，不以二者互相替代。
- 同一复制后堆仍无法关闭旧当前任务的 GHinv，负对照未删除、guard 未放宽。原物理 switch 后通过最高就绪分支建立新资源。
- `CSinit_requires_clear_stacks` 从原 InitTaskSt 推出 si 与 cs 都为空。两个独立对照分别仅将 si 改为 `[0]`、或仅将 cs 改为 `[false]`，其余保持；两者均不可能满足 InitTaskSt。
- 上述负对照仅否定“将暂停现场视为初始现场”的做法，**不否定这些任务可以用其他恢复契约正确恢复**。第253步的非空栈资源见证仍保留。

## 审查和边界

- 不是任意 client、API 调用、循环或内存读写程序的 TaskSim。只证明原有限 skip client。
- 不是任意中断现场的恢复；目标初始形状限制为 true/nil/nil。推广时需要对应的恢复契约，不能直接套用 InitTaskSt。
- 不是完整全局复制前缀到返回链；同一点 CGpending 一致不等于全局前缀、抽象切换和续体均已纵向闭合。
- 不是 `WFInt`，不是 `GOOD_OS`。Exit/Sched 环境迁移、初始化可达性和整核连接仍待完成；K1–K4 未闭合，uCOS3 未开始。
- C/config/AST/framework、旧 Inv/LI/BDspec、旧测试和冻结证据不改；不以删除旧失败制造通过。未提交／推送。

## 验证与阅读顺序

本步日志位于 `audit/logs/stage254-nonterminal-saved-contract/`：代码前冻结的 protocol、每次实际编译及源码快照、逐根 Print Assumptions、递归 coqchk、build、审计、完整测试和清理记录均分别保留。最终结果以 `verification.json` 为准；结构测试不能替代数学检查。

初学者可按“原 skip 状态 → 后继匹配 → TaskSim 七项义务 → crt_init → 实际资源交接”的顺序阅读。下一项实质义务是将已闭合的有限 client 契约接入原全局 ProgSim 的真实切换后续执行，并明确旧任务续体与目标任务各自的模拟责任；不能把这一步有限示例称为整核完成。

## 本步实测结果

| 检查 | 结果 |
| --- | --- |
| 生产 13 根 + probe 5 根 | 实际编译、逐根假设检查与递归 coqchk 均通过 |
| Coq 8.18.0 构建 | 通过 |
| project-audit | 通过 |
| 新增结构测试 | 5/5 通过 |
| 完整测试 | 2434 项，427 失败、1 错误；失败／错误 ID 及顺序与第253步相同，新增 5 项均通过 |
| make audit | 失败：既有函数证据身份过期，未重新冻结或改写旧证据 |
| git diff --check | 仍有旧 framework/logic/inferules.v 的 6 行空白失败，未修改旧文件 |

允许的既有经典假设仅为 classic 和 functional_extensionality_dep，无新增公理。全仓未通过不影响上述局部证明的实际检查结果，但局部结果也不能消除旧失败或代替最终 GOOD_OS。
