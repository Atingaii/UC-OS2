# 第240步：地址绑定不变量接入 Exit 完整切换路径与三函数候选环境

## 这一步解决什么

第238步让 Enter 使用记录 running、nesting、lock 地址的 `LocalInv`，第239步把这个不变量带入实际 dispatch。本步补齐同一 **changed-case** 的函数入口、临界区、计数递减、调用、切换恢复、退出临界区和返回，避免只证明中间片段却声称函数已经接通。

初学者可以按以下顺序阅读：

| 层次 | 本步接口 | 含义 |
| --- | --- | --- |
| 原始资源 | `V293_bound_core_frame_local` | 从原堆和名称绑定推导 `CurLINV`；running 绑定在 core 外，不能只复用旧 core 引理 |
| 完整函数体 | `V293_OSIntExit_bound_body` | 在 running=1、lock=0、nesting<=1、最高就绪任务不同的条件下检查整个 normalized Exit |
| 函数边界 | `V293_OSIntExit_bound_builder_contract` | 对任意程序、实参表、逻辑参数和 BuildPreI/BuildRetI 结果证明函数契约；非法非空实参不能通过 builder |
| 调用 | `V293_OSIntExit_bound_call` | 真正的 `scall`，保留调用者 frame 和返回的 `p_local` |
| 三函数环境 | `V293_bound_irq_WFFunEnv` / `V293_bound_irq_WFIFun` | 原 Enter、Exit、Sched 三个函数体共享同一地址绑定 LocalInv 和原 ready/TCB/storage Inv |

## 关键约束

- 不修改 C、配置、原 AST、框架、战术、旧证明或原资源不变量。
- 函数体的前置仍是原 `bodydata`，不要求调用者额外交出 globals 或中间 Hoare 结论。
- `LocalInv` 的三个全局地址观察没有可写堆所有权，但不等于逻辑上的 Aemp。只能复制这些共享名称观察，不能复制控制字节或其他可写资源。
- `excrit` 重新证明为 LocalInv 参数化引理，不把旧 shared-LI Hoare 结论直接改名当成新证明。
- 返回保存 bound `p_local`，切换后的共享值仍存在量化，不冻结切换前值。

## 可观察证据与消融边界

`audit/probes/V293OSIntExitBoundInternalProbe.v` 独立写出函数体和 builder 的字面后置，检查 typed builder 和真实调用前置非空，并验证整个程序与旧 `RDprogram` 定义相同。具体三函数环境、实际函数体、通用契约、实际调用和非法实参拒绝均由 Coq 检查。

`BIsame_exit_shared_control`、`BIsame_sched_shared_control` 固定旧 shared-LI 对照的运行时代码；`BIbody_post_forget` 只消去返回的绑定观察，得到旧字面后置。其余资源、原 Inv 和代码不变。这是规格的单因素弱化，不是两次完整执行，也不证明旧规格不成立。第238步只改错一个绑定的状态负对照保持原样；它不替代本步的函数体及环境证明。

## 不能据此宣称的结果

这是 changed-case 整函数，而不是所有 Exit 路径。quiet/same 动态规格尚未迁移；新环境使用受限 changed-case Exit 规格，旧动态三函数环境未迁移，不能把二者混为同一已完成环境。

typed 非空见证不是初始化可达；本步不是 `WFInt`，不是 `GOOD_OS`，没有闭合同程序 K1–K4，也未覆盖所有 BuildintPre 或最终 iret。uCOS3 未开始，无提交／推送。下一步要先把 quiet/same 路径纳入同一个候选 LocalInv，再连接中断返回及顶层义务。

独立逐根假设、递归 coqchk、构建和完整回归以 `audit/logs/stage240-bound-exit-body/verification.json` 为最终记录。旧423失败、1错误以及 audit/whitespace 历史失败必须保留；六门覆盖不因增加局部证明而自动升级。
