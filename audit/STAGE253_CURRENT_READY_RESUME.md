# 第253步：切换后的就绪资源转移与恢复契约

## 本步解决什么

第252步已有原物理 switch 的条件 ProgSim 桥，但独立闭合的目标任务已结束且中断关闭。本步先消除**资源交接层**对这两个条件的依赖，不把资源可交接误写为任意暂停任务的执行已经验证。

生产模块 `certiucos/v293/proofs/V293CurrentReadyResume.v` 提供五个根定理：

1. `V293_current_positive_isr`：旧 storage Inv 与新 current Inv 的正索引 ISR 资源相同。
2. `V293_current_ieoff_equal`：两者的中断关闭不变量相同。index 0 的 current guard 没有被删除；它不属于该关闭分支。
3. `V293_current_off_INV`：仅对 `ie=false` 的旧当前任务，把旧 INV 转为新 INV；没有声称中断开启时也可直接转换。
4. `V293_current_ready_transfer`：在当前任务已真实交给最高就绪目标、两个任务投影及 `good_is_S` 成立后，复用原 `swi_rdy_inv'` 重分配资源。输出目标任务的新 INV/RDYINV；物理与抽象 merge 均保持，不新增共享所有权。
5. `V293_current_resume_saved`：保持目标私有 frame 分离，并将上述资源交给**显式假设的** saved TaskSim 恢复契约。通过原 `rdyinv_isremp` 消去 RdyChange 的 ISR 清理差异。

恢复定理中的 saved contract 仍是全称前提，**不是已经独立证明的任意暂停任务 TaskSim**。没有把一个假设套进结论就记为已闭合，也没有把泛型 P 当作 InitTaskSt 的证明。

## 实际见证与对照

`audit/probes/V293CurrentReadyResumeProbe.v` 从第251步真实 current-priority 复制后的同一 typed 堆继续使用原物理 `lpstep`、原 scheduler 和资源切换定理。复制与 switch 点均保留 `CGpending`。返回物理／抽象总量、私有 frame、INV 及 RDYINV。

- `CRactual_transfer` 允许任意目标代码与目标 ie/si/cs，仅要求 si 合法。
- `CRenabled_nonterminal_transfer` 实例化目标为未结束的两条 skip 序列，`ie=true`、`si=[0]`、`cs=[false]`；`INUM=2`，栈合法。
- `CRnonterminal_progress` 独立证明该代码未结束且能迈出原 cstep。**这不是 TaskSim 的独立证明**。
- 同一复制后堆仍保留旧 current 被 GHinv 拒绝的负对照。current handoff 后最高就绪条件用于建立新 SWINVt，未放宽 guard。
- 资源转移没有要求目标终止或 ie=false；旧当前任务的 ie=false 前提仍保留。二者不能混淆。
- typed probe 保留的 `JHprivate` 是**旧当前任务的 frame**，不是已建立的目标任务 LINV。生产恢复定理对目标私有 frame 的分离性作条件化证明；本步尚无目标私有 LINV 与 saved TaskSim 同时闭合的实际见证。

同一点的 `CGpending` 一致不等于已经连接完整的全局复制前缀、抽象切换及返回执行；本步不是完整复制至返回链。也没有以“早期被拒绝”推断所有下游恢复机制均有效。

## 范围和下一项义务

不是任意 client，不是全局 ProgSim，不是 `WFInt`，不是 `GOOD_OS`；K1–K4 未闭合，uCOS3 未开始。下一项实质义务是从真实保存的任务不变量／全局模拟中建立 saved TaskSim 契约，并将复制、switch、高层当前任务更新及恢复接在同一条执行链上。不能仅增加一个同形条件定理充数。

C/config/AST/framework、旧 Inv/LI/BDspec、旧证明、测试和冻结证据不改。覆盖仍为 `94 / 1 / 1 / 1 / 1 / 0`，不因局部新引理而增长整核覆盖。未提交／推送。

## 验证与证据入口

证据目录：`audit/logs/stage253-current-ready-resume/`。协议在实现前冻结；保留每次真实失败编译及源码快照。稳定编译、逐根 Print Assumptions、递归 coqchk、build、project-audit、全量测试及旧失败差异分别落盘；以最终 `verification.json` 的实测结果为准，不把结构测试当作数学证明。

旧 make audit 的 stale function identity 和旧 framework 空白问题继续保留，未放松 gate 或改写旧报告。收尾仅删除本步一次性信任驱动和已恢复的缓存备份，保留源码、失败证据及可复用 Coq 依赖。
