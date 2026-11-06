# 第269步：实际调度切换后，共享资源重新封装

## 这一步解决什么

第268步覆盖了某个旧任务实际切出、显式切回和释放返回，但没有把调用路径中的共享全局变量统一收回候选不变式。共享变量不能一直被当作切出任务的私有资源，否则无法向统一的中断与调度证明继续连接。

本步复用现有 `V293_ready_current_inv`，不改 C、AST、框架、旧不变式或旧证明。先走实际源码级 boundary 调用、局部分配与初始化、running/nesting/lock 守卫、真实 OS_SchedNew、优先级比较、计数、复制与 switch，再在 **switch 完成后** 重新封装资源。没有要求复制与切换之间的暂态也满足较强条件，旧暂态反例仍保留。

## 生产接口

`certiucos/v293/proofs/V293OSIntExitSharedReclose.v` 的唯一上层接口是 `V293_exit_boundary_shared_reclose`。

- 输入：旧 Ready/TCB 共享候选、七个外置全局变量的独占资源、任意 typed storage 列表 `rest`，以及满足 `GoodInvAsrt R` 的 frame。
- 路径：直接调用已证 `V293_OSIntExit_boundary_switch`，不以执行关系或模拟关系作为前提。
- 输出：实际有限全局执行；目标指针和 high/nesting/lock/cache/running/counter 六个存储单元，以及 `rest`，统一收进现有 current 候选不变式。
- 新分配的 saved 区与保留 frame `R` 仍单独分离；没有把它们冒充共享变量或证明已经释放。
- 既有目标任务的 code/env/aux 绑定、计数更新、保存区可写性和缓存一致性结论同时保留。

这里的保留 frame 不等于已经证明为任务私有的 LINV。实例中的 `SRprivate` 虽沿用此名称，但含有 `RCframe` 的只读查找表与 canary；本步只把列出的可写单元收进共享候选，没有声称所有全局资源都已归位。既有 IRQ builder 的布局还包含可写查找表存储，本步不能直接与其作不变式身份替换。

这是从较弱入口到切换后较强共享候选的资源连接，不是同一个完整全局 Inv 的所有路径保持定理，也没有改写函数覆盖证书。

## 独立实例与单因素对照

`audit/probes/V293ExitSharedRecloseProbe.v` 直接实例化新接口，复用旧 BX 程序、任务表、物理堆及中断续体；不是新造一个只有 skip 的程序，也不假设 ProgSim 或执行结论。

实例将原 frame 中可写 byte 单元 block 99 移入一个**非空** `rest`；block 100 仍在保留 frame，且最终值为 0。saved 分配仍独立，所有四字节保持可写。实例对两种入口 IE 及任意既有临界栈尾成立。

冻结协议先于实现，见 `audit/logs/stage269-exit-shared-reclose/protocol.json`。`SRcopy_ablation` 在同一入口物理堆、抽象任务表、code/env/aux、计数初值和栈尾上，只改变 `BXcmd` 是否包含优先级复制：

| 实际执行 | 目标指针 | current cache | current 候选重封装 | 缓存与目标任务一致 |
| --- | --- | --- | --- | --- |
| 保留复制，再 switch | Ready | 4 | 成立 | 成立 |
| 省略复制，仍 switch | Ready | 6 | 成立 | 不成立 |

**重封装通过不等于缓存正确。** 现有 guard 允许“缓存匹配当前任务，或者当前任务已经最高 ready”两个分支，省略复制的路径仍可走后一个分支。因此接口保留独立结论 `V293_cache_current ... <-> sync=true`，不以候选不变式掩盖这一差别。两次执行各自选择 fresh saved 块，不声称分配地址相同或完整终态堆相同。

## 验证与证据

本步日志在 `audit/logs/stage269-exit-shared-reclose/`。稳定重复编译、根定理假设与递归 coqchk、完整 unittest、构建、审计、旧证据差分和清理结果以其中的 `verification.json` 为准；不能把历史 PASS 当成本步实测。

失败的编译日志及每次输入快照保留；旧测试、旧失败和冻结 manifest 不重写。README/状态只前插，工程只新增一行生产文件登记。

## 尚未完成什么

- 这是 ADR-0010 接受的**显式源码级切换边界**，不是原外部 CPU-port 声明或汇编实现的细化证明。
- 独立实例当前任务仍抽象 waiting，初始 high=88，而固定最低优先级为12；typed 入口不等于完整 Inv 或初始化可达状态。
- 端点停在 switch 后，旧任务仍挂起；未将本步重封装与第268步切回返回拼成同一个完整共享 Inv 的闭环。
- 未证明任意中断交错、任意 client、所有 OSIntExit 分支、WFInt/WFIFun 或完整 GOOD_OS。
- K1–K4 的同程序整核回归未闭合；uCOS3 尚未开始；未提交或推送。

下一步应连接切换后共享候选、任务私有 pending/saved 资源和既有返回模拟接口，明确任务间共享/私有边界；仍须分别处理缓存一致性与复制暂态，不得仅靠重封装通过宣布完成。
