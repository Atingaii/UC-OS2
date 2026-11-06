# 第272步：在真实返回状态上建立原 TaskSim

## 这一步补什么缺口

第271步已把实际返回堆分成原 `INV ** RDYINV ** frame`，但尚无原任务模拟。旧的 `V293_skip_client_TaskSim` 接口使用 `InitTaskSt`：它要求 IE=true、中断栈和临界保存栈为空。这不能直接用于实际恢复后的 IE=false 或仍有临界保存栈的任务。不能为套用旧定理而重置 flags、栈，或把原初态断言弱化。

新增生产文件 `certiucos/v293/proofs/V293ReturnClientTaskSim.v`，唯一上层接口 `V293_return_client_TaskSim`。它不要求 InitTaskSt、执行成功或 TaskSim 前提。保留既有 core、Inv、RDYINV 和有限 skip client 家族，不增加新的任务／不变式定义：

```text
core ** (CurTid t ** (LINV li t lg ** R))
  ==> 原完整堆/抽象状态 = 共享部分 + 目标任务部分 + 外部 R
      共享部分满足 INV；任务部分满足 RDYINV ** LINV
      同一个任务部分具有原框架 TaskSim
      TaskSim 后置仍是精确的 RDYINV ** LINV
```

公开条件仍是 ISR 位全部 false；只有 IE=false 时要求 top<=INUM。任意真实 LINV 与任意 R 由调用方提供，不能从空内存制造非空私有资源。

## 原七项义务如何处理

`V293_return_client_coinduction` 直接使用原 `task_sim` 构造器，不假设任何模拟结论：

| 原义务 | 本步处理 |
| --- | --- |
| 普通低层一步 | 复用既有 client 逐步匹配引理，高层真实步匹配；物理状态不变，原 join、INV、局部断言及精确 P 保留，再递归 |
| 带事件的一步 | 原有限 client 家族不产生事件，排除前提 |
| switch | 该家族当前语句不是 switch，排除前提 |
| 终止 | 同一终止代码、高层零步、原资源及精确 P；不吞掉资源 |
| abort | 复用原 client abort 匹配引理，不假装不可能发生 abort |
| stkinit | 当前语句不匹配，排除前提 |
| stkfree | 当前语句不匹配，排除前提 |

内部为满足原 CurLINV 形状会使用其已有 Atrue；**公开 TaskSim 的 P 不退化为 Atrue**，仍完整保留 RDYINV 与 LINV。先从271的同一分离取得共享与任务部分，再显式拆出 R；四个原 join 同时覆盖整个输入物理堆与抽象资源，不复制共享 core。

## 同一实际完整调用和栈顶消融

独立文件 `audit/probes/V293ReturnClientTaskSimProbe.v`：

- `RTfull_call` 只有原两个 fresh 前提，复用原 FWtasks/FWos 完整调用；在目标 pending 真正返回、释放 saved98 后，为实际 caller `SKIP/(kenil,kstop)` 建立 TaskSim，并保留旧 saved 值、canary90=99 和已释放四字节的事实。
- `RTnonvacuous` 给出可满足入口及真实完整执行；无执行或模拟前提。
- `RTsaved_top_actual_ablation` 复用270/271同达到堆只删目标保存栈顶的实际双执行。两支均得到 TaskSim 与精确资源分离；没有再算一组新增执行。

| 单因素对照 | 最终 IE / 临界保存栈 | 最终完整物理堆 | 返回后的 TaskSim |
| --- | --- | --- | --- |
| 原 false :: true :: vci | false / true :: vci | 同一 Mf | 成立 |
| 仅删首个 false | true / vci | 同一 Mf | 成立 |

两支都真正走过 switch、excrit、sret、free、caller；不是用早拒绝替代下游验证。变体从共同达到快照开始；不声称两个不同栈均由同一个原始完整入口执行产生。

`RTnot_initial` 另证 IE=false 或临界栈非空与原 InitTaskSt 不兼容。这是断言边界检查，不是另一项实际执行消融。`RTnonterminal_resume` 单独验证原非终止 skip 家族有真实 cstep、非 IsEnd 且可得 TaskSim；**不是把完整调用的实际终止 caller 改成非终止程序**。

## 所有权与适用边界

实例沿用原 `V293_shared_li` 空局部候选。旧 saved 与整个 STframe（含 RCframe 的只读 lookup92）仍是外部 R，**不是目标任务私有 LINV**。没有把旧任务 canary 或 saved 转给目标；生产接口虽允许任意真实 LINV，当前具体实例不证明非空栈布局／私有 saved 安装。

这是返回之后、既有有限 client 家族的 TaskSim，**不是整核** TaskSim 或任意客户程序模拟；也不是 pending 返回之前那条 excrit/sret/stkfree 路径的 TaskSim。实际完整调用的 caller 已终止，这项实际端点实例不能替代生产 cofix 的非终止支持，反之亦然。高层规格 A 任意，是因为此 client 不调用内核 API，不是已证明任意 API 规格。

原任务仍 blocked，没有唤醒消息，不能立即切回；不借环境切回伪造完整共享循环。目标 pending 已存在、共同 si、typed high=88 非初始化可达、原 IRQ builder 布局差异和 ADR-0010 源码级 port 边界均不变。没有新增 cache 一致性、初始化、全路径安装、WFInt/WFIFun、任意交错保持或完整 OSIntExit 规格。

## 核查与后续

前瞻协议实现前冻结，稳定编译各两次；4个生产根与6个独立根执行 Print Assumptions 和递归 coqchk。新增结构测试不替代 Coq 内核证明。完整测试保留旧失败及原始顺序，旧代码、测试、冻结 manifest 不改。实际结果记录在 `audit/logs/stage272-return-client-tasksim/verification.json`，不能以局部通过宣称全仓通过。

下一步应把**同一个 Inv/LINV 与端点 P**接到目标 pending 返回之前的原 TaskSim 义务，特别是临界退出、返回和保存区释放；不能仅再包装已经终止的 caller。随后仍需真实唤醒/ready 更新、旧任务恢复、任意交错、函数/中断安装及初始化连接。

**源码级 GOOD_OS、同程序 K1–K4 尚未完成，uCOS3 未开始，未提交／推送；总目标 active。**
