# 第243步：bound LocalInv 的 changed/same 连续中断返回

## 从上一轮接上了哪里

第242步完成 quiet 路径。本步增加两个稳定入口：

- `V293_interrupt_bound_changed_continuous`
- `V293_interrupt_bound_same_continuous`

它们均连续证明原 `EOI → scall Enter → scall dynamic Exit → exint` wrapper，采用同一个第241步 BDspec、bound LI 与原 ready/TCB/storage Inv。不是另写运行时程序，也没有修改固定 C、配置或 AST。生产文件为 `certiucos/v293/proofs/V293InterruptBoundDispatchContinuous.v`；独立检查文件为 `audit/probes/V293InterruptBoundDispatchContinuousProbe.v`。生产代码不依赖 audit。

## 为什么不能直接复用旧 wrapper 定理

旧定理使用 shared LI，新的局部不变量还保存 running/nesting/lock 的 GE 地址绑定。不同 LI 的 InfRules 不能直接互换。因此本步只复用旧的断言资源蕴含，重新连接 bound Enter/dynamic Exit 的真实调用与 EOI/iret 规则。两个稳定连续定理均没有中间 Hoare 结论前提，也没有外加 globals 前提。

| 环节 | changed | same |
| --- | --- | --- |
| Enter | 原强 snapshot 资源拆开，将原 globals 与 shared p_local 关闭成 bound p_local，实际调用后再打开 | 原 payload 保持，完整只读资源留在 frame，同样重建绑定调用 Enter |
| Exit 前 | 原 changed 编码在动态合同中定义相等，无需改变原状态 | 原完整只读份额拆分为动态合同所需部分与 reserve，再关闭 bound p_local |
| Exit 后 | 使用实际动态后置归还的 bound p_local，保留 SWINV 与中断栈 | 先打开 bound p_local 保留 GE frame；原 resources_close 重组只读半份并关闭 storage，再重新关闭绑定 |
| iret | 关闭同一原 Inv，使用实际 BuildintRet | 关闭同一原 Inv，使用实际 BuildintRet |

复制的仅是零资源足迹的 GE 观察，不复制堆单元；same 没有将未归还的只读权限当成完整写权限。共同三函数环境的 GoodI/WFFunEnv/WFIFun 原样复用。

## 独立检查与消融

`BCbuilders`/`BSbuilders` 确认字面断言是实际 BuildintPre/BuildintRet 的结果。`BCtyped_entry_nonempty`/`BStyped_entry_nonempty` 使用原具体 typed 字节堆证明强入口非空；两个 `actual_wrapper` 实际实例化新稳定定理，不接收中间证明作为假设。

返回字面检查保留 spec_done、ISR 位、ISR 栈、空临界区栈、IRINV、空局部变量域与 bound p_local。Waiting 返回侧另复用独立 typed 物理状态见证；**本步没有另证 Ready 返回侧的独立 typed 非空，也没有证明强 changed/same 入口与新实际 BuildintPre 在同一状态成立**，不能从前后置非空分别存在推出执行可达。

1. `BCreturn_forget`/`BSreturn_forget` 各自只删除返回中的地址绑定要求，其余资源与元数据不变。这是单因素断言弱化，**不是两次完整执行**，也不是所有下游机制必要性的证据。
2. 生产文件导入消融：entry08 → entry09 仅删除十个未使用的直接 Require，所有定义、陈述及证明正文保持不变，两次编译均成功。不是运行时性能实验。
3. `BCabstract_entry_differs` 明确证明 changed 所需抽象入口 `sched;;spec_done None` 与 same/quiet 的 `spec_done None` 不同。不能把共同函数环境误写成统一 ISR 抽象规格。

## 完成边界

条件强 snapshot 仍要求 prior all-clear、有效向量、nesting=0→1 以及各自 dispatch 路径的 ready/priority/TCB 一致性。same 还要求 table 的指针类型证据。旧 quiet 的饱和与其他 ISR 位限制不因本步消失。

**不是所有 BuildintPre**，**不是 `WFInt`**，不是初始化可达，也**不是 `GOOD_OS`**。候选 Enter 与旧 local-storage Enter 边界差异仍存在；生产 ISR 抽象规格、任意入口控制条件、非全清 ISR 返回、初始化、其他 API 和同程序 K1–K4 仍开放。uCOS3 未开始，未提交／推送。

## 实测记录与下一步

本步16个生产根、16个独立检查根逐根检查假设，并对两个模块递归 coqchk。允许的既有逻辑基础仅 classic 与 functional_extensionality_dep。五项新增 Python 测试只做结构、来源和证据回归，不替代 Coq。精确实测以 `audit/logs/stage243-bound-dispatch-continuous/verification.json` 为准；成功和失败编译快照均保留。

旧423失败、1错误及有序 ID 必须不变；make audit 的陈旧函数证据身份失败和原六处 whitespace 失败不通过改 gate 消除。前一检查点的全文件集合检查不能在新增 .v 后原样重跑，本步只对前一冻结 manifest 的非滚动文件验证哈希，不改写旧检查器或证据。

下一步优先建立强 changed/same snapshot 与实际 builder 的同状态资源连接，并解决不同路径的 ISR 抽象操作统一；然后推进非全清 ISR 与 WFInt。三条条件连续路径齐备并不等于整核闭合。
