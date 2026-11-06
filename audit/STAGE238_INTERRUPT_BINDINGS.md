# 第238步：地址绑定进入 LocalInv，真实入口不再外加 globals

## 本轮实际闭合的接口

`certiucos/v293/proofs/V293InterruptBindings.v` 的稳定接口是 `V293_interrupt_bound_entry`：

- 使用原 ready/TCB/storage `Inv`，从真实 `BuildintPre` 的 **pre 本身**出发；没有 `pre ** globals`、中间 Hoare oracle、初始 running/nesting/lock 值或 ISR 全清前提。
- 三个控制字节及界限仍从原 storage 打开，不把地址绑定误当成内存值。
- 连续执行真实 `eoi` 和 `scall enter nil`，后置精确保留其他 ISR 活动位、两栈与旧 nesting 到 `nest_after` 的关系。
- 真实 `OSIntEnter` 更新和完整返回本体、函数 builders 的通用合同及单函数 `WFFunEnv/WFIFun` 均在同一个新 LocalInv 下证明；不是把中间调用的正确性当成开放前提。

新文件只复用框架已有的 `LocalInv`、原 Enter updates 定理及原 builder/storage 资源接口；不增加框架规则、运行时机制、C 补丁或 AST。

## 给初学者的解释

| 对象 | 本轮如何使用 | 不能混淆为 |
| --- | --- | --- |
| 全局地址绑定 | running/nesting/lock 分别映射到哪些 typed 地址 | 对应地址当前存的值 |
| LocalInv | `V293_irq_bound_li` 保存这三条 `Agvarenv`；不依赖线程或逻辑参数 | 新的一份物理内存所有权 |
| 原 Inv | 继续拥有 ready/TCB/storage，包括三控制字节 | 任意可加入 ISR 栈深度等式的容器 |
| BuildintPre | 自带 `p_local`，所以可直接提供地址绑定 | 任意旧 Aemp builder 都已经变强 |
| GoodI | 同一 Inv 对新 LocalInv 仍合法 | 三函数环境或整个操作系统已经完成迁移 |

`V293_irq_bound_empty` 说明新 LocalInv 的堆/抽象资源足迹为空，**不说明它的逻辑内容等于 Aemp**。它对全局环境有实际约束。`V293_irq_bound_good` 同时证明 `GoodLocalInvAsrt` 和精确足迹；`V293_irq_bound_GoodI` 复用原 GoodI，仅处理与 LocalInv 有关的释放分支，不弱化 Inv 或调度条件。

## 单因素地址对照

在 `audit/probes/V293InterruptBindingsProbe.v` 中：

1. `EBentry_nonempty` 在原 `JBmemory 1 Int.zero Int.zero` 与同一抽象任务状态、prior 位1活动、栈 `[0;1]` 上，构造新 builder 的真实内存分割。
2. `EBenvironment` 检查新 LocalInv、原 Inv 和原 Enter 本体的单函数环境；`EBsame_Enter_body` 明确它就是原三函数程序中地址301的函数。
3. `EBactual_prefix` 检查实际 EOI/Enter 连续调用，不仅检查一个更新数学函数。
4. `EBbadge` 只把全局变量112（running）的绑定从块99改为块100；`EBsingle_changed_binding` 证明其他全局绑定不变。内存、抽象状态、ISR 位图、两栈、局部环境和逻辑操作均保持相同。
5. `EBbad_weak_builder_nonempty` 证明同一组 M/O 分割在正确环境满足新 builder，在错误环境仍满足旧 Aemp builder；`EBbad_bound_builder_rejected` 证明错误环境不可能满足新 builder。

这是固定状态断言的单因素对照，**不是两次完整执行**。错误绑定的早期拒绝只证明这一边界有效，不能代替 Enter 本体证明，也不推出 Exit/scheduler 已正确迁移；后者未在本步完成。未宣称语义 TDD。

## 明确边界与下一步

新 LocalInv 是入口的候选接入，不替换或改写旧三函数环境，也不冻结为整核唯一 LocalInv。虽然入口不再外加 globals，但仍需在共同程序中接通 Exit/scheduler 的合同，并由初始化建立相同绑定；不能把新 LocalInv 的选择当成所有旧前置已覆盖。

**不是 `WFInt`，不是初始化可达，也不是 `GOOD_OS`。** 完整 Exit/iret、lookup 内容、current priority/TCB 与阶段相关 nesting 关系、生产 ISR 抽象规格、全部 API 连接及同程序 K1–K4 仍开放。uCOS3 未开始。

六门覆盖仍为 `94/1/1/1/1/0`，不按新增文件数增加覆盖。旧423失败、1错误及既有 audit/whitespace 失败保留；本轮实际构建、独立检查及测试计数见 `audit/logs/stage238-interrupt-bindings/verification.json`。未提交／推送。

## 可复核证据

证据目录：`audit/logs/stage238-interrupt-bindings/`。保留实现前的协议及身份、四个配置后函数的源码重建、每次成功/失败编译的源码快照和日志、逐根假设、递归 `coqchk`、构建与完整测试、对抗审查、旧文件哈希和清理清单。冻结后使用：

```bash
python3 -B audit/logs/stage238-interrupt-bindings/checkpoint.py recheck
```

旧证据不改写；只清理由本步生成、交付不再需要的临时信任驱动及其产物，恢复原算术缓存，保留源文件、验证日志、失败快照及可复用 Coq 产物。
