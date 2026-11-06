# 第236步：从真实中断入口取出控制值并连接 Enter

## 本轮解决什么

上一轮的 quiet/changed/same 连续证明从条件强入口出发。要向整个中断正确性推进，必须先检查框架实际生成的 `BuildintPre` 是否真的包含这些条件，而不是把条件默认为成立。

本轮新增 `certiucos/v293/proofs/V293InterruptEntryControl.v`。稳定接口是 `V293_interrupt_entry_control`：

1. 输入是实际 `BuildintPre` 生成的前置，加上显式的 `running/nesting/lock` 全局地址绑定 frame。
2. 打开同一个 ready/TCB/storage 不变量，从三个 `Tint8` 存储单元提取存在的 `run/nest/locked` 及其 `<256` 界限。不是事先规定初值为 `1/0/0`。
3. 执行原 `eoi` 规则，再调用原共同规格中的精确 `OSIntEnter` 合同。
4. 后置保留三个旧值见证，并把实际 nesting 写成 `V293_interrupt_nest_after run oldnest`；其余 ready/TCB/storage、局部资源和地址绑定仍保留在快照中。

没有添加任意中间状态蕴含或执行正确性假设，没有改旧 C、配置、AST、框架、tactics 或旧证明。使用 `V293_quiet_irq_snapshot` 只复用其资源布局；这个断言本身不含 quiet 判定，名字不意味着本轮只覆盖 quiet 控制值。

## 给初学者的解释

可以把入口看成一个封好的资源包：之前的分支证明要求包里有某些具体值；本轮先实际拆包、读出值，再证明 Enter 如何更新它。这里的“读出”是证明中打开存储断言，不是添加新的 C 读取语句。

| 概念 | 本轮实际含义 |
| --- | --- |
| `BuildintPre` | 框架根据中断号、ISR 状态和不变量生成的入口断言 |
| `globals` | 变量名指向哪块内存的约束；自身不占堆内存，但不是无条件事实 |
| `EX run/nest/locked` | 当前内存里确实存在的字节值，不是猜测值 |
| `nest_after` | 运行时且计数未饱和才加一，否则保持原值 |
| `InfRules` | 框架中的语句 Hoare 推导；这里覆盖 EOI/Enter 前缀 |
| 非空见证 | 确实存在一个具体 typed 字节堆满足实际入口，排除只因前置矛盾而通过 |

具体探针使用现有 typed 内存，`run=1/nest=1/lock=0`。`ECsnapshot_to_builder` 把原具体快照重新封装为真正的 builder 前置并保留绑定，`ECbuilder` 验证 builder 等式，`ECentry_nonempty` 给出堆与抽象资源的分割见证；不是只证明更强快照非空。原 `QCspec/RDprogram/RDinv` 的 `GoodI/WFFunEnv/WFIFun` 原样复用。

## 边界对照

保持同一个更新函数和其余参数不变：

| 对照 | 变化因素 | 结果 |
| --- | --- | --- |
| `run=1, nest=254` | 基准 | 更新到255 |
| `run=1, nest=255` | 只改变初始 nesting | 饱和，仍为255，不是256 |
| `run=0, nest=254` | 相对基准只改变 running | 仍为254 |
| `run=1, nest=1` | 非零初值样例 | 更新到2 |

这些是 Coq 检查的更新关系实例，不是两次完整执行的消融实验。实际前缀主定理对所有满足入口的字节值量化，不预设 nesting 未饱和，也不预设 quiet 条件。它仍明确要求入口 ISR 原位全清、合法中断号及实际 Enter 规格查表成立。

## 不能由此宣称什么

- **globals 绑定是显式附加 frame**，现有 `BuildintPre` 本身没有给出这些绑定。因此不是无附加条件的全部入口闭合。
- 只接通 EOI/Enter 前缀，不包括 Exit/iret；不是 `WFInt`。
- 当前 storage 只有 lookup 表字节的类型，没有固定表内容；也没有 current priority 与当前 TCB 对应、nesting 与 ISR 栈对应关系。本轮不把这些缺失条件冒充由 Inv 推出。
- fixture 仍使用常 Aemp LocalInv，不是生产 ISR LocalInv；不是初始化可达证明。
- 尚无生产 ISR 抽象动作或 tick 本体连接，最终 `GOOD_OS`、同程序 K1–K4 回归仍开放；uCOS3 未开始。
- 覆盖六门仍为 `94/1/1/1/1/0`。结构测试不是语义 TDD；既有423失败、1错误及 audit/whitespace 失败必须保留。

## 验证与下一步

实测记录放在 `audit/logs/stage236-interrupt-entry-control/`，包括每次编译的源快照、源码身份重建、逐根假设与递归 `coqchk`、构建和测试日志。最终数值以 `verification.json` 为准，旧证据不改写。

下一步应先在实际生产入口资源中落实地址绑定和必要的语义关系，再把真实前缀后置分流到已验证的 Exit/iret 路径；不能简单拼接三个强入口就宣布 `WFInt` 或整核完成。
