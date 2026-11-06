# 第213步：不同优先级退出接入真实函数 builders

## 相比上一步新增什么

第212步闭合的是已打开资源、已分配 saved 单元的完整归一化本体。本步稳定接口为 `V293OSIntExitChangedInternal.V293_OSIntExit_changed_builder_contract`：从实际 `BuildPreI` 取得入口，执行同一个完整归一化本体，将原线程恢复后的资源打包回实际 `BuildRetI`。主定理只有一个 `InfRules` 结论，没有假设整个本体、中段 Hoare 或表达式求值 oracle。

```text
BuildPreI 的 saved 单局部单元 + 外部函数前置 + 单局部 domain
→ 从 domain 推出不遮蔽；内部补足 high 的环境绑定
→ 第212步完整本体：初始化/临界区/dispatch/switch/恢复/退出/return
→ 同一 storage Inv + 私有 saved + 无共享旧值快照的外部后置
→ BuildRetI
```

源码、配置、AST、框架、tactics、旧证明、旧测试及冻结证据不变。沿用 ADR0010 接受的切换抽象，不开展编译器、ABI、硬件工作。

## 为什么函数断言不能携带局部环境

`fpre`、`fpost` 是带 `GoodFunAsrt` 证明的真实函数断言。它们不含局部变量绑定、局部 domain 或 `A_notin_lenv`；这些仅由 builders 和桥接证明内部引入。外部前置中的纯条件给出就绪位图/任务表/指针表关系、当前任务存在、优先级界及 nesting≤1；真实完整字节提供 running=1、lock=0。

八个名称不等条件用于从 saved 单局部 domain 导出 table/high/target/current/counter/nesting/lock/running 不遮蔽。它们不是函数前置中偷偷预设的局部环境事实。内部 `high_binding` 从已有 globals/prefix 与空资源推出，不向调用者索要第二份物理单元。

外部后置只保留返回 None、恢复后的同一 storage Inv、原线程/栈、全局环境和受约束的额外 frame；不保留切换前 tasks/events/time/ready/current/counter 的值。共享控制字节仍归还同一 Inv。返回描述原线程将来恢复，不证明 switch 必然返回。

## 非空性与事前单因素对照

| 证据 | 观察 | 边界 |
| --- | --- | --- |
| `CBresources_owned` / `CBpre_owned` | 从独立编码字节、全局/单局部环境及任务表构造实际 builder 前置 | 不从主 Hoare 结论反推前置；不是初始化可达性 |
| `CBentry_nonempty` | nesting=1，当前等待任务 priority=4，最高就绪目标 priority=12，确实是不同任务 | 通用前置的缓存—当前任务关系仍未建立 |
| `CBzero_max_entry` | nesting=0、UINT32 最大 counter 的入口也非空 | 沿用现有模加语义，不声称无溢出 |
| `CBactual_contract` | 实例化完整 builder Hoare，而非只检查定义可计算 | callee 的增强 Spec lookup 仍是前提 |
| `CBarity_control` / `CBreturn_arity_observation` | 非空实参由实际 BuildPreI 拒绝；BuildRetI 不检查形参数量 | 不声称两者均拒绝 |
| `CBshadow_control` | 只将 saved 标识符117改为 running 标识符114，局部绑定随声明更名；两侧实际 builder 前置非空，内存字节完全相同 | 全局 running 仍在 block13/Tint8，但局部 running 成为 block16/Tint32，所需不遮蔽绑定不能成立 |

遮蔽对照通过框架 `GoodFunAsrt` 的局部环境独立性迁移同一物理资源，不改变外部断言、字节、任务表、ISR/IE 或操作码。它仅测量 builder/名称分离边界，不声称完整函数变体执行，也不把早期拒绝当作 downstream switch 的有效性证据。协议在编码前冻结于 `protocol.json` / `protocol-identity.json`。

## 限制与核验

当前仍要求原 IE=false、ISR 全清，参数化 si/ci；这不是任意 ISR/IE 的完整退出规格。这里连接的是实际 builders 的资源断言，**不是局部分配/free 的操作执行轨迹**。不同优先级路径尚未与既有不调度/同优先级路径合成同一生产规格、统一完整函数环境；生产 Inv 资源来源、生产 ISR/LocalInv、WFInt、初始化、GOOD_OS 与同程序 K1–K4 仍开放。uCOS3 未启动，阶段一未完成。

实际结果以 `audit/logs/stage213-interrupt-exit-changed-builders/verification.json` 为准。逐次失败编译快照和诊断全部保留；递归 coqchk、逐根假设、两次构建、精确配置后源码重建、5项新结构回归与完整旧回归逐项记录。结构回归不冒充语义证明或语义 TDD。旧423失败/1错误的 ID/顺序必须原样保留；旧 make audit 证据身份失配、inferules.v 第581–586行空白问题不改门槛。

README/状态只前插，工程清单只追加。清理前逐项确认本轮一次性 Trust 驱动/产物及缓存备份，恢复原缓存字节后删除备份；保留源码、诊断和可复用 Coq 产物。六门仍为 `94 / 1 / 1 / 1 / 1 / 0`，总目标 active，本步未提交/推送。

下一步是把 changed 路径与 quiet/same 的契约统一，并消除其 callee lookup 的环境义务；随后推进生产 Inv/ISR 与初始化，而不是把当前受限函数契约记作整核完成。
