# 第114步：从开启中断的真实入口接通受限任务创建契约

## 这一步解决什么

第113步已经证明临界区内 NULL 槽的连续失败路径，但尚未从函数入口接入。本步保留原完整 `OSTaskCreateExt` AST，把真实 CPU 局部赋值、优先级检查、进入临界区、动态读取共享槽位、原返回路径和标准函数契约连接起来。

这里的“整函数契约”指证明对象是原完整函数体，不是已覆盖所有运行情形。当前合法优先级路径限制 `OSIntNesting=0`，TCB 空闲链表头限制 NULL；公开后置条件是受限返回码集合，不能当作完整的分支关系规格。总目标仍 active。

## 入口到返回

| 实际检查 | 本步连接的路径 | 边界 |
| --- | --- | --- |
| 优先级非法 | 初始化 CPU 局部后，优先级大于等于13，返回42 | 参数仍须满足类型及标准入口要求；此路径不要求共享池借还前提 |
| 合法优先级、槽位非 NULL | encrit1 从同一个 Inv 借出槽位；真实 typed load 与比较决定占用；excrit1 原样归还后返回40 | RESERVED 只持半权限也可读取，未升级为写权限；其他指针为完整权限 |
| 合法优先级、槽位 NULL | 真实预留写入、归还共享池、栈 Hook、七参数 TCB 调用、失败后借池合并预留权限、回滚 NULL、返回66 | TCB 空闲池为空；Hook 仅有外部标准规格，不含函数体证明 |

合法入口不预先选定槽位值：同一个存在资源池允许 NULL、RESERVED 和其他任务指针。`Rbefore`／`Rafter` 保留 Hook 前后的资源变化，不把跨中断资源当固定快照。公开后置给出42／40对应入口资源、66对应后续资源，不声称公开规格已经精确表达所有输入与返回的对应关系。

## 可复用接口与具体实例

- 生产模块：`certiucos/v293/proofs/V293TaskCreateEnabledOwned.v`，515行、11个证明根。
- 稳定上层定理：`V293_OSTaskCreateExt_enabled_owned_contract`。使用真实 `BuildPreI`／`BuildRetI`、九个参数、三个局部变量及精确声明域；只有一个最终 `InfRules` 结论，没有外部执行或求值 oracle 前提。
- 独立探针：`audit/probes/V293TaskCreateEnabledOwnedProbe.v`，576行、32个证明根；不在生产证明依赖链中。
- 探针使用同一 `EOInv` 和同一有限 `EOSpec`，检查完整创建函数及完整空池 `OS_TCBInit`。Hook 只有契约，不能把它算成 `WFIFun`。
- `EOEnabledEntryLiteral` 给出真正 IE=true 的十二局部字节入口：CPU 初值99，由真实函数赋值为0，而非在前置条件中偷做初始化。
- `EOCallerHasNoSharedBytes` 证明调用者在共享 head／slot／counter 地址没有字节；`EOEnabledSharedCompatible` 证明它能与共享池内存共存。同一不变量支持 NULL、半权限 RESERVED、完整权限其他指针。

以上是局部前提可满足性，不是初始化可达性或生产全局不变量。本步没有增加同一新不变量下完整 TCB 内部入口的字面实例；不能把完整 callee 的条件证明说成已经完成该实例。

## 前瞻单因素消融

在开始实现前，`protocol.json` 已写明“只移除比较输入字节”的检查范围；运行前另写 `controls-plan.json`。两份源仅 `Action` 定义不同，固定地址、指针类型、半权限 RESERVED 编码、预期观测及共同输入证明：

- 保留字节：typed load 返回 RESERVED，Coq exit0。
- 移除字节：typed load 为 None；共同输入和空内存读取引理先通过，随后原预期指针等式被拒绝，Coq exit1。
- 正向语义定理 `EOComparisonReadNeedsBytes` 证明两者观测不同；不把编译失败本身冒充语义反例。

此实验只说明一次类型化读取需要输入字节，不证明整个变异 API 的执行，也不替代中断、所有权保持或所有下游机制的验证。

## 实测与保留失败

证据目录：`audit/logs/stage114-enabled-owned-taskcreate/`；最终实测以 `checkpoint-report.json` 及冻结清单为准。

- 稳定编译：生产 `proof22`、探针 `probe05` 均 exit0；此前失败尝试的源码快照和日志保留。
- 集成构建通过；280个活动 Coq 模块（177个当前目标、103个框架／策略）。这是已有产物上的集成构建，不冒称全新干净构建。
- 对43个新增证明根打印假设，并对280个活动模块及独立探针执行 `coqchk`；只允许既有 `classic` 和 `functional_extensionality_dep`，结果由 `trust.json` 核验。
- 新增结构回归8项通过；全量1590项中423项失败、1项错误，失败及错误 ID 与第113步相同。结构测试不替代 Coq 语义证明。
- `make audit` 仍因旧函数证据身份过期 exit2；项目结构子检查通过。`git diff --check` 仍是既有 `inferules.v` 六行尾空白，与第113步日志相同。未改旧门槛或删除失败。
- 六门仍为94／1／1／1／1／0，不授予新的生产整函数或整核覆盖信用。
- 固定 C／AST／配置和旧冻结证明保持；检查实际上游函数切片及模型哈希。本步没有重放逻辑修复目录，不把历史逻辑路径当本步实际重建。
- 逐项核对后仅清理本步临时 Coq 源及审计产物，保留生产产物、探针源码、编译快照和日志；清理细目见 `cleanup-inventory.json`。

未提交、未推送，Git HEAD 保持原值。

## 尚未完成与下一步

1. 本契约的合法优先级路径固定 counter0；正 ISR 计数返回60尚未与此 nullable 预留池统一。需要能容纳计数变化且一致的同一不变量，不能强制 counter0 后宣称覆盖 ISR。
2. 非空 TCB 分配、真实成功返回0及后续调度尚未接入该池；下一步优先接实际非空分配资源，不固定 snapshot 返回0来冒充动态分配。
3. 栈 Hook 函数体、生产全局 Inv、完整函数环境 `WFIFun` 与初始化仍开放。
4. 源码级完整 `GOOD_OS` 和同一程序 K1–K4 尚未闭合；阶段一未完成，不开始 uCOS3。
