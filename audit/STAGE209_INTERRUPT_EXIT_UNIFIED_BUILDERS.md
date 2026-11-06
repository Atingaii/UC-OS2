# 第209步：不调度与同优先级退出的统一真实 builders

## 本步解决的缺口

第205步已有不调度归一化本体的 Hoare 证明，第208步已有同优先级真实 builders 和受限三函数环境。本步先把不调度本体接到真实 `BuildPreI/BuildRetI`，再把两种退出路径合到同一个动态退出规格；没有假设整个退出函数正确。

- 生产文件：`certiucos/v293/proofs/V293OSIntExitUnifiedInternal.v`。
- 不调度接口：`V293_OSIntExit_quiet_builder_contract`。
- 统一接口：`V293_OSIntExit_unified_builder_contract`。
- 三函数环境：`V293_unified_exit_env_WFFunEnv`、`V293_unified_exit_env_WFIFun`。
- 具体探针：`audit/probes/V293OSIntExitUnifiedInternalProbe.v`。

对象仍是已接受的完整归一化退出本体，不是原始 CPU 调用的端口精化。本步**没有**覆盖不同任务 handoff，也没有建立生产 Inv 或完整源码级 `GOOD_OS`。

## 先理解“不调度”

设入口字节分别为 run、nest、locked。

| 前置条件 | 实际退出行为 | 返回 nesting |
| --- | --- | --- |
| run≠1 | 不进入运行分支，不进入临界区 | nest |
| run=1 且 nest≥2 | 进入临界区并递减，仍有中断嵌套，不调用调度器 | nest−1 |
| run=1 且 locked>0 | 进入临界区，若 nest>0 则递减；调度锁阻止调度 | max(nest−1,0) |

这三类条件可以重叠，不是三个新的运行时机制。统一使用 `V293_exit_quiet_depth` 描述返回值。前置还要求三个值均在字节范围、ISR 栈顶部合法。

不调度动态参数保存 aop、原 IE、ISR、ISR 栈和临界栈。普通外部断言只提供 running/nesting/lock 的全局地址和字节单元、当前任务不变量及调用者 frame；不含 saved、局部环境或预先假设的不遮蔽事实。真实 builder 的 saved 单局部 domain，加上三个全局名不同于 saved，推导局部不遮蔽。

unpack 把真实 builder 重排成第205步完整本体所需资源；pack 把返回资源和 saved 局部单元重新组装成 `BuildRetI`。外部断言的 `GoodFunAsrt`、调用者 frame 的 `GoodFrm` 分开证明，不把 IE/ISR/栈当作普通 frame。前后保持原 aop、IE、ISR、两栈和调用者资源。

## 为什么要统一规格

`V293_exit_path` 只读取逻辑参数头部的布尔标签：quiet 选择不调度契约，same 选择第208步同优先级契约。它不是 C 参数，不读取或改变运行时 IE；真正的 IE 仍在路径内部的逻辑载荷中。

实际程序、退出函数标识、saved 声明和函数体完全不变。`V293_OSIntExit_unified_builder_contract` 对任意真实 builders，根据标签直接调用已证明的 quiet 或 same 稳定接口。无效标签对应不可满足前置；不是新增运行时拒绝分支。

同一个增强 Spec 同时包含实际 OSIntExit、OSIntEnter、OS_SchedNew；逐一证明真实 builder→InfRules，再直接闭合 WFFunEnv/WFIFun。同优先级路径仍要求 running=1、nesting≤1、lock=0、最高就绪优先级等于当前缓存。两种路径的合并不让不同任务切换自动成立。

## 非空与单因素对照

`UBbig_owned` 从已独立构造的 `BLphysical_owned` 字节内存开始，加入具体 saved、running 和局部 domain；不是以目标前置或本体结论作为假设。新内存把 locked 参数开放，因而能见证 locked=1，而不是拿 locked=0 的旧状态冒充调度锁路径。

`UBquiet_pre_nonempty` 对任意合法 run/nest/locked 和原 IE 证明真实统一 builder 前置非空；`UBquiet_three_causes` 具体实例化 `(1,2,0)`、`(1,1,1)`、`(0,1,0)`，三者共享同一程序和规格，ISR 栈=[0]、临界栈=[false]、saved 原值1。见证中的 extra=Atrue 只接收未使用的既有资源；生产定理仍对任意满足 GoodFunAsrt/GoodFrm 的 frame 参数化，不删除所访问单元。

`UBsame_pre_nonempty` 从第208步独立见证推导统一 same 路径的前置；`UBsame_actual_program` 证明它与此前程序完全相同。两条路径均有具体前置，不是仅证明一个空前置环境。

`UBquiet_decode/UBquiet_valid` 排除解码失败和无效字节状态。`UBquiet_IE_control` 固定全部实际内存、IE=true、ISR、两栈和其他逻辑字段，仅把内部逻辑 IE 从 true 改为 false；两侧均成功解码且满足同一有效性条件，正控满足前置，反控由 Aie 矛盾排除。**这是规格与现场身份对照，不是两个完整程序变体执行，也不证明每个下游机制都工作。**

## 核验、失败保留及边界

证据目录：`audit/logs/stage209-interrupt-exit-unified-builders/`。

事前协议和基线先于实现冻结；每次编译保存快照、退出码和日志，失败不删除。Coq 活动期间不编辑 Coq 输入。26 根分别 Print Assumptions、两入口递归 coqchk；允许假设不扩大。固定源码、配置、AST 和全部旧证明/测试保持；重新构造三个配置后函数核对哈希。

新增5项结构回归，不冒充语义 TDD；全量回归与第208步逐项比较失败/错误标识及顺序，既有423个失败、1个错误仍保留。构建、项目审计、既有 coverage 审计及旧空白问题分别报告。稳定编译、实际退出码和最终数字以 `verification.json` 为准。

最终只清理逐项确认的一次性信任驱动、其产物和缓存备份；先恢复原缓存字节。源码、失败证据及可复用 Coq 产物保留。

具体 LocalInv 仍为见证，不代表生产可达性；真实 builder 断言不等于已经执行完局部分配/释放；参数化 Inv 不等于生产数据所有权已构造；归一化本体不等于端口 refinement。

## 接下来

下一项核心缺口是不同任务 handoff：需要实际提供任务切换规则所需的任务/抽象状态资源，不能把整段 InfRules 或生产 Inv 当作开放假设绕过。之后继续生产 ISR/LocalInv/WFInt、初始化、整核链接及同程序 K1–K4。

六门仍 `94/1/1/1/1/0`，`GOOD_OS` 未完成，uCOS3 未启动。目标保持 active；未提交或推送。
