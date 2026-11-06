# 第203步：把中断进入函数纳入共同函数证明环境

## 这次解决什么

前一步证明了一条实际中断进入、调用和返回轨迹，但一条轨迹不能代替整核所需的函数环境证明。本步沿用已有时间组件，建立同一个内部程序 `P` 和规格 `Spec`：

| 层次 | 本步接入 | 检查内容 |
| --- | --- | --- |
| API | OSVersion、OSTimeSet、OSTimeGet | 同一 `Spec` 下的原 `WFAPI` |
| 内部可调用函数 | OSIntEnter、OS_SchedNew | `WFFunEnv`、`WFIFun`、定义域、函数查找与语法 |
| 共同逻辑上下文 | 原 `time_names_li`、`time_shared_inv` | 同一个 name-only LocalInv 和既有局部 GoodI |

这里 OSIntEnter 按框架的**内部可调用函数角色**连接；不是宣称它已有公共 API 规格，更不是把它安装成生产 ISR。

稳定接口为 `V293_irq_clock_components_checked`。两个内部函数的每个实际 `BuildPreI` / `BuildRetI` 成功输入，均直接调用原有通用合同生成 `InfRules`，没有把“函数体已经正确”或 `WFFunEnv` 本身作为前提。不是将单函数环境结论直接套到合并后的环境。

通用接口允许 API 标识左优先覆盖，故不宣称对所有参数均有五个不同函数；独立数值实例使用三个不同 API 标识及两个不同内部标识，`FEfive_entries` 明确检查五个真实定义。

## 如何排除空前置条件带来的假进展

`FEchecked` 使用相同 `FEP/FESpec/FELI`。`FEsched_nonvacuous` 与 `FEenter_nonvacuous` 各自构造真实 builder 和满足其前置的非空物理资源，共用一个兼容的 `FEGE`：调度输入、当前任务指针、中断 running/nesting 等绑定不冲突。

这是**两个不同调用状态**，不是同一时刻重复拥有共享内存；也不是初始化可达性。调度状态含局部 y，进入状态局部环境为空。name-only LocalInv 只约束时间变量的名字绑定，不拥有完整任务表；局部 `GoodI` 不能冒充生产调度/ISR 全局不变量。

## 预先固定的单因素对照

1. 仅移除 OSIntEnter 定义，`Spec` 与其他定义保持不变：定义域不匹配，拒绝 `WFFunEnv`。
2. 仅将该函数返回类型从 `Tvoid` 改成 `Tint32`，函数体、参数和局部声明保持不变：定义域仍匹配，但完整 `WFFunEnv` 的类型/定义义务拒绝。

`FEonly_entry_changed` 证明其他标识不变，正确替换恰等于原程序。这两个对照只测**函数链接/类型边界**，不声称验证执行路径、ISR 或所有下游机制。

## 验证与边界

五个配置后 C 定义均从锁定源码重新预处理，核对定义、函数体、物理源码范围和文件哈希。证据见 `audit/logs/stage203-interrupt-function-environment/`：失败编译保留；稳定编译、逐根假设及递归 `coqchk`、结构测试、全量回归、旧文件身份与清理结果由最终 `verification.json` 记录。

没有改 C、配置、AST、旧证明、框架或旧失败来制造通过。既有审计身份过期及框架行尾空白仍保留。六门仍为 `94/1/1/1/1/0`，不是覆盖进度升级。

**尚未完成**：将 OSIntExit 接入此环境、生产 WFInt/ISR、完整任务不变量、初始化、全函数环境、全局模拟、源码级 GOOD_OS 与同程序 K1–K4。uCOS3 尚未开始，目标保持 active。

下一步应对齐 OSIntExit 所需的调度调用规格和共同不变量，推进真实函数环境义务，而非继续用相似存在性轨迹替代这些义务。
