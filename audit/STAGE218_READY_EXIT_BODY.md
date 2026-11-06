# 第218步：同一就绪共享不变量下的完整退出本体

## 从哪里接着做

第217步已将真实 `OS_SchedNew` 调用、目标指针赋值、不同优先级 guard、计数器递增、缓存复制与原 switch 接到同一个 ready/TCB/storage Inv。本步沿这一接口向外连接完整归一化 `OSIntExit` 本体，不新增运行时代码，也不改变固定 C、配置、AST、框架、tactics 或旧证明。

这里的“完整本体”指完整的语句序列，不是覆盖全部输入路径的生产函数契约。当前前置仍限定 running=1、lock=0、nesting≤1、不同优先级、原 IE=false、ISR 全清，且调用者已打开共享资源并分配 saved 局部单元。

固定源码身份从四个实际配置后函数重建：`OSIntEnter`、`OSIntExit`、`OS_SchedNew`、`OS_Sched`。准确的定义、来源定位和哈希在本步 `source-check.json` 与 `source-recheck.json`，没有替换发行版或修改旧冻结证据。

## 新的上层接口

生产文件：`certiucos/v293/proofs/V293OSIntExitReadyBody.v`。

`V293_OSIntExit_ready_body` 在单条 `InfRules`、同一个 `V293_ready_storage_inv` 下连接：

1. saved 初始化为0；
2. 实际 running guard；
3. 实际 encrit；
4. nesting 递减以及 nesting/lock guards；
5. 第217步真实 dispatch，包括实际调度调用和 switch；
6. 原线程恢复后的实际 excrit；
7. 无返回值 return。

没有把完整本体的 Hoare 结论当成前提，也没有用断言等价直接迁移 `InfRules` 的 Inv 索引。调用边界仍显式要求实际 callee 规格 lookup；完整统一的函数环境尚未建立。

### 为什么重证 excrit

旧 storage Inv 下的 excrit 结论不能直接换成新的 ready/TCB/storage Inv。本步证明 `V293_ready_storage_full_open/close`，在真实资源级别打开/关闭同一 Inv，然后用 `excrit2_rule` 重新证明 `V293_ready_storage_resumed_excrit`。

ready 位图、优先级表、TCB 记录、dispatch 指针和控制存储在切换前一起关闭到 Inv。running/nesting/lock 与 lookup 的完整所有权也转成带类型存储归还；恢复后不声称它们仍取本次调用之前的共享值。恢复断言仅保留同一 Inv、线程身份、控制栈、环境、saved 单元及规则允许的调用者 frame。通用 `px` 只要求 `GoodFrm`，不等于已完成全程序线程私有数据分类。

## 独立完整入口不是空前提

探针：`audit/probes/V293OSIntExitReadyBodyProbe.v`。

`JBentry` 从实际字节和独立抽象任务表构造完整入口，未使用第217步局部后缀的只读 lookup 夹具：

- `OSTCBCur` 使用 `Tptr V293_tcb_type`，不是旧夹具的 `Tvoid` 指针；
- lookup 为256字节完整可写数组；ready 行为 `[16;0]`，group 按真实计算为1；
- 优先级表13项，选中 priority=4 的 ready 任务，当前任务 priority=6 且等待；
- TCB 的所有权覆盖当前 Inv 要求的记录字段，不声称包含整个 C TCB 全布局；
- high 初值88、counter 任意32位值、running=1、lock=0、saved 任意值；内存拼接有真实不重叠证明。

`JBentry_nonempty` 给出 nesting=0/1 的非空前置和最高就绪任务事实；`JBactual_body` 在同一实际地址、任务表和资源下实例化完整接口。counter、saved、临界栈及剩余抽象动作均为量化参数，因此最大 UINT32 counter 也在定理覆盖范围；这不是声称已执行两份完整函数轨迹。

## 单因素对照的准确范围

前瞻协议只要求局部临界栈尾段对照。`JBexcrit_control` 固定物理堆、抽象资源、环境和原控制状态：

| 变体 | 操作 | 临界栈结果 |
| --- | --- | --- |
| 保留 excrit | 实际 `loststep` | `false::ci` 弹为 `ci` |
| 中性化为 skip | 不改变状态 | 原状态不满足要求 `Acs ci` 的后置 |

不满足性由列表长度矛盾证明，对任意 `ci` 成立。对照说明实际退出临界区原语不可省略，但只覆盖最后原语，不是两份完整 OSIntExit 执行，也不替代完整函数上下文中的变体运行。

## 核验和保留的旧失败

本步证据目录：`audit/logs/stage218-ready-exit-body/`。准确实测数值以 `verification.json` 为准，逐根假设见 `assumptions-by-root.json`。

- 新本体与探针稳定编译，逐根 `Print Assumptions`，两个入口模块递归 `coqchk`；不增加许可公理。本次检查26个根，输入656份 Coq 源文件（含一次性驱动）；实际假设仅 `Classical_Prop.classic` 与 `FunctionalExtensionality.functional_extensionality_dep`。
- 两次全量构建和项目审计退出码均为0，五个新增结构回归全部通过。结构回归检查接口、来源、编译身份和实验边界，不冒充语义 TDD。
- 全量 tests 共2254项，与第217步逐项比较原失败/错误的身份及顺序完全一致。既有423 failures、1 error保留，未通过改写冻结证据制造通过。
- `make audit` 的旧函数证据身份过期错误和 `inferules.v` 的旧空白检查失败保留。
- 失败编译、源码快照、诊断重放和日志保留；先清点再删除本步一次性信任驱动与编译物，恢复原有两份算术缓存，不清理旧产物或用户数据。

## 下一步与仍开放事项

下一步把这个新 Inv 下的完整本体接入真实 `BuildPreI`/`BuildRetI`，再迁移三路径统一 Spec 和函数环境。协议中的 builders 拓展本步未实施，不将其记为完成。

仍开放：lookup 内容关系、控制值语义、cache/current 关系、生产 ISR/LocalInv、WFInt、全初始化及同程序整体连接。归一化 handoff 按既定 ADR-0010 接受的源码抽象边界处理，不等于原端口外部函数体、编译器、ABI 或硬件验证。

六门保持 `94 / 1 / 1 / 1 / 1 / 0`；源码级 `GOOD_OS` 和同程序 K1–K4 未完成，uCOS3 未启动。总目标仍 active；本步未提交、推送。
