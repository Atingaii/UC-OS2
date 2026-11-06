# 第220步：动态快照与统一函数环境接入就绪共享不变量

## 本步解决的问题

第219步已经在新的 ready/TCB/storage 不变量下证明真实函数 builders，但运行快照仍是模块参数；第215步的动态规格与统一函数环境只适用于旧 storage 不变量，不能直接记作新不变量的成果。

本步把这条缺口真正接起来：运行时快照进入逻辑实参，归一化 `OSIntExit` 的 quiet/same/changed 三条路径共用一个调度规格，`OSIntExit`、`OSIntEnter`、`OS_SchedNew` 的函数环境也使用同一个新的不变量。没有改动 C、配置、既有 AST、框架、tactics、旧证明或旧冻结证据。

这仍是三个内部函数的局部环境，不是94个配置函数的完整生产程序。

## 可供下一层使用的接口

生产文件：`certiucos/v293/proofs/V293OSIntExitReadyDynamic.v`。

| 接口 | 含义 |
| --- | --- |
| `V293_ready_dynamic_exit_inv` | 与第219步定义相同的 ready/TCB/storage 不变量；不依赖某次运行的快照 |
| `V293_ready_dynamic_exit_inv_good` | 该不变量实际满足框架 `GoodI` |
| `V293_ready_dynamic_changed_fpre/fpost` | 从逻辑实参解码快照，直接调用第219步真实 builders 的外部断言；畸形编码为 `Afalse` |
| `V293_ready_dynamic_changed_builder_contract` | 真实 `BuildPreI` / `BuildRetI` 接到第219步完整本体，而非假设本体 Hoare |
| `V293_OSIntExit_ready_dynamic_builder_contract` | 三条退出路径共用 joint 调度 lookup 和同一新不变量 |
| `V293_ready_dynamic_exit_env_WFFunEnv/WFIFun` | 对三函数环境逐函数构造实际本体及 builders 义务 |

### 不是把不变量索引强行替换

changed 分支直接使用新不变量下的第219步定理。quiet/same 复用本来就对环境不变量泛化的当前 V293 契约；调度 lookup 经已证 `V293_critical_to_joint` / `V293_ISR_to_joint` 嵌入。既有无 `scalle` 语法约束仍由真实本体满足，不放宽框架规则，也没有使用 `InfRules` 的 Inv transport。

### 只保留必要的快照约束

复用第215步已经证明往返与单射的 `V293_changed_snapshot` / encode / decode，不复制 codec。

旧动态模块需要 `table_length` 来把依赖 entries 长度的旧 storage 不变量改写成固定索引。新的 ready 不变量已经固定真实就绪表语义，不依赖这次快照的 entries 长度，所以不再添加这个模块参数、额外长度门和 Inv 重写引理。**真实优先级表13项约束仍由第219步 valid / priority-table 关系保留，不是取消实际边界检查。**

返回仍持有同一共享不变量，不冻结切换前 tasks/events/now/entries/nest/counter；`RDpost_forgets_counter` 额外证明，只改变 counter 快照时返回断言完全相同。aop 和控制栈并未因此变成无关参数。

## 非空入口与单因素消融

探针：`audit/probes/V293OSIntExitReadyDynamicProbe.v`。

- `RDenvironment`：实例化同一真实类型 TCB、相同物理地址布局下的 `GoodI`、`WFFunEnv`、`WFIFun`。
- `RDbuilders` / `RDactual_contract`：实际 builders 和实际统一 Spec 下完整归一化本体的实例，而非另一个小程序。
- `RDpre_reduces`：合法动态逻辑实参的入口正好化为第219步真实 builder 入口，没有附加无关长度条件。
- `RDchanged_nonempty` / `RDentry_nonempty`：从独立 JB 的完整 lookup、真实 TCB 记录、ready 和控制字节构造前置，最高就绪任务确实不同于当前等待任务；覆盖 nesting≤1、任意 UINT32 counter、saved 原值和 critical stack。
- `RDzero_max_entry`：显式覆盖 nesting=0 与最大计数器。
- `RDmalformed` / `RDpath_tag_reduces`：畸形编码被拒，另一个路径 tag 确实进入通用 quiet/same 契约。

`RDcounter_dynamic_control` 固定同一个最大计数器物理状态，只把逻辑 counter 快照从最大值改成1：两种快照 codec 都合法，匹配入口非空；错误快照由 `RDcounter_load` 提取出的实际95块 `Tint32` load 排除。因此这不是编码门提前拒绝造成的伪消融。

**该对照只测试入口资源匹配，不是两份完整函数执行，也不能据此声称所有下游机制或初始化均已验证。**

## 核验

核验结果与清理清单记录在 `audit/logs/stage220-ready-dynamic-environment/`。结构回归不冒充语义 TDD；语义证据为 Coq 根、逐根假设与递归内核检查。准确配置后的四个 C 函数重建与哈希核对只证明源码身份，不是新增 C→AST 翻译正确性证明。

实测结果：

| 检查 | 结果 |
| --- | --- |
| 生产/探针根 | 18个逐根假设检查通过 |
| 两个入口递归 `coqchk` | 退出码0，约365.8秒 |
| 检查期间 Coq 输入 | 660份未变，含一次性 Trust 驱动 |
| 构建 | 两次退出码0；增量构建，不声称清空缓存后的 clean build |
| 新结构回归 | 5/5通过 |
| 全量 tests | 2264项，423失败、1错误；旧失败/错误ID及顺序与219完全一致 |
| 项目审计 | 通过 |
| `make audit` | 退出码2；保留旧函数证据身份失配 |
| `git diff --check` | 退出码2；旧 inferules.v 第581–586行空白，输出与219逐字节相同 |

实际假设为 `Classical_Prop.classic` 和 `FunctionalExtensionality.functional_extensionality_dep`，未扩大允许集。生产 stable 为 internal02，探针 stable 为 probe01；internal01等全部编译快照与日志保留，本步没有失败编译。旧冻结证据除明确允许变更的文档/工程配置文件外按字节保护。

清理前逐项清点本步一次性 Trust 源码、Coq 产物与缓存备份；恢复原有算术缓存，保留交付源码、证据、可复用依赖与生产/探针编译产物。清理与只读复核见 `cleanup.json` / `final-recheck.log`。

## 与最终目标的距离与下一条实质义务

`framework/proof/toptheorem.v` 的 `verified_os'` 明确要求同一实际程序上的 `WFAPI`、`WFInt`、`WFIFun` 和初始化 `side_condition`。本步给出的是三函数 unit 的 `WFIFun` 与同一 Inv 的 `GoodI`，不是这些完整前提，更不是 `GOOD_OS`。

下一步应从真实 `BuildintPre` / `BuildintRet` 的资源出发，连接 ISR 入口到本步动态规格，而不是继续只叠加包装定理。当前核心阻碍已能定位：

1. `framework/logic/inferules.v` 的中断 builder 提供 `invlth_noisr I 0 i`、实际 ISR 位和 `i::si`，不是直接提供已打开的 changed 前置。
2. 当前 Inv 的 ready/TCB 语义已存在，但 lookup 与运行/嵌套/锁等控制单元仍只是存储所有权；不能据此任意推出运行值、最高就绪缓存或 lookup 内容。
3. `V293InterruptSourceRoundtrip.v` 的 EOI→enter→exit→exint 是具体执行结果，不是 `WFInt`；现有 changed 前置要求 clear ISR 和原 IE=false，必须从实际中断入口推导，而非重新假设结论。
4. quiet/same 的泛化契约已经在统一规格下证明，但本步没有额外构造与 changed 同布局的所有有效入口，也未证明初始化可达。

需要对这些缺口逐一给出真实资源推导、反例或明确约束；不可令初始化为 false、令有效调用前置为空，或删除配置中的功能来制造整核通过。

六门仍 **94/1/1/1/1/0**。源码级 `GOOD_OS`、同程序 K1–K4、生产 ISR/LocalInv、`WFInt` 和初始化仍开放，uCOS3 未开始。总目标保持 active；本步未提交或推送。
