# 第219步：就绪共享不变量接入真实函数入口与返回

## 这一步解决什么

第218步已证明完整归一化 `OSIntExit` 的不同优先级路径，但入口要求调用者事先准备内部局部变量及名称不遮蔽条件。本步把这条证明接入框架实际 `BuildPreI` / `BuildRetI`，使上层可以使用函数接口，而不是手工拼内部断言。

固定目标仍为 uC/OS-II V2.93.01；C、配置、既有 AST、框架、tactics、旧证明与旧冻结证据不变。四个配置后函数 `OSIntEnter` / `OSIntExit` / `OS_SchedNew` / `OS_Sched` 从固定源码重建并核对哈希、定位，见本步 `source-check.json` 与 `source-recheck.json`。这不新增 C→归一化 AST 的翻译正确性声明。

## 上层可调用的结果

生产文件：`certiucos/v293/proofs/V293OSIntExitReadyInternal.v`。

稳定接口：`V293_OSIntExit_ready_builder_contract`。

连接顺序：

1. 展开实际 `BuildPreI`，检查空形参/实参匹配，取得 saved 局部单元及单局部 domain；
2. 外部前置使用 `GoodFunAsrt`，不依赖调用者局部环境；
3. `V293_ready_builder_unpack` 从真实全局绑定和 saved domain 推出名称不遮蔽，借出局部单元；
4. 直接应用第218步在同一 `V293_ready_storage_inv` 下的完整归一化本体：saved 初始化、running guard、encrit、nesting/lock guards、真实调度与 switch、原线程恢复后的 excrit、return；
5. `V293_ready_builder_pack` 归还局部单元/domain，并满足真实 `BuildRetI`。

主定理只有一个 `InfRules` 结论，没有把完整本体的 Hoare 当成前提，也没有通过断言等价替换 `InfRules` 的 Inv 索引。复用的第213步 valid 与 high-binding 引理属于当前 V293 工程，分别处理纯约束和空资源环境，不用于旧 Inv 的证明迁移。

### 共享资源没有变成私有快照

外部物理资源增加真实类型的 TCB 记录所有权，交给第218步本体后关闭到同一 ready/TCB/storage Inv。切换后不保留切换前的 tasks、events、now、entries、nest 或 counter 值；后置保留同一共享 Inv、线程身份、控制栈、全局环境、调用者 extra 以及 builder 要求的局部单元。

extra 同时要求 `GoodFunAsrt` 和 `GoodFrm`。这不是已经完成全程序线程私有数据分类的声明。后置局部单元的值由 builder 存在量化，并不把共享值冻结为调用前快照。

## 非空入口与单因素对照

探针：`audit/probes/V293OSIntExitReadyInternalProbe.v`。

- `RBbuilders`：真实 builders 返回本步所用的前后置。
- `RBpre_owned`：在第218步独立实际字节夹具上补全真实 globals/domain，构造实际 builder 前置；不是假设该前置。
- `RBentry_nonempty`：最高就绪任务为实际不同任务，入口存在；任意 counter、saved 原值、critical stack，nesting≤1。
- `RBzero_max_entry`：显式覆盖 nesting=0、最大 UINT32 counter。
- `RBactual_contract`：在同一真实类型 TCB、完整可写 lookup、ready 和控制字节参数下实例化生产接口。

物理夹具来自第218步冻结的 JB 内存，而不是旧 Tvoid 指针或缺少 TCB 所有权的夹具。TCB 记录仅指 Inv 所需字段，不声称已覆盖完整 C 布局或启动可达性。

`RBshadow_control` 只改变 saved 声明和局部绑定的名称（120→running 的112），所有物理字节保持相同。正常与变体两侧 builder 前置都可满足，但变体不能满足内部 running 不遮蔽绑定；因此必须保留生产接口的名称不同约束。**这是 builder/名称边界对照，不是两份完整函数执行，不据此给下游机制补记成功。**

另有精确边界观察：`BuildPreI` 拒绝非空实参；`BuildRetI` 不检查这个数量，仍返回 `Some`。不把返回 builder 描述成实参数量检查器。

## 核验与保留失败

机器结果见 `audit/logs/stage219-ready-exit-builders/verification.json`，逐根假设与递归检查见 `trust.json` / `assumptions-by-root.json`。核验包括两个入口模块递归 `coqchk`、两次构建、完整 tests、项目审计、固定源码重建与字节保护。结构测试不冒充语义 TDD，语义证据来自 Coq。

实测结果：

| 检查 | 结果 |
| --- | --- |
| 新增生产接口/探针根 | 18 个逐根假设检查通过 |
| 递归 `coqchk` | 两个入口及递归依赖通过，约289.5秒 |
| Coq 输入身份 | 检查期间658份输入未变（含一次性 Trust 驱动） |
| 构建 | 两次退出码0；不是全新清缓存构建声明 |
| 新结构回归 | 5/5通过 |
| 全量 tests | 2259项，423失败、1错误；旧失败/错误ID及顺序与218完全相同 |
| 项目审计 | 通过 |
| `make audit` | 退出码2，旧函数覆盖证据身份失配 |
| `git diff --check` | 退出码2，旧 inferules.v 第581–586行空白；输出与218逐字节相同 |

实际假设为 `Classical_Prop.classic` 和 `FunctionalExtensionality.functional_extensionality_dep`，未扩大第218步允许集；不把允许但未使用的 Eqdep 假设记作实际依赖。

全量回归保留第218步的旧失败与错误身份、顺序；`make audit` 的旧覆盖证据身份失配及旧空白错误也保留，不改门限或冻结报告制造通过。所有失败编译源码/日志保留。清理前逐项记录一次性信任驱动及其编译产物、缓存备份；恢复既有算术缓存，保留源文件、交付证据与可复用 Coq 产物。

## 还没有完成的工作

当前仍限 running=1、lock=0、nesting≤1、不同优先级、原 IE=false、ISR 全清；入口仍是已打开共享资源的函数边界。

本模块运行快照仍是参数。第215步动态逻辑实参、第214步统一 quiet/same/changed Spec 与生产函数环境尚未迁移到这个新 Inv；不能把旧 storage Inv 下的结果算作新 Inv 已完成。后续首先连接动态快照/统一规格，再处理完整生产 Inv 的控制值、lookup、缓存—当前任务关系、生产 ISR/LocalInv、WFInt 与初始化。

六门仍为 **94/1/1/1/1/0**。最终源码级 `GOOD_OS`、同程序 K1–K4 尚未闭合，uCOS3 未启动；总目标保持 active。本步未提交或推送。
