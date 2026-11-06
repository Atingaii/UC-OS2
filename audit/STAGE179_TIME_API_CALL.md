# 第179步：时间 API 的真实调用与局部分配

## 从哪里推进到哪里

第178步证明了同一物理堆上 `strong core ** actual caller pre` 可以同时成立，但该堆的两个局部槽已经存在。它不能证明机器会真正创建这些槽。

本步从**没有 API 局部槽的旧 `TRmemory`** 出发，在既有小步语义 `loststep` 的有限闭包中执行原 `OSTimeGet / OSTimeSet` 调用，最终到达原函数体入口。这个实际分配产生的同一终点同时满足强共享 core 和真实 `BuildPreA'` 前置条件。没有改写 C、配置、AST、框架、旧不变量或旧证据。

## 给初学者的理解

可以把一次函数调用分成三段：

1. **调用准备**：求值实参，保存调用者环境，分配参数和局部变量。本步补上这一段。
2. **函数体执行**：初始化 saved，进入临界区，读取或设置时钟，再退出临界区。既有局部 Hoare 证明不能直接冒充一条完整执行轨迹。
3. **返回**：释放局部槽，恢复调用者环境并交付返回值。还需要把同一实际轨迹继续接过去。

因此本步不是把“整核正确”勾选完成，而是消除“入口资源虽然合法，但可能根本进不去”的缺口。

## 生产接口

新增 `certiucos/v293/proofs/V293TimeAPICall.v`，5个证明根：

- `V293_time_parameter_store`：从实际未初始化参数槽的所有权构造一次成功 `store`，同时保持空间 frame。
- `V293_time_get_call_entry`：实际无参 call、函数查找、两个 local 分配和分配结束，共5个小步，到达原 getter body；两个槽都是 `Vundef`。
- `V293_time_fresh_after_alloc / V293_time_fresh_after_store`：不同 block 的分配或写入不会破坏另一 block 的 fresh 性。
- `V293_time_set_call_entry`：实际有参 call、常量求值、实参列表结束、函数查找、参数分配及真实写入、saved 分配和分配结束，共7个小步，到达原 setter body。参数槽确为 `Vint32 n`，saved 为 `Vundef`。

两个入口定理量化程序、调用者环境、续延、内存、IRQ 与抽象资源；但前提中的空间 frame **在最终 callee 环境中评价**，不承诺任意 caller 断言都能跨名字变化运输。`kcall` 保存原 caller 环境，不据此声称已经执行返回。

## 同一程序、同一终点

探针 `audit/probes/V293TimeAPICallProbe.v` 仍用上一轮 `pumerge RAapi RAinternal`，不是另建只含 getter／setter 的替代程序。强 core 仍保留 TCB、ready bitmap、priority table、当前指针和 clock。

| 资源 | 地址 | 调用前后变化 |
| --- | --- | --- |
| clock | block150 | 两条调用准备轨迹都保持原字节与原 clock |
| ticks | block160 | 调用前 fresh；getter 分配 Vundef，setter 分配并写入 n |
| saved | block161 | 调用前 fresh；两者分配 Vundef |
| 其他块 | 原布局 | 所有非160／161块的每个字节保持不变 |

`Cget_actual_call / Cset_actual_call` 分别给出实际轨迹、精确 `BuildPreA'`／`BuildRetA'` 等式、原完整 body 的既有 `InfRules` 契约、**同一实际 Mf 上** `Ccore ** caller pre`，以及非局部字节保持。契约通过真实 builder 的精确 `Some` 等式识别，不用 body 证明充当内存存在性的 oracle。

## 前瞻协议与对照

实现前冻结的协议见 `audit/logs/stage179-time-api-call/protocol.json`，未事后改写。

| 对照 | 固定因素 | 机器证据 |
| --- | --- | --- |
| 正控 | 原程序、原 body、旧强 core 与 abstract map | 从无 locals 的 TRmemory 真正调用并分配，到达满足 builder pre 的终点 |
| 只改实参 | 相同 caller／ks／ct／clock／lg／初始内存／程序 | `Cset_two_argument_control` 给出 n 与 bad 两条实际调用，各自正确 caller pre 与同一强 core 均接受，clock 都不变 |
| 独立参数负控 | 已执行 bad 调用的同一终点与正确 action | 实际160块 load=bad，旧值 n 的局部断言不能成立；不依赖 action guard 的早拒 |
| fresh | 原旧堆字节 | `Cfresh` 证明160／161确实未分配，生产引理维持后续 fresh；不是把已分配 Jmemory 当起点 |
| caller 同名变量 | caller 的1002绑定到有实际 clock 字节的150块 | `Ccaller_shadow_control`：callee 的1002绑定新160块，kcall精确保留原caller，150块值不变 |

实参两运行的 ghost action 随对应 API 实参变化，初始**机器状态**和其他源程序输入不变；负控在新调用的同一 action 下只检查错误局部值。因此不声称两种 API action 在同一状态同时成立，也不靠 action 不同制造参数内存检查通过。

## 源码身份与边界

固定 V2.93.01 提交与授权修复不变。`os_time.c` 原文件 SHA256 为 `a53a16a53e8d9cf1f508e97914d7cc91ea33019d8dfc3d6bc60741005bebb346`，getter定位237–250行，setter定位267–278行；两段与既有 AST 映射的哈希单独检查，宏抽象仍沿用 ADR0005。

不新增 Inv、Spec 或空 hook。语义轨迹不包含 ghost O／op 的变化；它们仅用于入口终点的资源满足关系。参数 ct 的通用 fixture 见证不意味着所有 ct 都是有效生产运行态，生产初始化仍需另证。

本步**只到原 body 入口**，不是 call→body→return 完整轨迹，不证明中断交错、全局初始化、完整生产 LocalInv、tick／hook／ISR 安装或全程序环境。三 API 与内部调度器的局部环境不等于完整内核环境。六门仍为 `94 / 1 / 1 / 1 / 1 / 0`；同程序 K1–K4 与最终源码级 `GOOD_OS` 开放，第一阶段未完成，uCOS3尚未开始，总目标 active。

## 复核与下一步

稳定编译身份见 `stable-compiles.json`；所有中间失败日志及源码快照保留。17个根的 `Print Assumptions` 与两个新入口及递归依赖的 `coqchk` 结果见 `trust.json`，不冒充全部历史入口重检。新增5项 Python 回归核对源码身份、真实步骤结构、终点契约、对照与递归检查身份；文本检查本身不是语义证明。

全套回归在新增前与文档定稿后比较完整失败／错误 ID，不删旧失败或削弱门。实际测试数量、构建、范围审计、旧覆盖身份与旧空白失败、旧文件哈希、清理和最终冻结，以本目录 `verification.json` 及原始日志为准。没有提交或推送。

下一步从本次**真实分配产生的同一 Mf** 继续原 body 的 saved 初始化、临界区与时钟访问，并接释放／返回；继续补生产共享状态和全程序环境。不能再次把“已分配资源分别非空”当作新增进展，也不能将本步调用准备等同于整核完成。

## 本轮实际观测

- 稳定生产编译为 body08，探针为 probe10；18次编译中的14次非零诊断和全部快照保留，未把技术失败算作消融成功。
- 17根假设检查通过；两个入口的递归 coqchk 通过，用时293.80秒。573份 Coq 输入在检查期间保持不变；实际仅使用既有 classic 与 functional_extensionality_dep，允许集合未扩大。
- 新增5项回归全部通过。新增前全套2053项与上轮完全相同的423失败／1错误ID已核对；新增后两次完整运行的2058项及ID对照由最终 verification.json 再核对，不以本段文字代替原始结果。
- make build 与项目范围审计通过。make audit 仍因旧 stale function evidence input identity 退出2；git diff --check 仍为 inferules.v 581–586 六行旧空白。本轮新增交付文件单独检查无行尾空白。
- 最终清理只针对逐项确认的一次性 Trust 驱动及产物、原缓存备份和本轮新测试的可再生 Python 缓存；恢复原 lia／nia 缓存，保留交付源码、所有失败快照／日志与可复用 Coq 产物。清理明细由 cleanup.json 记录。
