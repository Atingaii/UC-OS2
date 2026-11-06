# 第144步：原切换的缓存契约与同步缺口

## 这一步解决什么

第143步已经把真实 `sfexec` 调度调用接到原全局切换，但切到优先级4的 Ready 后，`OSPrioCur` 实际 load 仍为6。本步不是继续增加一个有限正例，而是给出任意满足所有权前提的状态的通用接口，并把旧完整调用轨迹接到明确的反例结论。

`csrc/upstream/v2.93.01/checkout/Source/os_core.c` 的 `OS_Sched` 在调用 `OS_TASK_SW()` 前只增加计数器；分析端口 `csrc/analysis-port/os_cpu.h` 只有 `void OSCtxSw(void);` 声明。原 `pswitch_step` 只 typed store `OSTCBCur` 并改变执行任务，不写优先级缓存。不能据此编造端口函数体，更不能静默修改固定 C／AST／框架以获得通过。

## 通用接口

生产文件：`certiucos/v293/proofs/V293ReadyCacheContract.v`，已加入 `_CoqProject`。

- `V293_cache_current`：诊断性纯关系；实际 load 的缓存等于同一任务表中 current 的合法优先级。不是新生产 Inv，也不是新增转移规则。
- `V293_cache_current_iff`：对任意任务表、内存、任务及合法优先级，已知缓存值与目标任务记录时，该关系当且仅当两优先级相同。使用原优先级表示注入性，不把预期结论当公理。
- `V293_cache_current_mismatch`：不同优先级的直接拒绝定理。
- `V293_ready_cache_write`：完整 cache 所有权与 ready SWINV 构造成功的实际字节 store；不是调用者提供最终堆或成功 store。保留任意空间 frame、原 SWINV，以及缓存地址以外的每个字节。
- `V293_ready_switch_cache`：由同一内存执行原 `lpstep`／`pswitch_step`，构造实际 current 指针 store，保留 cache 所有权和全部 frame，返回实际 pointer/cache load，以及切换后 coherence 的充要条件。输入任务表必须等于实际 `O` 的 `abstcblsid` 槽；输出槽仍为同表，不能任取无关任务表作为 oracle。分离所有权已经足够，未额外要求 cache/current block 不等。

这些是任意状态的条件契约，不等于初始化可达性或所有运行轨迹上的性质。

## 单因素对照：两边都确实切换

探针：`audit/probes/V293ReadyCacheContractProbe.v`。

`SCwrite_switch_ablation` 先执行原调度尾段到同一 `Mtail`。正例由所有权构造唯一 cache 字节写入6→4，再执行原切换；负例只省略这一次写入，也实际执行原切换。task、target、current、代码、continuation、环境、aux、计数器及 frame 均不变。

Coq 同时证明：两边 current 实际 load 都是 Ready；正例 cache=4 且 coherent，负例 cache=6 且不 coherent；最终两堆在缓存一个地址以外的所有字节逐点相同。包括 current 指针的四个字节，证明使用真实 store 的逐字节结果，未用提前拒绝替代后续切换验证。

正例只是 **store＋原 switch 的资源契约充足性检验**：store 没有安装到冻结 C 或 AST，没有正例完整调用轨迹，也没有从外部端口声明推出执行这次 store。它不是端口实现已修复的证据。

`SCcall_gap` 则接第143步原 `sfexec` 全局闭包，保留真实 pointer/cache load，得到负例。因此缺口不是一张未执行的内存截图。有限实例仍是存在性、无交错执行，不是全部交错保证。

## 验证与冻结

前瞻协议在写新证明前保存于 `audit/logs/stage144-ready-cache-contract/protocol.json`；先记录完整旧文件基线及旧缓存。实际结果以本目录 `checkpoint-report.json`、`verification.json` 为准。

验证覆盖新根的 `Print Assumptions`、全部活动模块及旧额外探针的独立 `coqchk`、完整 build、8项新接口检查、清理前后全套测试，以及旧失败 ID 集合和数量精确比较。失败的首次编译及精简导入的失败记录全部保留，不覆盖、不删证据。Python 字符串检查仅防止接口/身份漂移，语义由 Coq 根证明。

没有更改源码、配置、旧 AST／framework／tactics 或旧检查点实质证据。不提交、不推送。

## 尚未完成与下一步

本步定位而非关闭端口同步缺口。仍须在已接受的源码级抽象边界上建立有来源的切换端口映射／契约实现，连接完整调度调用；不能把本步条件契约直接当作该实现。另有旧任务恢复、初始化、API／ISR 保持、生产全局语义 Inv、WFIFun 等义务。

六门保持 `94/1/1/1/1/0`；全套旧423失败／1错误及审计 `stale function evidence input identity` 继续如实保留。`GOOD_OS` 和同程序 K1–K4 未完成，uCOS3 未开始，总目标 active。
