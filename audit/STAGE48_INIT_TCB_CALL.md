# 第48步：OS_InitTCBList完整调用及局部生命周期

## 本步接通了什么

固定V2.93.01配置后的`OS_InitTCBList`，现在有稳定接口：

`V293InitTCBCall.V293_OS_InitTCBList_call_return`

代码在`certiucos/v293/code/V293OSInitTCBCall.v`，证明在`certiucos/v293/proofs/V293InitTCBCall.v`。它从**没有callee局部存储**的入口，连接实际call、四次局部分配、完整函数体、void返回、free及恢复caller。四个声明按真实源码顺序为ix、ix_next、ptcb1、ptcb2，占1／1／4／4字节；不是先假设四个对象存在再只证明循环。

同一条轨迹中，两次真实OS_MemClr调用清零728字节TCB表及52字节优先级表，原生while执行12次，再写末项Next=NULL及两个链头。释放前Ms的ix为12；返回后Mf中四个局部块的全部10字节都不存在。Mf仍具有全局结果与frame的可写所有权，不只是读回结果。

返回资源迁移辅助引理只运输与环境无关的raw cells片段，并要求这些资源地址不在被释放块内；不把任意环境依赖断言R无条件搬回caller。

## 独立入口与读回

`audit/probes/V293InitTCBCallProbe.v`独立给出有限非零／未初始化入口、程序表及字面完整AST。caller非空，与callee使用同名标识符41，但指向另一存储块110，原值7。入口完全没有四个callee局部块90–93。

同一返回Mf检查12条Next链接、末项NULL、两个链头、13个优先级NULL槽、一个TCB零字节和四个保护值，共33个load实例。另一个Ms读回仅检查释放前ix=12，不混作返回后的读回。返回后重新求值caller的同名变量仍是7，所有10个局部字节都已释放。

这排除了“caller为空所以恢复错误不可见”“callee与caller共用变量”“只检查释放首字节”“返回值在另一份内存里”等具体问题。

## 证据与边界

机器证据位于`audit/logs/stage48-init-tcb-call/`：

- `source/result.json`及`source-call.json`：锁定源码身份、94函数身份、实际四声明顺序。C自然void返回归一化为显式sret；**人工映射，不是已验证前端**。
- `proof22.json`、`probe08.json`：当前通过版本；此前失败日志和源码快照全部保留，不改写为成功。
- `build.json`：正式195活动源构建通过，复用965个旧生产产物；**不是source-only冷构建**。
- `trust.json`：58个根的Print Assumptions及4模块coqchk全部通过；假设只包含既有classic、eq_rect_eq、functional_extensionality_dep，本步未新增公理或开放证明。
- `control-plan.json`执行前冻结四个单因素错误结论。`control-results.json`记录wrong-caller、freed-local-readable、wrong-final-null、frame-corruption，分别在243／245／246／246行被拒绝。证明体不变，只授予最终连接拒绝信用，**不是机制消融或下游全部safety**。
- `baseline-tests.json`／`final-tests.json`保留全仓实际失败；新增8项测试单独运行。全仓并非全绿，不能用新增测试通过替代旧回归结果。
- `final-report.json`／`final-evidence-manifest.json`记录最终哈希、完整回归、清理及旧证据保留；最终状态以这两份文件为准。

入口仍有明确fresh、四块NoDup、返回资源避开释放块等前提；标识符递增是alpha编号约定，不是运行时ix取值约束。当前是无交错**存在性执行轨迹**，不是Hoare/APIRule，也不是所有交错执行安全。193旧活动源、965旧产物、固定C／配置、旧测试及旧证据保持不变；仅追加两个活动源并更新三个中文索引／教学文档，历史检查点不被重写。

正式六门仍为94／1／1／1／1／0，未晋级。完整OSInit／OSStart可达性、任务与ISR、源码级GOOD_OS及同程序K1–K4仍开放，uCOS3尚未启动。未提交／推送Git。下一步沿锁定C的真实顺序组合初始化调用，在同一内存上连接任务／对象初始化与OSStart，而不是再造孤立入口。

## 回归中发现的缓存变化

首次新增测试在旧文件哈希门失败：正式构建给既有`.Makefile.coq.d`追加了两个新源的六条依赖规则。没有放宽门或修改测试；先保存生成后的完整缓存快照，再只在还原候选的哈希与冻结baseline完全一致时恢复既有缓存。`dependency-cache-restoration.json`记录准确原因与前后哈希。首次失败日志保留；第二次新增8项测试全部通过。该恢复不改变源码、Coq产物或已经完成的构建／coqchk证据；下次make仍可再生成依赖。

## 最终回归结果

本步全仓1177项：394失败、1错误；基线1169项：393失败、1错误。原有394个失败／错误诊断ID全部保留，无旧失败消失。新增8项全部通过；唯一增加的旧测试失败来自第47步仍要求活动源恰好193的历史快照断言，本步追加两个源后为195，未改旧测试迎合新状态。默认`make audit`仍退出2（历史覆盖证据过期），范围检查、固定C检查和`git diff --check`通过。
