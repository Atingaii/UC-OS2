# 第50步：OS_InitEventList 的完整函数调用

## 实际完成了什么

稳定接口 `V293_OS_InitEventList_call_return` 位于 `certiucos/v293/proofs/V293InitEventList.v`。从原始可写事件表和旧非空／任意链头出发，真实分配四个局部对象，执行一次 `OS_MemClr` 调用、原生while的一次迭代、尾部赋值，再执行void返回、free和caller恢复。返回同一个Mf中的可写资源，而不只是几个读回值。

源码是锁定V2.93.01及两项已授权修复后的 `os_core.c:1336–1373`。本步重新物化源码、重新预处理及Clang AST，94个配置后函数身份全部匹配冻结清单。配置后body SHA-256：`230bd821cc790a82385212f2bde26fb379626776971cc295ee8d39a3e2ebc796`。准确定位、全源码身份、命令及结果见 `logs/stage50-init-event-list/source/result.json`。

## 与真实C的连接

Clang固定分析布局检查：2个事件，每个16字节，表32字节；Type偏移0、Ptr偏移4、Cnt偏移8、Grp偏移10、Tbl偏移11。两个计数器均2字节，两个指针均4字节。直接复用原先已有的事件结构类型，不新造另一个对象定义。

`OSEventPtr` 的真实类型是 `void *`，模型不是TCB的Next或自引用结构指针。保留C中实际发生的两次Type=unused写入，即使先前清零已经产生相同值。for保留原生while，末尾执行计数器增量；不是用结果列表替代循环。

手工规范化包括：固定 `2u-1u` 为1、sizeof为32、隐式窄化／指针转换显式化、组合NULL指针转换归一化。所证执行中的计数器值只为0／1，不触及unsigned算术边界。`source-connection.json`核对Clang的声明、循环、写入、尾部及链头，`EventLiteralAST`另行核对字面Coq函数AST。**这些不是已验证的C前端，不授编译器或ABI信用。**

## 独立入口与同状态检查

`audit/probes/V293InitEventListProbe.v` 不导入其他审计probe。实际有限内存含：

- 事件块82的32个初始字节全255，而不是预置好的NULL表；
- 旧空闲链头块94指向121；
- 表后第32字节保护值17、独立保护字123；
- caller的41号变量指向块110，值7；callee也用41号名称，但用独立局部环境。

`EventLiteralEntry` 构造可居留入口所有权，不把入口当成公理。程序同时包含真实事件函数和真实清零函数。`EventConcreteExecution` 在同一个Mf建立全部30项读回，没有额外要求调用者证明每项readback type/val匹配的开放前提：2个Type、2个Ptr、1个头、22个其余零字节、3个frame。另证callee退出前ix=1、四局部全部12字节释放，以及同名caller变量恢复为7。

最终链：`OSEventFreeList → Tbl[0] → Tbl[1] → NULL`。

## 检查与反例范围

证据目录：`audit/logs/stage50-init-event-list/`，最终事实以 `final-report.json`／`final-evidence-manifest.json` 为准。正式构建199个活动源，复用985个旧产物，不是全仓source-only冷构建。信任检查同时打印既有框架／初始化根和本步根，并运行顶层框架及本步code/proof/probe的coqchk。

四项前瞻负控只改一个最终结论，所有目标proof body、fixture、生产代码和其他结论不变：第一链接错误、末尾非NULL、空闲头指向第二项、frame从123变124。必须在对应读回连接行拒绝。这是最终接口负控，**不是四个机制的独立消融，也不声称所有下游机制／所有执行safety因早拒绝而成立**。生产中保留真正清零，因为还要把初始非零的22个其余字节变零；本步没有声称已单独测量删除清零的效应。

Coq初始导入、语法及证明错误的快照／日志全部保留。旧测试、旧源、旧冻结证据、固定C／配置不可改。默认audit与全仓既有失败继续如实记录，不以删除测试或重写冻结证据造绿。

## 还不能声称什么

- 本步是存在性、无交错的完整单函数执行，不是local Hoare或所有执行safety。
- 入口要求准确P绑定、环境名称及类型、四个fresh互异局部块、返回资源避开被释放块、可写表及frame。没有假设中间内存或函数结果，但外围调用者仍须真正满足这些前提。
- **尚未连接第49步三调用的返回内存。** 下一步把事件资源作为前缀调用的frame携带，在实际TCB返回内存上构造fresh，再接事件调用。
- OSInit还有两个只有声明而无实现的port hook；Flag／Mem／Q及Idle／Stat任务初始化还需继续。即使接完第四个kernel调用，也不是完整OSInit入口可达性。
- OSStart、完整运行Inv／task／ISR、源码级GOOD_OS及同程序K1–K4均未完成；六阶段正式覆盖不晋级。uCOS3只能在阶段一完成后按老师附件继续，尚未启动。
- 未提交／推送Git，最终目标保持active。
