# 第62步：OS_TCBInit成功分支的真实调用入口到第一个Hook

## 对象、接口与可观察结果

仍为固定uC/OS-II V2.93.01、固定配置和两类授权修复。fresh物化的94项身份完全一致，source identity为`74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da`。`OS_TCBInit`对应`os_core.c:2022..2151`；没有改C、配置、修复或已有证明。继续复用第61步的完整归一化函数语法，新增唯一活动源`certiucos/v293/proofs/V293TCBInitEntry.v`。

稳定接口`V293_OS_TCBInit_call_to_first_hook`从七个已求值实参的sfexec进入，构造9个fresh块，执行7次参数分配／store、2次局部分配、cpu_sr=0、临界区取出空闲TCB、18字段初始化、真实scall及Hook实参求值，停在第一个Hook的sfexec。实际continuation保留后续优先级表、第二Hook、发布及return语法，不是跳过它们。前提不含选定fresh9、NoDup、中间内存或执行结果；`V293_tcb_fresh_nine`由任意M的HalfPermMap有界性给出fresh9。

一个Mf同时拥有18个最终TCB字段、8个输入参数／局部单元、pop后链头及next、saved0和caller frame。保护caller存储不等于恢复caller执行环境：此刻callee九对象29字节仍存活。初始IE任意，si／ci和IE恢复到入口值；未执行Hook的函数查找或函数体。若P中Hook缺定义，证明同sfexec无loststep。

## 独立入口、负控与消融

独立probe显式编码TCB18个旧字段均Vundef、head209、TCB301:8、next301:28和5个保护字段；caller旧108指向602，值88，保护字601为77。没有预分配callee局部，不导入其他probe。p12／p11与next非空／NULL形成4份独立内存，IE任意；每例25项typed-load，IE开关共8参数实例、200项读回。并非任务共存、8次独立coqc或完整94函数程序；stack指针不解引用，不授有效stack信用。

前瞻冻结positive及四个只改结论的负控，证明体完全相同；错误Hook地址、priority、空闲链头、保护字分别在34／49／64／79行拒绝。它们检测终点敏感性，不是内部机制独立消融。

前瞻单因素lookup实验只改变P501，其他函数定义、同一终点代码／状态／内存均不变：原调用无loststep，提供测试sentinel后有sfexec到salloc的一步。sentinel不是真实源Hook，没有执行其body；只授函数查询可用性信用，不授分配／18store／优先级表／发布／return因果信用。初版harness因state中fun缺类型推断失败；第二版仅把证明中的显式exists改eexists，theorem statements、程序及fixture逐字不变；两个版本和失败均保留。

## 失败、信任边界与下一步

proof01仅prologue通过，不冒充最终证明；proof02..07失败保留，proof08通过，最后注释版本经正式make build重编并与production-final快照匹配。probe01／02因类型有效性实例失败，03／04通过；最终probe04快照为准。初稿生成器保留但不用于覆盖最终源码。

新增源无Axiom／Admitted／Parameter／Conjecture，不导入历史内核证明。50个Print Assumptions根及三模块coqchk、5项新增测试、完整回归与396条既有诊断的逐ID对照、缓存原字节恢复、旧14433文件／1105产物保护，以`audit/logs/stage62-tcb-success-entry/final-report.json`及非自引用manifest为最终记录。222源增量构建复用1105旧产物，不是cold build；不修改默认失败门槛。

固定输入五个端口Hook仅声明、无实现；应用Hook关闭不能消除CPU Hook。本轮不造noop、不修改端口、不新增受信契约。手工前端及ADR0005临界宏归一化擦除CPU_SR token字节效应，非verified frontend或原端口执行。定理只给存在性无交错轨迹，外层七实参表达式求值未含，不证明全执行安全、local Hoare、完整OS_TCBInit／OSInit或七调用Mf连接。

正式六门仍94/1/1/1/1/0，源码级GOOD_OS与同程序K1–K4开放，uCOS3未开始，目标active；没有Git提交或推送。下一优先明确真实端口实现／可核验外部规格，再接优先级表、第二Hook、发布、成功返回与OSTaskCreateExt、stack及七调用实际内存，不将片段累积误算整体完成。一次性scratch及probe产物先全盘点再全量复查后删除；生产产物、源码、用户数据、旧缓存与全部失败证据保留。
