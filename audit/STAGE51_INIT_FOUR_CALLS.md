# 第51步：四个真实初始化调用接入同一内存轨迹

## 这一步解决的问题

之前，前三个初始化调用已经串联，事件初始化只有独立的完整调用证明。本步新增稳定接口 `V293_OSInit_four_calls`，实际执行：

`OS_InitMisc → OS_InitRdyList → OS_InitTCBList → OS_InitEventList`

四个调用共用同一个P和caller。事件表的32个旧字节及旧空闲链头作为frame穿过前三次调用；取得实际返回内存Mtcb后，再从它的有限块上界构造四个fresh、互异、避开返回资源的局部块，调用事件初始化。**入口没有假设Mtcb、事件局部块或其freshness，也没有假设事件函数的结果。**

源码重新物化、预处理及Clang AST检查，94个配置后函数身份与锁定清单全部一致。`source-connection.json`核对OSInit顺序及四个函数的既有准确身份。Coq把前三个相邻C语句分组为一个sseq，再接事件调用；没有改变语句或调用顺序。字面AST在独立probe核对。仍是手工前端，不是已验证C转换。

## 跟着内存流理解

| 时点 | 执行／资源变化 | 不能偷用的假设 |
| --- | --- | --- |
| M | Misc、ready、TCB、事件旧存储及frame可写 | 不能预置初始化结果 |
| Mmisc | 真实十项Misc清零；事件存储原样保留 | 不能沿用M的新鲜性到以后 |
| Mrdy | 真实ready循环和返回 | ready局部释放只属于这个时点 |
| Mtcb | 两次清零、TCB建链、链头及返回完成 | 事件局部fresh必须从实际Mtcb构造 |
| 事件调用内 | 分配四局部，清零32字节，原生循环建链，写尾NULL和空闲头 | 不用结果列表替代实际语句 |
| Mf | 事件四局部共12字节释放；caller恢复；全部全局结果及frame仍可写 | 不声称更早的ready／TCB局部块在Mf仍缺失，后续可复用 |

独立 `audit/probes/V293InitFourCallsProbe.v` 不导入其他审计probe。它构造真正有限的非零／Vundef入口：TCB旧字节、全255优先级表和事件表、非空旧链头、非零Misc／ready，以及同名变量41的非空caller（块110，值7）。具体P含本片段所用五个函数：四个初始化函数及真实MemClr；不冒充完整94函数程序已实例化。

`FourConcreteExecution` 在**同一Mf**返回完整全局资源的可写所有权，并证明76项选择性读回：

- 前缀49项：13个TCB Next槽、2个链头、13个优先级NULL槽、7个ready单元、10个Misc单元、4个frame单元；
- 事件27项：2个Type、2个Ptr、1个空闲链头和22个其余清零字节。

`FourChecksValid`、`FourChecksInFinal` 都已独立闭合，读回定理没有开放的type/val匹配前提。caller同名变量仍为7；末尾事件指针为NULL，空闲链为 `Tbl[0] → Tbl[1] → NULL`。

## 单因素消融：只移除第四次调用

`ablation-plan.json` 在执行前冻结。保留相同P、有限入口、配置、三个前缀调用、frame及证明接口，只删除事件调用；`FourWithoutEventCall` 证明实际三调用执行后的可观察结果：

| 观察项 | 四调用 | 删除第四调用 |
| --- | --- | --- |
| 事件首字节／Type | 0 | 255 |
| 事件空闲头 | 指向事件表首项192:0 | 仍为旧指针213:0 |
| ready组 | 0 | 0 |
| frame保护字 | 123 | 123 |

这是机器检查的存在性执行端点比较，不是C运行时测量；它隔离的是**整个事件调用**，不授予其内部清零、Type赋值、链表等每个机制的独立消融信用，也不证明所有执行safety。

另有四项前瞻最终接口负控：错误事件第一链接、错误事件空闲头、丢失ready清零、损坏frame。只替换一个结论，fixture、生产源码、全部目标proof body和其他结论不变；正例先通过，负例必须在指定读回证明行拒绝。这些负控与上述真正的调用删除消融分别记录，不混用信用。

## 检查及剩余工作

证据目录 `audit/logs/stage51-init-four-calls/`。最终事实以 `final-report.json` 和 `final-evidence-manifest.json` 为准。201源正式构建复用995旧产物，不是全仓source-only冷构建；打印框架及初始化信任根并运行coqchk。旧失败日志、首次probe导入错误及后续证明错误均保留；不修改旧测试或冻结证据造绿。正式六门仍为 `[94,1,1,1,1,0]`。

这只是BeginHook之后的四调用片段。OSInit还包含Flag／Mem／Q／Idle／Stat初始化，两个port hook目前只有声明。完整OSInit／OSStart、运行Inv、task／ISR、local Hoare和全执行safety、源码级GOOD_OS及同程序K1–K4仍未完成。阶段一完成后才按老师附件推进uCOS3；本步未启动uCOS3，未提交／推送Git。
