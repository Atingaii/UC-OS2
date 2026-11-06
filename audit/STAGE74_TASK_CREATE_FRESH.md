# 第74步：构造创建调用的新块，避开有限幸存集合

## 1. 本次真正消除了什么

前一轮完整调用接口要求输入12个块、互异、fresh和最终幸存对象的块分离。本步新增 `certiucos/v293/proofs/V293TaskCreateFresh.v`，不改变旧源码、模型、证明、测试和冻结证据。

| 稳定接口 | 输入 | 机器检查结论 |
| --- | --- | --- |
| `V293_create_fresh_twelve_avoiding` | 任意实际M、有限cell列表 | 存在12块，互异、fresh，避开全部cell块号 |
| `V293_create_fresh_call_prologue` | 精确函数映射、9实参类型有效、caller原所有权 | 自动选块后真实sfexec分配/写入，得到12对象38字节与原frame |
| `V293_OSTaskCreateExt_fresh_success_call_under_hooks` | 原全局/TCB前提、uniform真实Hook家族、初始所有权 | 自动选块，沿原调用链返回0、释放创建12对象及TCB调用9对象，恢复caller和同一Mr幸存数据 |

选择依据是 `HalfPermMap.bounded M` 与 `V293_cells_upper live`，起点取二者上界的最大值；后11块连续递增。没有新增allocator、没有修改C或操作语义。完整调用仍只覆盖OSRunning=0成功路径，从已求值实参的sfexec开始。

## 2. 不能把“fresh”当作“避开逻辑对象”

有限rawcell列表允许Tvoid；其大小为0，所有权可由空内存满足。块1上存在这样的逻辑cell，与实际空内存中的fresh块1不矛盾。

`audit/probes/V293TaskCreateFreshAnchor.v` 事先按protocol冻结单因素设计：保持空内存、12连续候选、块1零大小cell、内存上界和全部参数不变，只开/关选择起点对幸存上界的考虑。两组均互异且fresh；关闭时与块1重叠，打开时不重叠。`AnchorZeroOwned`额外证明该反例的rawcell前提确实可满足。

只为块选择/分离机制授消融信用，不为Hook、参数分配、整条调用或GOOD_OS授信用。具体结果见 `survivor-ablation-result.json`。

## 3. uniform Hook家族不是免费前提

三个真实契约指栈初始化返回、TCB初始化Hook返回、任务创建Hook返回。新完整接口要求：对所有合法新布局，三契约均成立，再由块选择实例化。相比前一轮针对固定布局的契约，这是更强的前提；因此本步不是旧完整定理的无条件强化，更不是Hook已经实现的证据。

固定目标仍缺五个端口函数定义：OSTaskStkInit、OSTCBInitHook、OSTaskCreateHook、OSInitHookBegin、OSInitHookEnd。无noop，无新增Axiom/Admitted/Parameter。完整成功条件定理未提供uniform家族的实现见证；仅入口分配不依赖Hook。

## 4. 独立实例与可复查证据

- `audit/probes/V293TaskCreateFreshProbe.v` 独立构造字面CallMemory，不导入旧probe。`CallLiteralEntry`证明初始所有权可满足；`FreshLiteralPrologue`自动构造12块并真实执行入口，同时避开零字节cell。
- `FreshConditionalExecution`固定p12与真实全局映射，保留uniform Hook家族作为明确前提，不伪造可运行完整程序。31项typed读取由同一rawcells/load关系推出，属于共享编码一致性，不是独立C oracle。
- `positive01`必须通过；三个负控只改返回值、返回环境或释放后字节终点，保持证明体完全相同，须在apply处失败。只证明声明端点受约束，不代表执行所有错误路径。
- 重新提取并逐项复核固定配置94个函数身份、源码后缀和参数/局部声明；手工前端仍沿用ADR0004/0005/0007，不证明ABI或编译器正确性。
- 238活动源（135目标、103框架）增量构建，不是cold；1185旧产物必须字节不变，1190生产产物保留。Print Assumptions的60根与coqchk均须真实完成，最终数字见final-report。
- 所有失败编译的日志和源快照保留；最终接受版本见accepted-versions。最早anchor缺生产vo、缺bool类型、缺直接导入和nil类型的问题均不算负控成功。

## 5. 回归与审查边界

本步新增4项测试，旧测试原文不动。第73步 `test_preserves_baseline_and_exact_function_connection` 使用封闭世界精确列表，新增第238源将使它失效；不为制造全绿而改旧断言、删失败、改classification或重写旧报告。最终全量结果与相对第73步的新增/删除诊断逐项记录在regression-comparison；构建通过不等于测试全绿，默认audit原失败也保留。

六门保持 `94/1/1/1/1/0`。本步不是localHoare、所有执行safety、同程序K1–K4回归或源码级GOOD_OS。OSRunning=1的实际调度、错误分支执行、OSInit七调用同一实际内存及真实端口义务仍未闭合。uCOS3未启动，目标active，未提交/推送。

清理前先列出并复核全部一次性scratch/sourcework/probe编译产物的身份，只删除本步一次性文件；保留旧缓存、用户资料、生产可复用产物、所有成功/失败证据。全Coq结束后精确恢复两份原缓存。审计详情：`audit/logs/stage74-task-create-fresh/`。

## 6. 下一步

先修正独立测试对活动源集合的生命周期设计（另立协议与测试，不改本步冻结证据），再沿真实端口/初始化连续内存向上连接；不得借新增条件包装定理宣布GOOD_OS完成。
