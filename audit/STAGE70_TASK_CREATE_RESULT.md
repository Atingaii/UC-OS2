# 第70步：把TCB返回值真实写入调用者err

## 实际增量

稳定接口为 `certiucos/v293/proofs/V293TaskCreateResult.v` 中的 `V293_OSTaskCreateExt_result_assigned_under_hooks`。

第69步停在 `OS_TCBInit` 已返回0、caller尚待执行 `kassignr err Tint8` 的状态；本步沿用完全相同的三个真实Hook返回契约，接上调用者的地址求值与实际字节store。终点为 `sskip None`，后续仍待执行参数化的 `rest`，没有把它假装成精确源代码后缀。

同一最终 `Mf` 同时满足：

- `err=0`，`psp` 仍等于栈Hook返回值；
- TCB初始化／发布结果、唯一的优先级槽所有权、caller的其它参数及外部frame保留；
- TCB调用的9对象29字节全部保持已释放；
- IE恢复原值，si／ci不变；fresh9仍只相对前缀实际到达的 `Mbridge`。

没有更改旧生产代码、框架、策略、C、配置或旧证据；没有新增公理或占位证明。

## 为什么不能只证明err变成0

若为接一条赋值而丢掉已释放局部对象的结论，上层以后可能无法证明资源安全。因此辅助引理 `V293_create_err_assign_preserves_release` 同时保留真实store、所有权与释放结论：

1. 从可写err单元构造实际store和执行轨迹；
2. 成功store意味着原err字节确实存在且可写；
3. 每个被释放对象的0偏移不存在，因此其块不可能等于err块；这个不别名事实是推导结果，不是新增调用者假设；
4. 使用store对其它块不变的引理，将所有已释放字节的 `None` 结论传到同一个最终 `Mf`。

主定理从第69步真实返回内存 `Mr` 开始赋值，不在另造的有利内存中赋值后拼贴结果。

## 独立验证与消融边界

`audit/probes/V293TaskCreateResultProbe.v` 的字面fixture不导入其它audit probe。两份body入口与两份假设返回锚点可满足；p0／p12实际到缺StackHook并证明无下一步。完整输出仍只有一个p12、旧任务链头NULL、非NULL栈返回的**条件实例**，不是固定缺Hook程序的成功运行。

同一输出内存可typed读取42项。该集合复用生产结果定义，所以不是独立完整语义oracle。额外正控固定字面err0、caller77、发布TCB指针，并检查原释放结论。四个负控只改结论、保持证明体原样：错误err9、错误caller0、错误保留地址指针、错误释放后字节存在；正控先通过，再要求负控在修改的终点失败。

前瞻权限消融只把独立返回锚点中err字节的写权限由true改为false：原始字节9相同，其余所有地址保持相同，两侧均可读err9和caller77；对同一地址、类型和返回值0，真实store在可写侧成功且读回0／77，在只读侧返回None。**只授真实store决策的信用，不授整段赋值轨迹、三个Hook或全主路径的独立消融信用。** 不声称假设返回锚点在固定程序中已成功到达。

## 源码身份与失败记录

证据位于 `audit/logs/stage70-task-create-result/`。先冻结protocol，再重新materialize授权修复源，核对Clang预处理／AST的全部94个配置后函数身份，并核对 `err = OS_TCBInit(prio, psp, pbos, id, stk_size, pext, opt)` 的LHS、参数顺序和位置。

生产proof01失败于未指定Tint8导致replacement类型无法推导；proof02失败于Freed中tp未显式实例化；proof03／04为列表结合顺序归一化问题；proof05通过。probe01、positive01通过。消融ablation01漏写内存字节构造器 `Byte` 而类型错误；原快照和原计划保留，修正同一实验的构造器后运行ablation02，但全内存 `vm_compute` 在134.5秒、约5GB驻留内存时仍未完成，主动中断并保留退出码-2。随后保持完全相同的42单元输入、因素和结论，改用已检查的所有权／字节引理；ablation03／04缺少正确定义模块的显式导入，ablation05／06需要显式自然数9／0实例化。每次修正前均冻结新计划并保留失败快照，最终 `ablation-plan07.json`／ablation07通过，没有缩减fixture或改变验收结论。负控原始计划中的同类未编译字节构造器也保留为快照，修正为合法memval后冻结 `control-plan02.json`；不将类型错误当作负控通过。

232活动源增量构建复用1155旧产物，不是冷构建。信任、回归、缓存恢复、清理和最终身份以本步 `final-report.json`、`trust.json`、`regression-comparison.json`、`cleanup.json`、`final-evidence-manifest.json` 为准。失败尝试不删除、不覆写。

## 下一步学习：返回值与变量不是一回事

| 时刻 | callee返回值 | caller的err | TCB调用局部对象 | 尚未执行 |
| --- | --- | --- | --- | --- |
| 第69步终点 | 0 | 原值，fixture中为9 | 9对象29字节已释放 | caller赋值、创建后缀 |
| 第70步终点 | 已被赋值动作消费 | 0 | 同一Mf中仍全部释放 | `if (err == 0)`、运行态检查／调度、最终return |

接下来应从锁定源精确建模这段后缀，区分OSRunning为0和1；需要调度时保留真实 `OS_Sched` 义务，不能造noop。之后再接调用者分配／返回和OSInit七次创建的实际连续内存。

## 仍然开放的总目标

三个真实Hook契约没有实现证据。固定源仍缺 `OSTaskStkInit`、`OSTCBInitHook`、`OSTaskCreateHook`、`OSInitHookBegin`、`OSInitHookEnd` 五个端口实现。手工前端ADR0004／0005／0007及CPU_SR字节效果擦除边界不变；不是verified frontend或ABI证明。

本步仍是存在性、无交错轨迹，不是localHoare、全执行safety、完整任务创建、完整OSInit或GOOD_OS。六门94／1／1／1／1／0不提升；同程序K1–K4、七调用实际Mf和整核证明仍开放。最终目标保持active，只有完整GOOD_OS阶段一完成后才开始uCOS3；本步未提交／推送。
