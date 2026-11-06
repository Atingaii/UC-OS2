# 第72步：创建函数释放自己的局部对象，真实返回上层调用者

## 这一步解决什么

第71步已经真实计算 `return err` 的结果，但还停在 `kret`，没有返回上层。本步沿同一条条件轨迹继续执行框架的 `sretv_step → sfree_step → sfreeend_step`，不另造中间内存或用常量返回绕过源表达式。

稳定接口：`certiucos/v293/proofs/V293TaskCreateReturn.v` 中的 `V293_OSTaskCreateExt_success_return_under_hooks`。

它从未分配的创建函数 **body 入口**出发，在三个真实 Hook 返回契约成立、`OSRunning=0` 等原有条件下：

1. 复用真实前缀、栈 Hook 返回/psp 写入、TCB 完整成功调用、err 赋值和源码成功后缀。
2. 从实际到达的 `Mf` 所有权导出每个创建局部对象可写，不把中间 `Writable Mf` 当成新前提。
3. 实际释放完整 `getaddr le`，恢复上层调用者环境及其 continuation，产生返回值 0。
4. 在同一个返回后 `Mr` 中，保留已发布的 TCB、全局及调用者 frame；TCB 调用早先释放的9对象29字节仍为 None。
5. 创建自身12对象38字节全部为 None，释放块以外的任意地址与实际 `Mf` 相同。

## 两层生命周期

| 对象 | 数量/模型字节 | 返回后状态 |
| --- | --- | --- |
| OS_TCBInit 参数和局部 | 9 / 29 | 上一步已释放，本步证明仍已释放 |
| OSTaskCreateExt 参数和局部 | 12 / 38 | 本步真实释放 |
| 已发布 TCB 实体 | 不计入上述局部 | 保留，不是可释放的栈对象 |
| 全局/上层调用者 frame | literal结果共31项typed读取 | 同一Mr保留 |

新 Clang AST 核对源码确有9参数、3局部：`psp`、`err`、`cpu_sr`。精确模型布局见 `logs/stage72-task-create-return/source-layout.json`。这里的38字节是框架类型长度之和，不是栈帧大小、ABI、对齐或机器码证明。task仍沿用ADR0007的uint32 selector；ADR0004静态符号和ADR0005临界宏归一化不变。

## 检查与证据

- 新 materialize 固定修复源码，94个函数身份全部与冻结清单相同；真实后缀的 `return err`、运行态条件及未执行错误回滚分支不变。
- 独立字面内存证明 p0/p12 的入口所有权可满足；完整条件输出实例为 p12、running0，读回31项。读回列表复用生产结果公式，**不是独立 oracle**。
- 上层 caller 示例绑定变量777到块601，其中值77仍可读；创建12项确认为38字节。
- 正控先编译，随后四项合法类型终点修改分别检查错误返回值、错误恢复环境、错误frame值、错误创建局部释放字节；证明体完全相同。
- 事先固定的单因素实验只改变实际返回值 continuation 是否包含 `kcall`：相同P/GE/LE/M/值，有调用者时真实释放并恢复，无调用者时无 `cstep` 下一步（不涵盖中断）。**仅授返回派发信用**，不授body/Hook/分配信用。
- 235活动源增量构建复用1170旧产物，非cold；60个根的假设输出和 `coqchk`；新增5测试与完整回归均在本步目录留证。完整回归仍395失败1错误，旧396诊断不删除、不重新分类，默认audit仍退出2。
- 精确成功版本见 `accepted-versions.json`；失败版本、日志及一次探索性 `Abort` 调试记录全部保留，后者不作为生产证明或可信根。
- 最后一次Coq检查后精确恢复 `.lia.cache` / `.Makefile.coq.d` 原始字节。只按预先逐项核对的清单清理本次scratch、source materialization及probe一次性产物；保留1175个可复用生产产物和全部证据。

最终数字、身份和状态以 `logs/stage72-task-create-return/final-report.json`、manifest及独立复核为准。

## 没有解决什么

**创建入口实际参数/局部分配尚未证明。** 完整 `getaddr` 布局、唯一块和幸存块分离仍是显式前提；不能把 body 入口到返回称为完整 `sfexec` 调用证明。

三个真实 Hook 返回契约未兑现。`OSTaskStkInit`、`OSTCBInitHook`、`OSTaskCreateHook`、`OSInitHookBegin`、`OSInitHookEnd` 五端口实现仍缺；入口内存可满足不意味着这些契约已经可满足。缺 Stack Hook 的程序仍能真实到达该入口后卡住。

本步只接 running0 成功路径；running1 的调度器调用/返回、错误路径执行、OSInit 七调用的连续实际内存仍未接通。仍为存在性、无交错的 `V293_local_steps` 条件轨迹，不是 local Hoare、全执行 safety 或 GOOD_OS。

六门仍为 `94 / 1 / 1 / 1 / 1 / 0`，同程序 K1–K4 与源码级 GOOD_OS 开放。uCOS3 按老师要求等待阶段一全部完成；目标保持 active，未提交/推送。

## 下一步

优先证明真实创建 `sfexec` 的9参数/3局部分配、绑定与该 body 接口连续连接，不能另假设已分配中间状态。随后接真实端口、调度和OSInit七调用；每一步仅提升实际闭合的边界。
