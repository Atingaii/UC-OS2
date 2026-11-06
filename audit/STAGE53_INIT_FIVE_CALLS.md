# 第53步：把 Flag 接到前四个初始化调用的真实返回内存

## 本步实际完成什么

稳定接口 `V293_OSInit_five_calls` 顺序执行：

`OS_InitMisc → OS_InitRdyList → OS_InitTCBList → OS_InitEventList → OS_FlagInit`

这些是固定配置后 `OSInit` 中 BeginHook 后相邻的五次调用。重新物化两项授权修复，核对全部94函数身份、准确调用顺序及前五个函数的既有源码证据；不修改 C、配置或授权范围。`OSInitHookBegin/End` 仍只有声明，不能视为已执行实现。

## 如何连接，而不是只把两个定理并排放置

1. Flag 表的60个任意旧字节及旧链头作为 frame 穿过前四次实际调用。
2. 从前四调用真正返回的 `Mevent` 构造四个新鲜、互异局部块，排除返回资源落入将释放的块。入口不假设中间内存、新鲜性或已分配 callee 局部。
3. 同一个程序 `P` 中执行完整 Flag 调用：真实清零、四次循环建链、尾 NULL、空闲链头及四局部的分配／释放。
4. 同一个最终 `Mf` 保有全部 Flag、Event、TCB、Ready、Misc 和用户 frame 的可写所有权，并恢复原 caller。

Flag 的布局沿用第52步已核对的5×12字节：Type 偏移0、WaitList 偏移4、16位 Flags 偏移8。新模型只对相邻调用作手工语句分组，不声称有已验证 C 前端或 ABI 证明。

## 独立入口与观察

`audit/probes/V293InitFiveCallsProbe.v` 不导入其他 audit probe。它独立构造有限内存：TCB 未定义字节、优先级／Event／Flag 全255、非空旧链头、非零 Ready／Misc，及同名 caller 变量 `41 → 110`（值7）。具体 fixture 是六函数程序，不是完整94函数程序。

在同一 `Mf` 证明122项 load：既有76项，加 Flag 的10个字段、35个其余零字节及1个链头。Flag 四局部的12字节在最终内存释放。前面 Ready／TCB／Event 的局部块可能被后续分配复用，因此不声称它们在最终内存仍全部缺失。

## 前瞻消融与负控，分别记账

冻结计划后，仅删第五次 Flag 调用：程序表、初始内存、环境、caller、前四调用及 frame 都不变，实际执行四调用前缀。Flag Type 字节仍255、链头仍214:0；五调用基线分别为0和194:0。Event Type、Ready 和保护字123不变。这只证明整次调用对于这些结果的作用，不给清零、建链、分配等内部机制分别授予消融信用。

另四项最终接口负控，只改一个结论，保持证明体不变：首链接错误、空闲头错误、Ready 丢零、frame 被破坏。先检查正控，再要求四个负控各在自己的读回证明行被拒绝；它们不是机制消融。

## 验证与边界

正式构建205个活动源，复用1015个旧产物，非 source-only 冷构建。85根 `Print Assumptions` 与四模块 `coqchk`、新增8测试、全仓回归、缓存恢复和清理的最终结果以 `audit/logs/stage53-init-five-calls/final-report.json` 为准；未生成最终报告时不得当作本步验收完成。原始失败日志和候选快照保留。

本步仍是**存在性、无交错执行片段**，不是 local Hoare、所有执行 safety、完整 OSInit／OSStart 或整核 GOOD_OS；六门不晋级。尚余 Mem、Q、Idle、Stat 调用及两个端口 hook，随后还要完成任务／ISR、运行不变式与同程序 K1–K4。完成 uC/OS-II 后才开始 uCOS3；没有提交或推送 Git。
