# 第328步：同一联合资源跨过原全局任务切换

## 从哪里继续

第327步从原始客户端 `OSTimeDly(3)` 出发，在真实阻塞、调度分配/初始化、helper调用/释放/返回、目标发布及比较自增后，得到同一末端堆上的 `SWINVt ** frame`，但停在 switch 前。第325步虽有切换可达性，却没有这个联合所有权。本步不重跑另一条轨迹来拼接资源。

固定内核仍为 V2.93.01 的锁定提交和两类授权修复。`source.py` 重建并预处理三项函数，保留真实源码片段及哈希。未修改 C、旧证明、旧测试或冻结证据。

## 新的稳定接口

`certiucos/v293/proofs/V293ReadyOwnedGlobalSwitch.v`：

- `V293_owned_switch_active_view`：拆开已有 `SWINVt`，证明 flags 只拥有空资源，再通过 `GoodInvAsrt R` 和完整就绪资源的良构性，改变局部环境、IE及临界栈。中断栈保持相同，不承诺任意辅助状态敏感 frame 都可搬运。
- `V293_owned_global_switch`：复用已有 `V293_ready_switch_step`，由当前指针所有权构造实际 store 和原框架 `lpstep`；同时检查旧、新任务环境及辅助状态在原 maps 中的绑定。调用者不提供成功 store 或最终堆。输出同一新堆上的物理 current、更新后的抽象 `curtid`、完整就绪资源与全部 frame，以及指针4字节以外的字节保持。

没有新增另一套 switch 语义，也没有修改原 AST 或原语规则。使用既有规范化C片段与框架switch抽象；源码重放和哈希只校验身份，不等于新完成了C到AST的翻译正确性证明。

## 原始客户端的非空实例

`audit/probes/V293ReadyOwnedGlobalSwitchProbe.v` 的 `DGglobal_switch` 对所有32位计数器 `c` 和两种初始 IE 无前提构造：

1. 原 `DXrun` 到同一个 `Mcut`，并持有原 `DOpost`；
2. 原 `lpstep` 从这个 `Mcut` 切换到 `Mf`；
3. 原全局客户端执行闭包到 `DXfinal`；
4. `DGpost` 在这个 `Mf` 上联合拥有：当前任务为 `OwnershipWaiting` 的完整共享字段、全部TCB记录、位图与优先级表，以及原 frame。

旧任务已阻塞，switch 把其代码改为 `SKIP` 并保留原 continuation；新活动任务为 `OwnershipWaiting`，其环境为 `DCle`。`DGmatched_high` 连接同一阻塞后抽象任务表的原 `hpstep`，不是任意抽象调度器。

`DGobserved` 从联合资源读取高优先级6、缓存4、计数器c+1、目标指针、guard、canary99及局部值；两个 CPU 槽仍为0且均有4字节写权限。`DGboth_IE` 覆盖两种初始IE，`DGwrap` 覆盖32位回绕，`DGdistinct_heaps` 保留客户端与OS堆同编号参数块分别99和3。

## 切换后辅助状态的真实边界

实际切换不改 `les` 和 `au` maps，但活动任务变了。被选任务绑定是 `(true,nil,nil)`，即 **IE=true**，不是旧任务的 `(false,nil,[enabled])`。

所以 `DGpost` 输出 `V293_ready_full ** frame`，而不是继续声称活动视图满足要求 IE=false 的 `SWINVt`。`DGactive_not_disabled` 对任意堆证明后者在启用中断的活动状态不成立。这不是资源丢失，而是必须丢弃已不适用的辅助状态观察。

## 事前单因素消融

协议在证明前固定，见 `protocol.json` 和 `protocol.sha256`。只中和末端当前TCB指针提交，其他前缀程序、执行、记录/位图/表、helper释放边界、计数器自增、CPU资源和canary不变。

`DGpointer_commit_ablation` 同时展示：

- 原前缀 `Mcut` 仍拥有 `DOpost`，current物理读取是旧任务；
- 正例实际 store 到 `Mf`，满足新任务 `DGpost`；
- 去掉这一次 store 的片段仍停在 `Mcut`，不能满足同一个 `DGpost`。即使抽象curtid、活动环境和IE按正例取值，`DGcurrent` 从所有权导出的物理读取也与旧指针冲突；
- 两侧计数器同为c+1、canary同为99，CPU均可写，helper释放见证保留在原 `Mh`。

这是最后指针提交片段的负例，**不是突变程序的完整全局执行**；不宣称能在原 `lpstep` 中“不写指针却成功切换”。辅助状态负例单独检验，不能由指针负例顺带推断。

## 验证与当前边界

| 检查 | 实测结果 |
| --- | --- |
| P/Q稳定编译 | 各两次，均exit=0，输入源码身份不变 |
| 递归内核复核 | 12根，exit=0，881个Coq输入身份不变；仅既有classic和funext_dep |
| 构建／项目审计 | 均exit=0；active 404，framework/tactics 103 |
| 新增测试 | 8/8，两次通过，最终核对再执行一次 |
| 全量回归 | 两次均2876项、439失败、1错误；旧失败/错误ID与顺序完全保持，无新增 |
| make audit | exit=2，仍为旧stale function evidence input identity |
| git diff --check | exit=2，仍为旧inferules.v六处空白，输出与前步逐字节相同 |
| 历史保持 | 原45672文件除允许的文档前缀、项目尾追加及生成依赖清单外不变；原306份pyc不变 |
| 清理 | 逐项审查后删除6个Trust临时文件及4份已恢复缓存备份；失败日志、快照、可复用Coq对象均保留 |

本步局部证明与无新增回归门禁通过，但全量测试和总体审计并未通过。`verification.json` 分别记录这些状态。4份原缓存字节均恢复，并使生成Makefile时间早于新项目清单，保证下一次构建重新生成而不漏编。

稳定 P/Q 各两次编译、逐根假设检查、递归 `coqchk`、构建、新测试和全量回归的实际结果在本步日志与 `verification.json`，失败快照照原样保留。历史439失败及1错误的基线不改写、不豁免，不能把“没有新增失败”等同于全量通过。旧函数证据身份与空白审计问题仍需如实报告。

**本步不是完整 API，不是全局记录不变量，不是全局 ProgSim，不是 GOOD_OS。** 它是常量参数、有限无交错轨迹到一次真实切换后的联合资源。helper只在 `Mh` 返回边界证明释放，不升级为最终整块fresh。优先级缓存仍为4，原switch只提交current指针，不虚构缓存同步。

后续仍需把活动／恢复契约接进真正的函数及全局模拟，处理旧任务恢复、调度退出及return；统一WFInt、初始化、同程序K1–K4和最终 GOOD_OS 仍开放。uCOS3必须在第一阶段真正结束后开展，总目标保持 active。没有提交或推送。
