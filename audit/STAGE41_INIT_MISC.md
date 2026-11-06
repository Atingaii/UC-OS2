# 第41步：从真实 OS_InitMisc 建立启动前的十个全局单元

## 对象与接口

固定 V2.93.01、固定配置、两类既有授权修复，源码身份仍为 `74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da`。实际 `os_core.c:1389–1418` 的 `OS_InitMisc` 定义哈希为 `e2244dd2db7d66ee7b16b24fb7c25617e4ca8e5d1e1bbe5110209f915acea280`，函数体哈希 `c46412d3e2adca015c1f5b24cfa1afc39456df56864665a2a2b82c210f7560f8`。重新物化、预处理及 Clang AST 检查全部94个配置后函数身份，再核对完整10次赋值的名称、类型、零常量与顺序。

| 顺序 | C 全局 | 固定配置类型 | 实际结果 |
| --- | --- | --- | --- |
| 1 | OSTime | unsigned int / Tint32 | 0 |
| 2 | OSIntNesting | unsigned char / Tint8 | 0 |
| 3 | OSLockNesting | unsigned char / Tint8 | 0 |
| 4 | OSTaskCtr | unsigned char / Tint8 | 0 |
| 5 | OSRunning | unsigned char / Tint8 | 0 |
| 6 | OSCtxSwCtr | unsigned int / Tint32 | 0 |
| 7 | OSIdleCtr | unsigned int / Tint32 | 0 |
| 8 | OSIdleCtrRun | unsigned int / Tint32 | 0 |
| 9 | OSIdleCtrMax | unsigned int / Tint32 | 0 |
| 10 | OSStatRdy | unsigned char / Tint8 | 0 |

`0uL` 是常量类型，不意味着左值 INT32U 是 unsigned long；以实际分析端口 typedef／Clang 类型为准。第一次检查器把二者混淆的失败、原检查器快照和后续修正均保留，不计正式通过。

新增代码 `certiucos/v293/code/V293OSInitMisc.v` 显式转换零到目标类型，并展开隐式 void 返回；手工前端，不是经验证的 C 编译前端。十次写入顺序未删除，附加空语句不产生存储效果。新增证明 `certiucos/v293/proofs/V293InitMisc.v` 暴露：

- `V293_OS_InitMisc_execution`：从十个可写原始单元及名称绑定，推导每次真实 store 存在，执行完整实际赋值序列，在同一 `Mf` 获得十个零值和原分离 frame。
- `V293_OS_InitMisc_call_return`：实际 `scall`→空参数／空局部分配→函数体→void return→空列表释放→恢复 caller。不是只有函数体 Hoare 结论。
- `V293_init_readback`：从上述最终资源读取实际内存；不运行同一个模型来生成期望结果。

初始资源接受任意原始值，包括 `Vundef`；不要求提前已经全为零。没有伪造当前任务，也没有假设运行期 `CurLINV`。frame 的前／后断言都在 callee 空局部环境求值，不把任意 caller 环境断言偷偷转移到 callee。

## 独立非空实例

`audit/probes/V293InitMiscProbe.v` 的入口包含非零值7／3／2／9／1／42／100，以及两个真正 `Vundef` 单元。证明全部物理／抽象资源可以同时满足，不是不可满足前提推出任意结论。独立字面 AST 写出全部10条赋值，而非复用生产递归生成器作为期望值。

最终从**同一个实际调用得到的 Mf** 字面读取全部10个零、额外块90的空指针和块99的123。块90只是独立 frame 中的空指针单元，**尚未把该单元绑定到真实 OSTCBCur 全局，也不是整个初始化状态可达**；gate 中 `null_current_preserved` 仅指这个启动前示例单元。保持空指针不等于已产生运行任务。

抽象时间槽入口故意为57，结束仍为57；物理 OSTime 变为0并不会自动建立物理／抽象时间一致的不变式。最终运行 Inv 需要在初始化组合时另行构造，而不是假装本函数执行了不存在的抽象 primitive。

## 前瞻单因素控制与边界

协议先于实现冻结于 `audit/logs/stage41-init-misc/protocol.json`：

1. 仅将最终 OSStatRdy 字面读取期望由0改为1，所有 Proof 和生产 AST 不变。应在最终所有权／读回连接处拒绝；只记后置条件连接检查，不记执行语义或下游机制信用。
2. 仅删除生产体 OSIdleCtrMax 那一项，独立字面 AST 及其证明完全不变。先正向编译最小字面消费者，再对可编译的缺项模型编译**相同消费者**；只记 AST 对应检查，不把更早生产证明类型不匹配当作后续语义验证。

旧源、旧失败、源码锁、C／端口／配置、既有框架、六门证据均不改写；新文件只登记当前工程。全部开发失败快照与日志保留。

## 尚未完成的连接

这是一段**无交错具体执行**及其局部资源构造：不是所有 ISR 交错安全；不证明调用之前的十个资源来自真实程序入口。`OSInit` 的其余就绪表、TCB／空闲任务／统计任务、对象池初始化及 CPU hook 仍须逐项连接。`OSStart` 建立当前任务与运行 Inv 仍开放，不能以 `OSTCBCur=NULL` 满足 `CurTid`。GOOD_OS、同程序 K1–K4、uCOS3均未完成，六门不晋级。

复用既有生产依赖，不声称全仓 source-only 干净构建。实际结果以本步正式检查、测试差分、清理清单及最终报告为准。

## 未通过的第一次正式检查

gate01 正向模型、执行证明、实例和错误结果控制完成，但漏赋值模型因删掉唯一使用处，无法推断未标注的 `idle_max` 类型。此失败**不符合**预定的 AST 拒绝位置，不计负控成功。保留 gate01 全部失败证据；给生产字段参数显式标注 `var`（不改变语义体），在新身份 gate02 重跑完整检查。没有删除失败，也没有降低原定检查标准。

## 实际收尾结果

正式 gate02 九命令退出码 `0／0／0／0／1／0／0／1／0`；生产代码／证明／独立实例 coqc 与独立 coqchk 三模块通过。生产2根／实例4根假设仅既有 classic／functional_extensionality_dep（字面 AST 无全局假设）。错误结果在第159行读回连接拒绝，漏项在第14行字面 AST 拒绝；均不授执行语义／下游信用。gate01 不符合预定位置的失败原样保留。

新增8测试清理前后全过；全量1122测试为376失败、1错误，此前377项诊断全部保留，无新增／删除，清理前后诊断 multiset 相同。scope／固定C／diff 检查0；默认audit仍exit2：stale function evidence input identity。正式六门仍94／1／1／1／1／0，未晋级。

旧181活动源／905生产依赖与既有缓存均未变；新增后183＝80目标＋103框架／tactics。基线仅4条声明的文档前插／追加和project追加路径改变，缺失0；HEAD不变，未提交／推送。此前五份冻结manifest逐项无漂移。

逐项清单确认类型、大小、hash／链接目标和目录成员，全部重查后首次unlink：删除1205项（1094软链接、111实文件／3164390字节）及152目录，仅两轮负控工作树、4个新鲜C临时树与probe5产物。基线删除0；源码、成功／失败证据、缓存、既有依赖及新增10个可复用生产产物保留。不是全仓 source-only 构建。GOOD_OS／K1–K4／uCOS3仍开放，总目标继续active。
