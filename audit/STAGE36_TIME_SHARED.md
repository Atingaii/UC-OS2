# 第36步：OSTimeGet 从共享不变式借出时钟再归还

## 目标与旧缺口

目标仍为固定 V2.93.01 的源码级 `GOOD_OS` 与同程序 K1–K4；完成阶段一后才开始老师要求的 uCOS3。本步没有改变终点。

第35步已经连接两个真实归一化时间接口函数体，但时钟字节由调用者独占，临界区获得的 Inv 仅原样穿过赋值。本步不再把这一点当作共享时间验证。

## 实际新增

生产文件 `certiucos/v293/proofs/V293TimeShared.v`：

- `V293_time_shared_core` 将真实四字节时钟与 `ostmid` 的抽象时间绑定到**同一个** `n`。保留既有 CurTid、任务表和事件表，不另建一个与内核无关的空不变式。
- 证明该非空核心的 `GoodInvAsrt`、`precise`、`inv_isr_prop`，构造真正框架 `Inv`；第0项为该核心，其余为空项。不是假设一个 open／close oracle。
- 全局名称绑定仍属于调用者；`A_notin_lenv` 是局部环境事实，框架不允许把它放入 `GoodInvAsrt`。时钟**字节**才移入 IRQ 不变式。
- 稳定接口 `V293_OSTimeGet_shared_body`：保存单元清零→`encrit1_rule`→打开取得的真实 `invlth_isr`→从拥有的时钟字节读取并赋值→重建同一个不变式→`excrit1_rule`→`rete_rule` 返回局部快照。
- 入口没有时钟字节、预定时钟值、成功 load／store 或执行 oracle；返回规格只说存在本次读到的 `clock`，不声称它仍等于退出后的共享时间。
- `V293_time_shared_clock_agreement` 显式连接抽象时间查找与同一内存的真实32位 load。

沿用第35步实际 `V293_TimeGet_body`，未换 AST 或删临界区。固定源码为 `os_time.c:237–250`，整文件 SHA256 `a53a16a53e8d9cf1f508e97914d7cc91ea33019d8dfc3d6bc60741005bebb346`；正式 gate 重新运行既有精确配置后源码映射脚本，不改旧证据。这仍是手工映射与 ADR0005 宏归一化，不是经验证的 C 前端或原端口硬件 token 仿真。

## 独立非空实例

`audit/probes/V293TimeSharedProbe.v` 独立指定：全局时钟块80、ticks块81、保存单元块82、当前任务指针块90、任务91；局部入口两个单元均为 `Vundef`；抽象状态真正含四个键。

不仅分别证明调用者与共享核心可满足，还证明 `SharedJointEntry`：在**同一个字面完整内存**上同时持有两部分。两份 CurTid 读权限来自同一个可写当前指针的真实分裂，不是假定两堆可兼容。`SharedCallerLacksClock` 检查调用者内存中块80的任何字节都不存在；共享核心对任意32位时间 `n` 满足物理／抽象读回一致。

这些是入口可满足性与推导，不是 OS 初始化可达性，也不是新的真实执行轨迹。

## 前瞻单因素负控

先冻结 `protocol.json`，再实现和运行。两项保留所有 Proof 正文及原 getter AST：

| 仅改变的因素 | 实际拒绝点 | 不能因此宣称 |
| --- | --- | --- |
| shared-copy 的局部结果固定为1，而不是读到的值 | gate01，第187行，归还／重组后的 ownership entailment 无法闭合，下一 bullet 报错 | 不证明错误返回、IRQ或上层 API 均已被各自验证 |
| 不变式物理字节固定为1，而抽象见证仍为n | gate01，第173行，打开核心到赋值输入的 ownership entailment 无法闭合，下一 bullet 报错 | 尚未到达 copy／退出／返回，不给予下游信用 |

错误日志为未闭合证明目标后的 `Current bullet ... is not finished`，不是缺导入、旧 `.vo` 不一致或修改 AST 的语法错误。只计实际到达的连接拒绝，不将早拒解释为所有后续机制有效。

## 范围与尚未完成

本稳定接口只处理 **IE=true 且所有 ISR 活动标志清零的任务入口**；这使本步能确实取得第0项共享核心。IE=false／嵌套进入需要来自外层的资源契约，不能无资源读取，尚未添加。

**尚未证明扩展 Inv 的 `GoodI`；不能把旧 `V293_shared_good` 套用到新 Inv。** 因而这只是共享资源版 InfRules 推导，不是所有 ISR 交错下的整核 safety。Setter 还需要真实写入与抽象 `ostmid` 更新的同步步骤，不能只改断言中的时间值。完整 API 调用／局部分配释放、CPU hook、初始化、TCB／位图／事件共享关系、GOOD_OS 与 K1–K4 均未闭合；uCOS3 未启动。

默认 audit 仍失败，覆盖六门不晋级；旧测试与证据不重绑。没有全仓 source-only clean build，也没有 Git 提交／推送。验证、测试诊断精确差分和清理结果见下方收尾记录及 `audit/logs/stage36-time-shared/final-report.json`。

## 本轮实际收尾结果

正式 gate01 六条命令退出码 `0／0／0／1／1／0`，依次为新鲜 C 检查、生产、probe、两项预期拒绝、独立 coqchk。生产3根／独立6根只含既有 classic、functional_extensionality_dep 或闭合，无新增公理。新增9测试清理前后均通过。

全量1081测试实际372失败、1错误：旧371项诊断全部保留，仅新增 stage35 的冻结项目输入身份／精确 append 两项失败；未修改旧测试或历史证据。默认 audit 仍 exit2，六门 `94／1／1／1／1／0` 不晋级。

基线176活动源／880既有依赖逐一无变化；新增后177源＝74目标＋103框架／tactics，保留5个新生产产物。旧文件仅4个已声明路径发生追加／前插，缺失0，Git HEAD未变。第34步121项与第35步150项冻结 manifest 均无漂移。

逐项登记并在首次 unlink 前全量重核后，清理382项（352软链接、30实文件975096字节）及45目录：仅本步两项负控工作树、新鲜 C 的仓库外物化工作树及probe5产物。未删除任何基线文件，保留源码、全部成功／失败证据、旧缓存与可复用依赖。清理后新9测试仍通过，全量诊断 multiset 不变。未提交／推送；不是全仓 source-only 构建。目标保持 active，下一步连接扩展 GoodI 与 setter 抽象时间更新。
