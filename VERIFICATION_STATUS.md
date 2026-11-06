<!-- remote-checkpoint-20261106-start -->
## 2026-11-06：保存当前工作到远程的检查点

当前是进行中快照，不是完成版本。第352步局部窗口证明已完成；第353步交错实验仍在源码副本准备阶段失败，尚无已复现反例。源码级 GOOD_OS 与同程序 K1–K4 未闭合，uCOS3 未开始。见[本次保存说明](audit/REMOTE_CHECKPOINT_20261106.md)；其中说明实际验证结果及未上传的本地证据范围。下方“未提交／推送”等文字保留各历史步骤当时的状态，当前提交／推送状态以 Git 为准。
<!-- remote-checkpoint-20261106-end -->

<!-- publication-window-results-start -->
两轮全量均3071项、450失败、1错误；旧失败／错误身份及顺序全部保留，新增失败0、新增错误0，增量门通过，全量与整体检查点仍未通过。新增7项两轮及清理后均通过；12根逐项信任门、递归coqchk、两轮重复编译及构建通过，允许假设仍仅原两项。逐项清理10个本步一次性文件；4份既有缓存bytes/mtime、306份pyc、可复用证明对象及所有失败快照保留。原审计身份过期和六处框架空白问题不变。真实发布窗口已闭合；旧forward关系正baseline成立，不夸大为所有不变量不可能。并发owner／全局强关系、hook实现、TaskSim、整核与uCOS3仍未完成；未提交／推送。
<!-- publication-window-results-end -->

<!-- publication-window-checkpoint-start -->
## 第352步：检验优先级表发布与就绪位发布之间的真实窗口

实际slot写入和退出临界区后、第二CPU hook调用前，真实新指针与旧bitmap在同一堆共存。旧map仍满足原forward ready关系（通用正baseline），但反向canonical拒绝新指针；标准插入新ready任务的map则被旧bitmap拒绝。字节级非空旧任务／真实RESERVED入口经初始化到首hook，再从独立首hook返回入口运行窗口，保留新旧记录、两row、group和sentinel。纯更新ready位后的正控制不算下游执行。

**不是内核Bug，也不证明所有抽象均不可行。** 第118–130步已有owner片段不重记；ADR0009并发owner／过渡态全局强关系仍未集成，CPU及栈hook、整函数TaskSim、OSInit、具体GOOD_OS与同程序K1–K4未完成。uCOS3未开始，总目标active。见[中文说明](audit/STAGE352_PUBLICATION_WINDOW.md)和[实测汇总](audit/logs/stage352-publication-window/verification.json)。旧断言／源码／测试／冻结证据不改，不登记full_target_linked；未提交／推送。
<!-- publication-window-checkpoint-end -->

<!-- creator-shared-return-results-start -->
两轮全量均3064项、450失败、1错误；旧失败／错误身份及顺序全部保留，新增失败0、新增错误0，增量门通过但全量与整体检查点仍未通过。新增7项两轮及清理后均通过；8根逐项信任门、递归coqchk、两轮重复编译及构建通过，允许假设仍仅原两项。逐项清理10个本步一次性文件；4份既有缓存bytes/mtime、306份pyc、可复用证明对象和全部失败快照保留。编译候选失败日志／快照全部保留；旧注册快照失败不豁免。旧函数审计身份过期和六处框架空白问题不变。运行期预留／psp赋值／实参求值已连接共享返回；一个栈hook、两个CPU hook、并发owner及整函数TaskSim、整核目标未完成；未提交／推送。
<!-- creator-shared-return-results-end -->

<!-- creator-shared-return-checkpoint-start -->
## 第351步：运行期创建前缀连接原强共享资源返回

从实际创建前缀的null槽入口，经真实预留写入、栈hook返回契约、psp赋值与七实参求值，到TCB初始化／发布／释放及err=0，保留同一返回堆上的原强共享资源。九个互异新鲜局部块在到达Mbridge后实际选择；任务入口和参数与实际栈调用一致。闭合单因素对照从独立栈返回现场只省略psp赋值，不授下游机制信用。

**仍需一个栈hook和两个原CPU hook契约；ADR0009并发owner未接通。** 仍是完整可写槽的条件组件，非整函数TaskSim、冷启动OSInit、具体GOOD_OS或同程序K1–K4。uCOS3未开始，总目标active，不登记full_target_linked。见[中文说明](audit/STAGE351_CREATOR_SHARED_RETURN.md)和[实测汇总](audit/logs/stage351-creator-shared-return/verification.json)。旧测试和冻结证据不改，新增失败不豁免；未提交／推送。
<!-- creator-shared-return-checkpoint-end -->

<!-- reserved-call-shared-results-start -->
两轮全量均3057项、450失败、1错误；旧失败／错误身份及顺序全部保留，新增失败0、新增错误0，增量门通过但全量与整体检查点仍未通过。新增7项两轮及清理后均通过；10根逐项信任门、递归coqchk、两轮重复编译及构建通过，允许假设仍仅原两项。逐项清理10个本步一次性文件；4份既有缓存bytes/mtime、306份pyc、可复用证明对象和全部失败快照保留。编译候选失败日志／快照全部保留；旧注册快照失败不豁免。旧函数审计身份过期和六处框架空白问题不变。物理预留槽局部返回接口已连接；两个CPU hook、并发owner及整个运行期调用者前缀、整核目标未完成；未提交／推送。
<!-- reserved-call-shared-results-end -->

<!-- reserved-call-shared-checkpoint-start -->
## 第350步：物理预留槽沿真实TCB发布恢复原强共享资源

入口持真实RESERVED指针与其余12槽hole；实际初始化、发布、返回后重组完整canonical表和原ready_payload，并保留同一Mr的物理资源到原抽象创建及err真实赋值。未把物理预留槽当null，未修改强谓词或固定源码。非空字面入口真实执行到首hook；同一堆上的独立首hook返回现场只省略发布写入时仍为RESERVED，实际执行则建立更新强表和新旧记录。

**仍需两个原CPU hook契约；完整运行期预留／栈hook／实参求值前缀及ADR0009并发owner未拼接。** 本接口从已求值sfexec且持完整可写槽开始，不替代全局ISR、整调用者TaskSim、OSInit、具体GOOD_OS或同程序K1–K4。uCOS3未开始，总目标active，不登记full_target_linked。见[中文说明](audit/STAGE350_RESERVED_CALL_SHARED.md)和[实测汇总](audit/logs/stage350-reserved-call-shared/verification.json)。旧测试与冻结证据不改，新增失败仍计入门；未提交／推送。
<!-- reserved-call-shared-checkpoint-end -->

<!-- call-result-frame-results-start -->
两轮全量均3050项、450失败、1错误；旧失败／错误身份及顺序全部保留，新增失败1、新增错误0，增量门失败但全量与整体检查点仍未通过。新增7项两轮及清理后均通过；10根逐项信任门、递归coqchk、两轮重复编译及构建通过，允许假设仍仅原两项。逐项清理10个本步一次性文件；4份既有缓存bytes/mtime、306份pyc、可复用证明对象和全部失败快照保留。编译候选的导入、解析和化简失败日志／快照全部保留；必要注册触发的旧快照失败不豁免。旧函数审计身份过期和六处框架空白问题不变。两个CPU hook、运行期预留槽连接、完整调用者模拟及整核目标未完成；未提交／推送。
<!-- call-result-frame-results-end -->

<!-- call-result-frame-checkpoint-start -->
## 第349步：保留调用者资源并执行TCB真实返回赋值

从真实sfexec入口、九局部分配和同一次连续TCB返回得到Mr，在原抽象创建步骤之后仍保留调用者物理frame，再实际执行err赋值得到Mf。闭合对照只省略赋值：同一非空共享就绪返回现场保持err=66，实际赋值后变0；不把独立返回fixture当完整调用可达性。

**仍需两个原CPU hook契约；null-slot入口不能直接连接真实运行期预留槽前缀。** 已用同堆不相容定理记录该接口缺口，不改源码、不削弱共享谓词。完整OSTaskCreateExt的TaskSim、OSInit、具体GOOD_OS、同程序K1–K4及uCOS3仍未完成，总目标active，不登记full_target_linked。见[中文说明](audit/STAGE349_CALL_RESULT_FRAME.md)和[实测汇总](audit/logs/stage349-call-result-frame/verification.json)。旧测试与冻结证据不改，任何新增回归失败仍计入门；未提交／推送。
<!-- call-result-frame-checkpoint-end -->

<!-- call-ready-commit-results-start -->
两轮全量均3043项、449失败、1错误；旧失败／错误身份及顺序全部保留，新增失败0、新增错误0，增量门通过但全量与整体检查点仍未通过。新增7项两轮及清理后均通过；6根逐项信任门、递归coqchk、两轮重复编译及构建通过，允许假设仍仅原两项。逐项清理10个本步一次性文件；4份既有缓存bytes/mtime、306份pyc、可复用证明对象和全部失败快照保留。曾因旧探针缺少vo和新增探针缺少直接import各失败一次，均已保留原日志／快照。旧函数审计身份过期和六处框架空白问题不变。两个CPU hook、完整调用者模拟及整核目标未完成；未提交／推送。
<!-- call-ready-commit-results-end -->

<!-- call-ready-commit-checkpoint-start -->
## 第348步：真实TCB调用入口连接共享就绪创建桥

从sfexec入口实际构造九局部分配、实参写入与CPU_SR初始化，保留旧任务记录，再接第347步同一返回堆上的shared_ready_records、ready_core和原hpcrt_step。入口不再要求已分配的局部单元；没有改写已有共享谓词或语义。单因素只删除主函数绑定，字节级非空任务入口保持不变：正向到首hook，负向无第一步；此早拒绝不授下游hook或commit信用。

**仍有两个原CPU hook前提，不是整个OSTaskCreate的TaskSim、冷启动OSInit或具体GOOD_OS。** 实参已经求值，九块互异／新鲜及已有当前线程/spec_crt仍是前提；完整两hook入口尚未构造。真实ISR的WFInt、同程序K1–K4及uCOS3仍未完成，总目标active，不登记full_target_linked。见[中文说明](audit/STAGE348_CALL_READY_COMMIT.md)和[实测汇总](audit/logs/stage348-call-ready-commit/verification.json)。不改旧测试或冻结证据；未提交／推送。
<!-- call-ready-commit-checkpoint-end -->

<!-- init-ready-commit-results-start -->
初始两轮均3036项、454失败、1错误；只删除本步误加空行后5项原格式检查恢复，未修改旧测试。修正后两轮全量均3036项、449失败、1错误；旧失败／错误身份及相对顺序全部保留，新增失败1、新增错误0；全量与整体检查点仍未通过，增量门未豁免。新增7项四轮及清理后均通过；注册修正后重做15根逐项信任门、递归coqchk和构建通过，允许假设仍仅原两项。逐项清理20个本步一次性材料，4份既有缓存bytes/mtime、306份pyc及可复用证明对象保留。全部Coq失败候选／快照、一次新增格式检查失败和一次错误脚本名调用保留。剩余新增失败是第346步组件证据固定_CoqProject全文件hash在必要追加注册后失配，未覆盖或豁免。旧函数审计身份过期和六处框架空白问题仍在。两处hook、完整创建模拟及整核目标未完成；未提交／推送。
<!-- init-ready-commit-results-end -->

<!-- init-ready-commit-checkpoint-start -->
## 第347步：连续TCB返回资源连接原抽象创建步骤

复用第346步连续返回，在同一个Mf上建立原shared_ready_records与ready_core；采用原hpcrt_step同步创建抽象任务、线程控制和客户环境，实际构造单指针参数分配／store／readback，而不是把纯set当执行。仅移除抽象任务插入的对照，旧表不能认证固定更新任务表见证；不靠早期物理门拒绝。不修改原共享谓词或框架规则。

**仍是有两处原CPU hook前提的资源／创建桥，不是完整OSTaskCreate的TaskSim或具体GOOD_OS。** 已有当前线程/spec_crt是前提，不能当作冷启动bootstrap。入口已完成分配／CPU_SR初始化，完整链表、OSInit、真实ISR的WFInt、同程序K1–K4及uCOS3仍未完成；总目标active。不登记full_target_linked。见[中文说明](audit/STAGE347_INIT_READY_COMMIT.md)和[实测记录](audit/logs/stage347-init-ready-commit/verification.json)。不改旧测试／证据；未提交／推送。
<!-- init-ready-commit-checkpoint-end -->

<!-- init-ready-payload-results-start -->
两轮全量均3029项、448失败、1错误；旧失败／错误身份及相对顺序全部保留，新增失败1、新增错误0，全量仍未通过。新增失败为第345步固定_CoqProject哈希在追加本步注册后失配；回归增量门失败且未豁免。新增8项最终连续两轮及清理后均通过；16根逐项信任门、递归coqchk、构建及工程范围检查通过。Coq失败候选及源码快照全部保留；未改旧测试或冻结证明。旧审计过期身份和六处框架空白问题保留。逐项清理11个一次性文件；4份既有缓存bytes/mtime、306份pyc、可复用生产／探针对象及全部失败快照保留。未提交／推送。
<!-- init-ready-payload-results-end -->

<!-- init-ready-payload-checkpoint-start -->
## 第346步：连续TCB初始化返回接入原强就绪payload

真实初始化前缀、发布和返回／释放沿用第345步接口，在同一返回堆组装两行就绪位图、组字节、完整13槽表和任务记录，直接建立已有V293_ready_payload，不另造弱模型。物理入口两种输入均无hook契约执行至首hook；完整返回仍保留两个原CPU hook契约。物理单因素仅将未访问行一个字节0改1，其余物理内存相同；负例的位图／任务关系门拒绝已证，但它同时违反组／行一致性，不声称唯一失败条件，也不给hook后负例执行记分。

**条件式连续初始化返回，不是具体内核GOOD_OS或OSInit执行证明。** 入口已完成分配／CPU_SR初始化，两个CPU hook实现仍缺失；ready_payload不是shared ready_core、完整链表或抽象commit。真实ISR的WFInt、ADR0005与非验证前端保持；同程序K1–K4及uCOS3未完成，总目标active。不登记full_target_linked，不改旧测试／失败。实测见[验证记录](audit/logs/stage346-init-ready-payload/verification.json)和[中文说明](audit/STAGE346_INIT_READY_PAYLOAD.md)。未提交／推送。
<!-- init-ready-payload-checkpoint-end -->

<!-- canonical-init-return-results-start -->
两轮全量均3021项、447失败、1错误；旧失败／错误身份及顺序完全一致，新增失败0、新增错误0，全量仍未通过。新增8项最终连续两轮及清理后均通过；19根逐项信任门、递归coqchk、构建及工程范围检查通过。物理字节对照过度展开的一次中断及新增文本检查误拼Lemma／Theorem的一次失败均保留；未改旧测试或冻结证明。旧审计过期身份和六处框架空白问题保留。逐项清理16个一次性文件；4份既有缓存bytes/mtime、306份pyc、可复用生产／探针对象及全部失败快照保留。未提交／推送。
<!-- canonical-init-return-results-end -->

<!-- canonical-init-return-checkpoint-start -->
## 第345步：完整优先级表接入连续TCB初始化／返回

在保留两个原CPU hook契约的前提下，沿真实TCB初始化前缀、发布及返回／释放，从同一返回堆取得完整13槽表与更新后的canonical任务记录联合资源。独立物理入口分配新旧TCB字段，前缀无hook前提执行至第一个hook；联合后置导出13槽load、记录一致性和哨兵77。19根逐项信任门及递归coqchk通过，允许集仍仅原两项。单槽重复指针对照只证明输入双向关系门拒绝，不声称下游执行或坏状态可达。

**条件式连续初始化返回，不是具体内核GOOD_OS或OSInit执行证明。** 入口已完成分配／CPU_SR初始化，两个CPU hook实际实现仍缺失；7字段canonical记录不是完整就绪／位图／链表强不变量；纯任务映射set不是抽象commit。真实ISR的WFInt、ADR0005与非验证前端保持。同程序K1–K4及uCOS3未完成，总目标active。不登记full_target_linked，不改旧测试／失败。实测见[验证记录](audit/logs/stage345-canonical-init-return/verification.json)和[中文说明](audit/STAGE345_CANONICAL_INIT_RETURN.md)。未提交／推送。
<!-- canonical-init-return-checkpoint-end -->

<!-- init-priority-canonical-results-start -->
两轮全量均3013项、447失败、1错误；旧失败／错误身份及顺序完全一致，新增失败0、新增错误0，全量仍未通过。新增8项最终连续两轮及清理后均通过；19根逐项信任门、递归coqchk、构建及工程范围检查通过。证据准备曾误用已自动清理的临时源码路径，修复后使用冻结源码锁、原源码及保留快照；准备失败和缺失证据导致的一轮8项中1错误记录保留，未改测试或放宽门。旧审计过期身份和六处框架空白问题保留。逐项清理10个一次性文件；4份既有缓存bytes/mtime、306份pyc、可复用生产／探针对象及全部失败快照保留。未提交／推送。
<!-- init-priority-canonical-results-end -->

<!-- init-priority-canonical-checkpoint-start -->
## 第344步：初始化优先级表排除空槽中的多余指针

实际清零前缀建立空表；实际两hook之间的赋值从完整可写表所有权构造成功store，并在同一返回堆保持双向表／任务关系和全部13槽读取。独立有限入口执行真实写表；仅把槽0从null改为优先级12任务指针时，旧单向关系两边均接受，新增反向关系只拒绝重复指针一边，槽外物理内存不变。19根逐项假设检查、两轮编译及递归coqchk通过，允许集仍仅原两项。

**这是初始化片段，不是具体内核GOOD_OS或OSInit执行证明。** 清零与写表实例是两个独立入口；纯任务映射插入不是抽象执行，不提供完整TCB／就绪／链表不变量，不能替代运行期预留槽规则。真实ISR的WFInt、完整初始化链、两个CPU hook、ADR0005与非验证前端缺口保持；同程序K1–K4和uCOS3未完成，总目标active。不登记full_target_linked，不改旧测试／失败。实测分别见[验证记录](audit/logs/stage344-init-priority-canonical/verification.json)与[中文说明](audit/STAGE344_INIT_PRIORITY_CANONICAL.md)。未提交／推送。
<!-- init-priority-canonical-checkpoint-end -->

<!-- global-soundness-bridge-results-start -->
两轮全量均3005项、447失败、1错误；旧失败/错误身份及顺序完全一致，无新增，但全量仍未通过。新增8项两轮均通过；18根信任门、9项原契约、四个独立交换对照及构建通过。旧审计过期身份和六处已跟踪框架空白问题保留。一次性材料清理实测见verification.json；既有缓存、306份pyc及可复用证明对象保留。未提交／推送。
<!-- global-soundness-bridge-results-end -->

<!-- global-soundness-bridge-checkpoint-start -->
## 第343步：原契约的全局soundness证明链通过信任门

初始化分区和执行轨迹转换改为泛化状态的普通归纳，复用第342步完整规则桥，将原WFAPI/WFInt/WFIFun/side_condition接到原框架GOOD_OS。9项原类型由Coq检查一致；18根逐项假设检查、两轮编译和递归coqchk通过，允许集仍仅原两项。四个独立单因素交换对照均先编译、再在最终Soundness假设闭包中因Eqdep拒绝；失败候选记录保留。

**这是有前提的通用soundness，不是具体内核GOOD_OS或OSInit执行证明。** 真实ISR的未过滤WFInt、规范初始化来源、ADR0005、非验证前端和两个CPU hook缺口仍在；同程序K1–K4与uCOS3未完成，总目标active。不登记full_target_linked、不改旧覆盖/失败。全量回归及审计实测见[验证记录](audit/logs/stage343-global-soundness-bridge/verification.json)，不能以局部通过替代整核或全量通过。见[中文说明](audit/STAGE343_GLOBAL_SOUNDNESS_BRIDGE.md)。未提交／推送。
<!-- global-soundness-bridge-checkpoint-end -->

<!-- soundness-assumption-isolation-checkpoint-start -->
## 第342步：原契约下的时间接口TaskSim通过信任门

已定位三条调用规则共享辅助引理的固定内存索引依赖归纳，改用泛化内存的普通归纳，保留完整40条规则。11项原契约由Coq检查类型一致；两轮重复编译、22根逐项假设检查与递归coqchk通过，允许集仍只有原两项，未加入Eqdep。实际OSSchedNew内部映射与非空时间get/set客户端已接到新TaskSim。旧第341步失败与红色对照保留，不改旧测试或旧证据。

本步是任务级关系，不是ProgSim／GOOD_OS或OSInit可达性。实际ISR的WFInt、规范初始化来源、ADR0005、非验证前端与两个CPU hook缺口保持；同程序K1–K4与uCOS3未完成，总目标active。新增检查、全量回归、失败身份比较与清理实测分别见[本步验证记录](audit/logs/stage342-soundness-assumption-isolation/verification.json)，不能以局部证明通过替代全量通过。见[中文说明](audit/STAGE342_SOUNDNESS_ASSUMPTION_ISOLATION.md)。未提交／推送。
<!-- soundness-assumption-isolation-checkpoint-end -->

<!-- time-source-task-sim-results-start -->
第341步最终实测：两轮全量均2989项、447失败、1错误；旧445失败／1错误身份及顺序保持，新增旧工程精确注册快照失败与本轮信任检查失败。新增8项两轮均7通过、1失败。编译与递归coqchk完成不等于信任门通过；额外Eqdep未消除，任务模拟候选不记通过，回归增量门和整体检查点也未通过。逐项清理19个一次性文件，保留失败记录、既有缓存和可复用对象；未提交／推送。
<!-- time-source-task-sim-results-end -->

<!-- time-source-task-sim-checkpoint-start -->
## 第341步：时间强WFAPI通过，任务模拟候选未通过信任门

生成的OSTimeGet／OSTimeSet接到原强就绪／时钟WFAPI，并构造真实框架TaskSim候选及非空联合入口。编译和递归coqchk通过，但13根中4根额外依赖`Eqdep.Eq_rect_eq.eq_rect_eq`，超出原允许集；任务／方法模拟及内部语义桥不记通过。未扩大允许集或改旧框架／测试。9根满足原允许集，包括强WFAPI、入口和名字单因素对照。

这是任务级候选，不是ProgSim／GOOD_OS或OSInit可达性。原非规范初始化夹具、ADR0005、非验证前端和两个CPU hook缺口保持。全目标、同程序K1–K4与uCOS3未完成，总目标active；旧覆盖不改写，未提交／推送。见[第341步中文说明](audit/STAGE341_TIME_SOURCE_TASK_SIM.md)，实测分列于本步verification.json。信任门失败，不以局部编译通过替代。
<!-- time-source-task-sim-checkpoint-end -->

<!-- time-continuous-global-checkpoint-start -->
## 局部进展：真实切换至时间接口返回的连续全局轨迹

第340步按实际客户端/内核边界，从原任务表上的真实切换连续执行生成的OSTimeGet／OSTimeSet，包含真实参数准备、分配、临界复制及释放/返回；客户端内存与内核堆分开。返回保留强core、当前任务与原上下文。非空实例覆盖两种初始IE；仅删除选中任务客户端绑定时，同堆切换仍成功，但顶层调用入口早拒绝，不据此推断下游有效。见[第340步中文说明](audit/STAGE340_TIME_CONTINUOUS_GLOBAL.md)。

**有限存在的连续全局路径，不是任意交错ProgSim、合法ISR、初始化可达性或GOOD_OS。** 实例未分配优先级槽别名不是规范初始化；ADR0005、非验证前端与两个CPU hook缺口保持。同程序K1–K4与uCOS3未完成，总目标active。旧覆盖清单与冻结证据不改写，未提交／推送。
实测：重复编译、17根递归信任检查、增量构建与两轮新增10项检查通过；两轮全量均2981项、445失败、1错误。旧444失败/1错误的身份和顺序保持；新增1个失败为旧第339步测试精确固定_CoqProject导致，事前已记录反例，未改旧测试、未撤销新生产注册、未豁免失败。证明检查通过，但回归增量门和整体检查点仍失败。总体审计旧证据身份过期、原六处空白问题保持。逐项清理14个一次性文件；4份既有缓存恢复前后身份相同，306份pyc和可复用对象保留；未提交／推送。
<!-- time-continuous-global-checkpoint-end -->

<!-- time-ready-global-call-checkpoint-start -->
## 局部进展：真实全局切换后的同堆时间调用

第339步从原强时钟／就绪切换不变量构造实际lpstep切换和当前指针写入，再让任务表中被选中的任务从同一Ms调用生成的OSTimeGet／OSTimeSet，返回保持强core、当前任务资源并释放局部对象。非空实例覆盖所选任务的两种初始IE；只保留旧抽象current的单因素解释在实际切换端点被晚拒绝。见[第339步中文说明](audit/STAGE339_TIME_READY_GLOBAL_CALL.md)。

**一次全局切换加有限局部调用，不是连续全局调用轨迹或GOOD_OS。** 实例额外的未分配优先级表槽别名只满足现有单向关系，不是规范初始化或OSInit可达性证明；不声称调度器计算出目标。ADR0005、非验证前端与CPU hook缺口保持。同程序K1–K4及uCOS3未完成，总目标active。旧覆盖清单及冻结证据不改写；实测结果见本步verification.json，未提交／推送。
实测：重复编译、29根递归信任检查、增量构建及两轮新增10项检查通过。最初两轮全量各2971项、478失败、1错误，额外34项均指向编译改变的.lia.cache；保留原结果，按事前冻结方案仅恢复该缓存、不改源码或测试后，两轮新鲜全量各2971项、444失败、1错误，旧失败／错误身份及顺序完全一致，无新增，但全量仍不通过。诊断脚本曾解析失败并误启动一轮，已中断并保留部分日志，不计为完成的验证。总体审计仍为旧证据身份过期，原六处空白问题保持；未提交／推送。
<!-- time-ready-global-call-checkpoint-end -->

<!-- time-source-ready-call-checkpoint-start -->
## 局部进展：源码时间接口从调用者到返回的资源闭合

第338步把生成的两个完整时间函数接到通用调用者接口：从调用者持有的强就绪／时钟core与当前任务半份资源出发，构造真实调用/分配、同一临界堆上的前后缀、合法抽象一步、返回/free，并保留同一返回堆上的资源。不再把分配后的callee所有权或成功执行作为前提；非空实例量化任意调用者、时钟、设定值和两种初始IE。只保留旧抽象时钟的事前单因素对照，在同一实际执行/返回堆上被强core晚拒绝。见[第338步中文说明](audit/STAGE338_TIME_SOURCE_READY_CALL.md)。

**有限无交错局部路径，不是任意调度的ProgSim、合法ISR或初始化可达性，更不是GOOD_OS。** 强API builder部分复用已有函数体契约；不是经验证C前端，ADR0005与两个CPU hook缺口保持。同程序K1–K4与uCOS3未完成，总目标active。实测检查分别记录于本步verification.json；旧失败、冻结证据和覆盖清单保留，未提交/推送。
实测：重复编译、18根递归信任检查、两轮新鲜源码重放、构建及两轮新增10项检查均通过；两轮全量各2961项、444失败、1错误，原失败/错误身份与顺序完全一致，无新增，但全量仍不通过。旧总体审计失败及六处空白问题保持。逐项清理14个一次性文件、恢复4份既有缓存，306份pyc与可复用对象保留；未提交/推送。
<!-- time-source-ready-call-checkpoint-end -->

<!-- time-source-connection-checkpoint-start -->
## 局部进展：完整时间API的源码对应与共同组件

第337步不重做已有时间证明：从固定配置后的完整C程序重新解析OSTimeGet/OSTimeSet，受限AST生成完整函数并由Coq证明与已有完整函数定义相等；两个生成函数在同一API映射、时间不变量和名字局部不变量下满足GoodI/APIRule。两种只换复制源的负控通过解析后，在不变的函数等式门晚拒绝。见[第337步中文说明](audit/STAGE337_TIME_SOURCE_CONNECTION.md)。

**不是经验证C前端，仍采用ADR0005临界归一化；不是全内核程序、合法ISR或全局初始化可达性。** 两个CPU hook仍缺实现。旧覆盖清单及冻结证据不改写；最终GOOD_OS、同程序K1–K4和uCOS3未完成，总目标active。实测验证单列于本步verification.json，旧失败保持，未提交/推送。
实测：两轮新鲜源码对应/受控晚拒绝、重复编译、8根递归信任检查、构建和新增12项检查均通过；两轮全量各2951项、444失败、1错误，旧失败/错误身份与顺序不变，无新增，但全量仍不通过。逐项清理10个一次性文件、恢复4份既有缓存，306份pyc和可复用证明对象保留；旧总体审计失败保持，未提交/推送。
<!-- time-source-connection-checkpoint-end -->

<!-- published-tick-resources-checkpoint-start -->
## 局部进展：初始化发布的head/Next和零延时资源

第336步沿原连续TCB初始化前缀、真实hook调用、优先级表与链表发布直至返回/释放，在两个CPU hook执行/保持契约下取得实际head/Next、delay0、全部canonical记录和其余字段/链槽/frame联合资源。另有无执行前提的有限实例，连续执行源码head赋值与零延时iteration；只改变delay四字节的候选说明canonical记录不能替代运行时零保持。见[第336步中文说明](audit/STAGE336_PUBLISHED_TICK_RESOURCES.md)。

**两个CPU hook契约仍开放，创建与扫描不是同一全局轨迹，不是合法ISR或无条件完整OS_TCBInit。** 不证明完整tick遍历/唤醒、空表接口或缓存同步；手工源码模型不是经验证前端。GOOD_OS、同程序K1–K4与uCOS3仍未完成，总目标active。实测验证另记本步verification.json；保留旧失败和冻结证据，未提交/推送。
实测：重复编译、11根递归信任检查、源码重放、构建及两轮新增7项均通过；两轮全量均2939项、444失败、1错误，旧失败/错误身份和顺序完全一致，无新增失败，但全量仍不通过。逐项清理10个一次性文件并恢复4份既有缓存；306份pyc、历史证据和可复用对象保留，未提交/推送。
<!-- published-tick-resources-checkpoint-end -->

<!-- tcb-init-tick-zero-checkpoint-start -->
## 局部进展：从实际TCB字段写入取得零延时资源

第335步沿固定源码模型的18条TCB字段写入取得delay44=0，并在同一末端堆上另证实际零延时tick iteration：进入临界区、零分支、Next赋值和退出，保留canonical ready记录、其余字段、参数和原frame。复用原非空初始化入口，不假设成功执行。只改变delay四字节的有限候选族证明：canonical ready记录门在0/3两者均通过，而零延时资源门只通过0。见[第335步中文说明](audit/STAGE335_TCB_INIT_TICK_ZERO.md)。

**这是字段片段，不是完整创建/OSInit或head/Next来源；两段执行同堆但不是合法ISR。** 不证明完整tick遍历或唤醒；手工源码模型不是经验证前端。GOOD_OS、同程序K1–K4及uCOS3仍未完成，总目标active。重复编译、11根递归信任检查、源码重放、构建及两轮新增8项均通过；两轮全量均2932项、444失败、1错误，旧失败/错误身份和顺序完全一致，无新增失败，但全量仍不通过。逐项清理10个一次性文件并恢复4份既有缓存，306份pyc及可复用对象保留；不改旧证据，未提交/推送。
<!-- tcb-init-tick-zero-checkpoint-end -->

<!-- switched-linked-tick-loop-checkpoint-start -->
## 局部进展：链表资源穿过真实调度/切换，实际while一步

第334步从第333步同一增强客户端入口出发，把head/Next和完整ready_full穿过原调度器及实际任务切换；在真实切换末端的同一堆上另证scanner分配、源码head赋值、实际while guard和一次未到期iteration，旧任务延时3→2、Next推进、回到残余while，current保持新选中任务。同输入仅将Next赋值替换为skip的实际循环片段仍完成倒计时与excrit，但在末端pointer门晚拒绝。见[第334步中文说明](audit/STAGE334_SWITCHED_LINKED_TICK_LOOP.md)。

**head/Next仍为显式初始资源，非初始化来源证明；全局switch与局部scanner/head/while尚未连接为合法ISR。** 不证明完整遍历/idle终止、到期唤醒、旧任务恢复或缓存同步；手工源码模型不是经验证前端。GOOD_OS、同程序K1–K4及uCOS3仍未完成，总目标active。编译、16根递归信任检查、新8项及全量两轮结果分开记录，实测见本步verification.json；不改旧失败或冻结证据，未提交/推送。
实测：16根递归信任检查、增量构建与两轮新增8项检查通过；两轮全量均2924项、444失败、1错误。比第333步新增1项旧严格清单快照失败，原443失败/1错误身份和顺序保留；无新增失败门禁仍为false，未豁免。逐项清理10个本步一次性文件并恢复4份既有缓存；历史证据、失败日志和可复用对象保留。
<!-- switched-linked-tick-loop-checkpoint-end -->

<!-- ready-tick-linked-entry-checkpoint-start -->
## 局部进展：显式链表资源下的head赋值与完整未到期迭代

第333步从入口即拥有head/Next的增强资源实例出发，沿实际全局客户端延时调用保留两槽，止于原调度调用前。另证新鲜扫描器分配、源码head读取赋值，以及完整未到期iteration：实际延时3→2、Next推进、退出临界区，保留同一完整ready_full并恢复原IE/临界栈。同输入上仅将Next赋值替换为skip的实际突变片段仍完成倒计时与退出，但在预期scanner指针门被晚拒绝。见[第333步中文说明](audit/STAGE333_READY_TICK_LINKED_ENTRY.md)。

**head/Next是显式初始资源，不由完整ready_full自动推出，也非OSInit/TaskCreate初始化来源证明；全局前缀与局部片段未伪拼成合法ISR。** 无while循环完成、到期唤醒、旧任务恢复或缓存同步结论；手工模型不是经验证前端。最终GOOD_OS、同程序K1–K4与uCOS3仍未完成，总目标active，未提交/推送。
实测：15根递归信任检查、增量构建及新增8项测试通过；两轮全量均2916项、443失败、1错误。较第332步新增1项旧严格_CoqProject快照测试失败，原442失败/1错误身份与顺序保持；无新增失败门禁未通过，未豁免。旧总体覆盖审计和六处空白失败保持。逐项审查后清理10个本步一次性文件、恢复4份既有缓存；旧失败日志、历史证据与可复用对象保留。
<!-- ready-tick-linked-entry-checkpoint-end -->

<!-- switched-tick-prefix-checkpoint-start -->
## 局部进展：显式扫描器准备后的实际 tick 前缀

第332步在第328步原全局切换末端堆上显式分配、准备扫描器，随后从完整ready_full所有权构造原tick iteration前缀：进入临界区、非零判断、实际减一、跳过未到期分支，旧任务延时3→2，停止于读取Next之前。同一输入上仅将减一赋值替换为skip的实际突变片段仍可执行，但在延时2的记录对应关系门被晚拒绝。见[第332步中文说明](audit/STAGE332_SWITCHED_TICK_PREFIX.md)。

**扫描器是显式资源准备，不是源码head初始化或合法ISR入口可达性；局部轨迹没有伪拼成全局中断执行。** 无Next/循环完成、到期唤醒、旧任务重调度或缓存同步结论；手工模型不是经验证前端。最终GOOD_OS、同程序K1–K4及uCOS3未完成，总目标active。编译、递归信任检查与全量结果分开记录，实测见本步verification.json；旧失败和历史证据保持，未提交/推送。
实测：9根递归信任检查、增量构建及新增8项测试通过；两轮全量均2908项、442失败、1错误。比第331步新增1项旧严格_CoqProject快照测试失败，原441失败/1错误身份及顺序保持；无新增失败门禁未通过，未豁免。
<!-- switched-tick-prefix-checkpoint-end -->

<!-- switched-countdown-closure-checkpoint-start -->
## 局部进展：真实切换堆上的倒计时资源闭包

第331步在第328步原全局切换末端的同一堆上，构造旧任务延时 `3 → 2 → 1` 的写入、原抽象等待一步和完整ready_full重装；原位图/表/其他记录/frame及新任务current保持。只省抽象提交的事前单因素对照，在同一个更新堆上被延时对应关系门拒绝。见[第331步中文说明](audit/STAGE331_SWITCHED_COUNTDOWN_CLOSURE.md)。

**这是store级资源闭包，不是实际tick/ISR执行，也不是到期唤醒或旧任务恢复可达性。** 没有补入虚构扫描器资源；缓存仍未同步。最终GOOD_OS、同程序K1–K4和uCOS3未完成，总目标active。编译、信任检查与全量回归分开记录，实测见本步verification.json；旧失败和历史证据保持，未提交/推送。
实测：10根递归信任检查、增量构建及新增8项测试通过；两轮全量均2900项、441失败、1错误。比第330步新增1项旧严格_CoqProject快照测试失败，旧440失败/1错误的身份和顺序保持；无新增失败门禁未通过，未豁免。
<!-- switched-countdown-closure-checkpoint-end -->

<!-- time-delay-nested-return-checkpoint-start -->
## 局部进展：实际延时调用的两层返回后缀

第330步从完整就绪资源和两层局部变量所有权，直接构造实际 `DAcontinuation` 上的资源条件TaskSim：调度器退出临界区/返回，再由延时函数返回客户端，释放全部四个局部对象的类型长度字节，保留原frame。非空实例从真实调用前缀的同一堆取得资源，支持两种保存IE；只中和外层return/free的事前单因素对照，在内层CPU已经释放后被外层变量缺失门拒绝。见[第330步中文说明](audit/STAGE330_TIME_DELAY_NESTED_RETURN.md)。

**这是实际嵌套上下文上的资源条件后缀，不是旧任务唤醒/恢复的全局可达性，不是完整API、ProgSim或GOOD_OS。** 起始资源来自前缀堆，不能冒充实际重新调度的末端堆；缓存仍未同步。统一WFInt、初始化、同程序K1–K4仍开放，uCOS3未开始，总目标active。各项实测与旧失败见本步verification.json，不宣称全量通过；旧证据保持，未提交/推送。
实测：14根递归信任检查、构建及新增8项测试通过；两轮全量均2892项、440失败、1错误。比第329步新增1项旧严格_CoqProject快照测试失败，旧439失败/1错误的身份和顺序保持；无新增失败门禁未通过，未豁免。
<!-- time-delay-nested-return-checkpoint-end -->

<!-- ready-resume-partition-checkpoint-start -->
## 局部进展：完整就绪资源的运行时分割与恢复后缀

第329步将第328步真实全局切换后的同一总堆拆成共享 INV、任务 RDYINV 和原frame；给出精确内存/抽象图join及satp，不重复占有core。实际新任务IE=true，空共享资源的事前单因素候选在其他执行/资源门通过后被INV门拒绝。复用同一完整ready_inv，另从CPU槽和任意合法恢复资源构造退出/返回TaskSim；非空实例支持两种保存IE。见[第329步中文说明](audit/STAGE329_READY_RESUME_PARTITION.md)。

**这不是旧任务恢复可达性，也不是实际嵌套OSTimeDly返回，更不是完整API、全局ProgSim或GOOD_OS。** 后缀实例专门用有限kstop上下文，不冒充原DAcontinuation；缓存、任意API/ISR闭包、统一WFInt、初始化及同程序K1–K4仍开放，uCOS3未开始，总目标active。编译/递归信任检查、全量回归及旧失败分别记录，不能互相替代；实际结果见本步verification.json，不宣称全量通过。历史证据不改写，未提交/推送。
<!-- ready-resume-partition-checkpoint-end -->

<!-- ready-owned-global-switch-checkpoint-start -->
## 局部进展：联合就绪资源跨过原全局任务切换

第328步从第327步同一原始客户端及调度末端堆继续，由当前指针所有权构造实际store与原lpstep，连接到同一全局闭包；物理current和抽象curtid共同改为被选任务，同一新堆保留完整记录/位图/表及全部frame。新活动任务实际IE=true，因此输出ready_full而非错误沿用关闭中断的SWINVt，并另证后者不成立。双IE、计数器回绕、原高层切换与client/OS堆隔离均有实例。只中和末端指针store的事前片段消融在其他资源保持后被当前指针门拒绝，不冒充突变程序的全局执行。见[第328步中文说明](audit/STAGE328_READY_OWNED_GLOBAL_SWITCH.md)。

**仍不是完整API、全局记录不变量、全局ProgSim或GOOD_OS。** frame要求GoodInvAsrt且中断栈相同；helper释放只在早先Mh边界，缓存仍4而high为6。恢复/return、统一WFInt、初始化及同程序K1–K4开放，uCOS3未开始，总目标active。12根递归coqchk及新增8项测试通过；两轮全量均2876项、439失败、1错误，旧失败身份/顺序不变、无新增，全量及总体审计仍未通过。实际结果见本步verification.json；历史证据不改写，未提交/推送。
<!-- ready-owned-global-switch-checkpoint-end -->

<!-- ready-owned-sched-call-checkpoint-start -->
## 局部进展：联合就绪资源穿过真实调度调用

第327步从第326步的同一原始客户端延时调用继续，实际分配/初始化调度CPU槽、进入临界区、调用并返回helper、发布目标、比较并自增计数器，止于原switch之前；同一末端堆联合拥有切换不变量、完整记录/位图/表及CPU/guard/frame。双任务实例支持两种IE和计数器回绕；只在末端观察门把c+1换回旧c的事前单因素对照被晚拒绝，不是程序突变执行。见[第327步中文说明](audit/STAGE327_READY_OWNED_SCHED_CALL.md)。

**本步未证明联合资源跨过实际switch，不是完整API、全局ProgSim或GOOD_OS。** frame要求GoodInvAsrt；helper释放见证只在返回边界Mh，不夸大为最终整块fresh。缓存、恢复/return、统一WFInt、初始化及同程序K1–K4仍开放，uCOS3未开始，总目标active。全量2868项中439失败、1错误，其中新增一项旧严格清单快照测试失败；无新增失败门禁未通过且未豁免。详见本步verification.json；历史证据不改写，未提交/推送。
<!-- ready-owned-sched-call-checkpoint-end -->

<!-- time-delay-ready-closure-checkpoint-start -->
## 局部进展：延时调用在调度入口闭合联合就绪资源

第326步从同一原始客户端常量调用出发，在真实阻塞后的同一堆重建 `V293_ready_full`，联合拥有完整TCB记录、就绪位图／优先级表、当前指针、共享字段及局部／frame资源，并给出精确物理读取。双任务实例覆盖两种IE；只在末端对应关系门换回旧抽象任务表的事前消融，在保留同一实际执行与资源后被位4对应关系晚拒绝。见[第326步中文说明](audit/STAGE326_TIME_DELAY_READY_CLOSURE.md)。

**本步仅到调度调用前，尚非跨调度／切换的所有权闭合，更不是完整API、全局ProgSim或GOOD_OS。** 第325步切换可达性保留；缓存、恢复／return、统一WFInt、初始化及同程序K1–K4仍开放。uCOS3未开始，总目标active；实测与旧失败见本步verification.json，未提交／推送。
<!-- time-delay-ready-closure-checkpoint-end -->

<!-- time-delay-call-global-checkpoint-start -->
## 局部进展：客户端延时调用到原全局切换

第325步从无伪造调用帧的客户端常量调用出发，真实求参、跨入OS、分配/初始化，再阻塞、执行调度/helper、比较自增，接到原全局切换。同一演化OS堆保留记录/位图/局部/CPU/canary；客户端堆与环境保持不变，即使两份堆使用同编号参数块且值不同。支持两种IE和计数器回绕。只删延时函数绑定的事前对照在相同全局客户端前缀后拒绝OS入口，仅检验早期链接。见[第325步中文说明](audit/STAGE325_TIME_DELAY_CALL_GLOBAL.md)。

**已补齐常量调用的整条原全局可达轨迹，但不是完整API、全局记录不变量、全局ProgSim或GOOD_OS。** 有限无交错，未推广任意表达式或客户端/OS return；优先级缓存、恢复/return、统一WFInt、初始化及同程序K1–K4仍开放，uCOS3未开始，总目标active。实际复核/旧失败见本步verification.json；不改旧源码、测试及冻结证据，未提交/推送。
<!-- time-delay-call-global-checkpoint-end -->

<!-- time-delay-allocated-sched-checkpoint-start -->
## 局部进展：真实分配的延时调用接通调度与末端切换

第324步在同一程序、同一演化堆中，从真实scall构造参数/局部分配、初始化、y首赋值和阻塞，再实际调用调度器/helper、比较并自增，最终在真实末端堆执行原低层切换，匹配同一阻塞后任务表的原高层选择。双任务实例保留记录、位图、延时、局部/CPU/canary，支持两种IE和计数器回绕。只改物理优先级表第6项的单因素对照在执行/资源门通过后，被发布目标身份门晚拒绝。见[第324步中文说明](audit/STAGE324_TIME_DELAY_ALLOCATED_SCHED.md)。

**这是局部真实调用前缀加末端原全局一步，不是整条调用全局可达性、完整API或GOOD_OS。** 客户端堆/OS堆分配边界、优先级缓存同步、恢复/return、全局记录不变量/ProgSim、统一WFInt、初始化和同程序K1–K4仍开放。负例仅局部前缀，不冒充错误物理表上的成功抽象调度；uCOS3未开始、总目标active。实际复核与旧失败见verification.json；历史证据不改写，未提交/推送。
<!-- time-delay-allocated-sched-checkpoint-end -->

<!-- time-delay-call-block-checkpoint-start -->
## 局部进展：真实延时调用接通阻塞与临界区退出

第323步从第322步真实调用及y首次赋值的末端继续，实际清除就绪位、写入延时并执行 `excrit`，止于 `OS_Sched` 调用前。同一末端堆给出原抽象阻塞一步、全部任务记录和位图；非空双任务实例支持两种IE，保留参数、CPU写权限与canary。只省延时写入的片段级单因素消融在清位、退出临界区及资源门成功后，被延时值门晚拒绝。见[第323步中文说明](audit/STAGE323_TIME_DELAY_CALL_BLOCK.md)。

**已接通入口到阻塞，但尚未接通本调用的调度／切换，不是完整API或GOOD_OS。** 不重复执行guard、encrit或y赋值；不将不同continuation的消融片段伪拼成完整调用。全局客户端堆／OS堆边界、优先级缓存、恢复／return、全局记录不变量／ProgSim、统一WFInt、初始化及同程序K1–K4仍开放，uCOS3未开始，目标active。实际复核与旧失败以本步verification.json为准；旧证据不改写，未提交／推送。
<!-- time-delay-call-block-checkpoint-end -->

<!-- time-delay-call-entry-checkpoint-start -->
## 局部进展：真实延时调用分配与未初始化 y 的首次赋值

第322步从实际 `scall` 构造参数／局部分配和CPU初始化，保持y为真实未初始化的 `Vundef`，再执行入口判断、临界区进入及TCB到y的首次实际赋值。非空同堆实例支持两种IE，保留任务记录／共享状态、参数、CPU写权限和canary。仅跳过CPU初始化的片段级消融在其他执行／资源门通过后，被CPU值门晚拒绝。见[第322步中文说明](audit/STAGE322_TIME_DELAY_CALL_ENTRY.md)。

**新入口尚未与后续阻塞／调度／切换证明接通，不是完整API或GOOD_OS。** 首次赋值终点不可重跑整个body；局部调用仍须处理全局客户端堆／OS堆边界。通用frame仅保留入口辅助状态快照，具体非aux敏感实例另证真实临界末端资源。全局记录不变量、全局ProgSim、优先级缓存、恢复／return、统一WFInt、初始化与同程序K1–K4仍开放，uCOS3未开始，目标active。实测与旧失败见本步verification.json；旧证据不改写，未提交／推送。
<!-- time-delay-call-entry-checkpoint-end -->

<!-- time-delay-global-switch-checkpoint-start -->
## 局部进展：真实延时／调度前缀成为原框架全局轨迹

第321步在保守扩展的同一程序中加入完整规范化延时声明，用精确匹配的调用帧，将实际阻塞、调度调用、比较、自增及末端切换整体提升为原 `lpstep` 闭包。非空同堆实例保存旧continuation、两任务环境／辅助状态、记录、CPU写权限和canary；支持两种IE及计数器回绕。仅删helper绑定的消融检验早期调用链接，不作为下游机制证据。见[第321步中文说明](audit/STAGE321_TIME_DELAY_GLOBAL_SWITCH.md)。

**仍不是完整API、全局记录不变量、全局ProgSim或GOOD_OS。** 入口在cpu_sr初始化之后，匹配帧不等于已证明调用入口可达；仅正向有限无交错轨迹。原switch不更新优先级缓存，旧任务恢复／return、统一WFInt、初始化和同程序K1–K4仍开放，uCOS3未开始，目标active。实际复核、旧失败与清理见本步verification.json；不改旧源码／测试／冻结证据，未提交／推送。
<!-- time-delay-global-switch-checkpoint-end -->

<!-- time-delay-switch-checkpoint-start -->
## 局部进展：延时阻塞后实际比较、自增和原框架切换

第320步消费真实调度调用，执行优先级比较与模2³²计数器自增，再由写权限构造原 `lpstep` 切换，匹配同一阻塞后任务表的原 `hswi_step`。两任务非空实例保留旧continuation、全部记录、canary及CPU写权限，支持两种IE与计数器回绕。只删尾部自增的片段级消融在同一输入堆／前缀、实际切换及资源门通过后，被计数器门晚拒绝。见[第320步中文说明](audit/STAGE320_TIME_DELAY_SWITCH.md)。

**原switch仅更新current TCB指针，不同步优先级缓存；不是完整API、恢复或GOOD_OS。** 延时入口仍在cpu_sr初始化之后，前缀局部、末端原全局一步；有限无交错，不是全局记录不变量或全局ProgSim。统一WFInt、初始化及同程序K1–K4仍开放，uCOS3未开始，目标active。真实复核、旧失败与清理以本步verification.json为准；旧源码／测试／冻结证据不改写，未提交／推送。
<!-- time-delay-switch-checkpoint-end -->

<!-- time-delay-sched-call-checkpoint-start -->
## 局部进展：阻塞任务实际调用调度器并发布目标指针

第319步从延时阻塞接到实际 `OS_Sched`／`OS_SchedNew` 调用、局部分配初始化、两道guard、helper释放和目标指针写回，无须假设当前任务仍就绪。双任务同堆实例保留原 `spec_step`、全部记录、位图、CPU可写及canary；同一程序支持两种IE。只改优先级表第6项的单因素对照在其他执行／资源门通过后被目标身份门晚拒绝。见[第319步中文说明](audit/STAGE319_TIME_DELAY_SCHED_CALL.md)。

**止于比较／计数器／switch之前，不是已切换、恢复或完整API，更不是 GOOD_OS。** current仍为阻塞任务；另一任务已ready是输入条件。规范化port、有限无交错轨迹；全局记录不变量、统一WFInt／全局ProgSim、初始化及同程序K1–K4仍开放，uCOS3未开始，目标active。真实复核、旧失败及清理以本步verification.json为准。旧源码／测试／冻结证据不改写，未提交／推送。
<!-- time-delay-sched-call-checkpoint-end -->

<!-- time-delay-entry-checkpoint-start -->
## 局部进展：延时入口判断、临界区恢复与真实提前返回

第318步把 `OSTimeDly` 三道短路判断接到实际临界更新和 `excrit`，在同一末端堆连接原抽象阻塞一步、全部任务记录、位图与 frame；支持无符号高位 ticks 及两种初始 IE。提前返回实际释放局部块并恢复 caller。只省略 `excrit` 的单因素对照在执行及物理资源均成立之后，被辅助状态恢复门晚拒绝。见[第318步中文说明](audit/STAGE318_TIME_DELAY_ENTRY.md)。

**入口在 cpu_sr 初始化之后，正分支止于 OS_Sched 调用前；不是完整 API、全局记录不变量或 GOOD_OS。** current仍指向刚阻塞任务，不冒充真实调度；较低优先级任务已ready仍为输入条件，不是唤醒。调用分配／初始化、真实调度与恢复、统一 WFInt／全局 ProgSim、初始化及同程序K1–K4仍开放，uCOS3未开始，目标active。实际复核与保留的旧失败见本步 verification.json；旧源码／测试／冻结证据不改写，未提交／推送。
<!-- time-delay-entry-checkpoint-end -->

<!-- time-delay-task-bridge-checkpoint-start -->
## 局部进展：延时阻塞连接原抽象一步及同堆全部任务记录

第317步将真实 `OSTimeDly` 临界更新接到原 `spec_prim_step`：从共享所有权读取 current／任务表，同一末端堆给出全部任务记录与位图关系，仅提交抽象任务表，保留 current／事件／时间与frame。两任务及canary实例非空；省略抽象提交的单因素对照在实际执行与物理记录成立后被晚拒绝。见[第317步中文说明](audit/STAGE317_TIME_DELAY_TASK_BRIDGE.md)。

**这是新局部临界更新契约，不是完整API注册、全局记录不变量或 GOOD_OS。** current仍指向刚阻塞任务，不能直接改current冒充调度；低优先级已ready仍是输入条件，非真实唤醒。guard／初始化／临界调用／return、后续调度、统一 WFInt／全局 ProgSim、初始化及同程序K1–K4仍开放；uCOS3未开始，目标active。实际复核与保留的旧失败以本步 verification.json 为准。旧源码／测试／冻结证据不改写，未提交／推送。
<!-- time-delay-task-bridge-checkpoint-end -->

<!-- time-delay-block-checkpoint-start -->
## 局部进展：真实延时阻塞更新连接同堆记录与就绪位图

第316步证明 `OSTimeDly` 临界区更新片段：实际执行撤出就绪位和非零延时写入，保留外部frame，同一末端堆给出原任务记录与位图/任务投影关系。非空实例中4仍就绪时6不能被选中；4阻塞后6才成为最高就绪。只删除延时写入的对照仍完成位图更新，但在末端延时门被拒绝。见[第316步中文说明](audit/STAGE316_TIME_DELAY_BLOCK.md)。

**这是局部阻塞片段，不是完整API、真实唤醒、物理回切或 GOOD_OS。** 低优先级任务已就绪是输入条件；guard/初始化、原抽象 `spec_step`、全局记录不变量、统一 WFInt/ProgSim、同程序K1–K4仍开放，uCOS3未开始。真实测试与递归复核结果见本步 verification.json；新增注册造成的旧315快照测试失配已单独记录，不改旧测试或冻结证据。目标active，未提交／推送。
<!-- time-delay-block-checkpoint-end -->

<!-- interrupt-resumed-task-sim-checkpoint-start -->
## 局部进展：非空 ISR 栈的原 TaskSim 与实际 free/exint 返回

第315步补齐旧返回证明仅支持空 ISR 栈的缺口。从 CPU/Core/CurTid 所有权构造原 `TaskSim`，并对任意外部内存 frame 执行八步释放、caller 恢复及 `exint`，不预设后继 TaskSim。删掉末端 `exint` 的单因素对照在相同七步前缀完成后被晚拒绝。详见[第315步中文说明](audit/STAGE315_INTERRUPT_RESUMED_TASK_SIM.md)。

**入口仍是已恢复 current 的 pending 状态；非空资源实例的上下文重设不证明 Ready/Waiting 到入口的可达性。** Waiting 仍须真实唤醒及重新调度。主模拟限保存 IE=false、IRQ 请求全清和受限 scalar；不是全局 ProgSim、统一 WFInt 或 GOOD_OS。初始化、全交错保持、同程序 K1–K4 及 uCOS3 仍开放，目标 active。实际测试、递归复核、旧失败和清理结果以本步 verification.json 为准；旧证据/旧测试不改写，未提交/推送。
<!-- interrupt-resumed-task-sim-checkpoint-end -->

<!-- builder-owned-cpu-checkpoint-start -->
## 局部进展：真实分配的 CPU 单元写权限跨切换保持

第314步加强 builder 前缀的资源结论：实际分配的 CPU 可写单元经同程序中断入口、调度切换和被选任务三步执行保持；原 `free` 可合法释放且剩余堆精确。仅撤掉首字节写权限、保持地址和值不变的对照中，读取仍成功，但释放被晚拒绝。详见[第314步中文说明](audit/STAGE314_BUILDER_OWNED_CPU.md)。

**这是释放能力及条件 pending-exit ProgSim，不是实际恢复／释放旧任务，也不是全局 ProgSim 或 GOOD_OS。** Waiting 仍阻塞，不能直接改成 ready。9个根递归复核、新增8项回归通过；完整2768项保留原437失败、1错误及原ID顺序，旧覆盖身份错误与六处空白问题不变。统一 WFInt／controls、全交错资源保持、真实恢复及 caller 后继、初始化与同程序K1–K4仍开放；uCOS3未开始，目标active。17项临时文件已逐项核对后清理，旧缓存、字节码、源码和证据保留；未提交／推送。
<!-- builder-owned-cpu-checkpoint-end -->

<!-- selected-scalar-task-sim-checkpoint-start -->
## 局部进展：切换后被选任务的原框架 TaskSim 与实际三步执行

第313步从实际切换后同一块堆的资源分区构造原 `TaskSim`，不再假设后继任务模拟已成立。原非空 `CSready` 使用真实被选环境继续执行常量求值、位取反及语句 continuation 消去三步，同时保留切出任务的非空caller。详见[第313步中文说明](audit/STAGE313_SELECTED_SCALAR_TASK_SIM.md)及其机器验证记录。

**TaskSim仅覆盖指定纯标量形状；有限全局轨迹与该任务模拟不是全局 ProgSim，也不是 GOOD_OS。** 原一元运算注释stub误读已由真实编译反例发现并修正，失败证据保留。全局中断交错、统一handler／WFInt、旧任务恢复与CPU资源保持、初始化及同程序K1–K4仍开放；uCOS3未开始，目标active，未提交／推送。18个根递归复核、新增8项回归通过；完整2760项回归保留437失败、1错误及原顺序。旧覆盖审计与六处旧空白问题保留，旧测试与冻结证据不改写。
<!-- selected-scalar-task-sim-checkpoint-end -->

<!-- builder-dispatch-global-checkpoint-start -->
## 局部进展：原中断入口连接同程序全局调度轨迹

第312步将实际 `pint`、EOI／Enter／normalized Exit／缓存拷贝提升为原 `lpstep` 的有限全局轨迹，在同一末端堆连接原物理切换与高层调度。非空实例保留原表达式 continuation、非空shadow caller和旧任务待执行的中断返回上下文。详见[第312步中文说明](audit/STAGE312_BUILDER_DISPATCH_GLOBAL.md)。

**有限全局执行与末端一步匹配，不是所有交错的模拟，也不是 GOOD_OS。** 5个根递归复核、新增7项回归通过；完整2752项回归保留437失败、1错误及原顺序，旧审计／空白失败不变。缓存／lookup一致性仍是显式输入，后继任务执行、旧任务恢复、统一 WFInt／TaskSim、初始化与同程序K1–K4仍未完成；uCOS3未开始，目标active，未提交／推送。
<!-- builder-dispatch-global-checkpoint-end -->

<!-- builder-dispatch-switch-checkpoint-start -->
## 局部进展：实际 builder 调度前缀连接同堆任务切换

第311步从未过滤的 `BuildintPre` 构造同程序的 EOI／Enter／normalized Exit／优先级缓存拷贝，再将同一后继堆交给原物理切换与高层调度规则。非空实例从阻塞任务切换到另一个最高就绪任务；不把等待任务改成 ready。详见[第311步中文说明](audit/STAGE311_BUILDER_DISPATCH_SWITCH.md)。

**仍是有限局部 handler 前缀与末端全局切点匹配，尚未提升整段全局轨迹，不是全交错模拟或 GOOD_OS。** 缓存／lookup 数值一致性是显式输入前提，初始化与全程序保持仍开放。11个根递归复核、新增7项回归通过；完整2745项回归保留437失败、1错误及原顺序。旧审计／空白失败保留，后继 continuation、统一 WFInt／TaskSim、同程序K1–K4仍未完成；uCOS3未开始，目标active，未提交／推送。
<!-- builder-dispatch-switch-checkpoint-end -->

<!-- control-switch-simulation-checkpoint-start -->
## 局部进展：原物理切换点与高层调度的前向匹配

第310步从所有权构造原物理切换和高层调度，证明所有低层一步后继相同、控制捕获与任务/内存帧保持，并复用原 `ProgSim` 的条件提升。非空 normalized Exit 前缀实际执行缓存拷贝，再在同一堆完成物理/高层切换，核对切出/就绪任务代码、环境及保存上下文。详见[第310步中文说明](audit/STAGE310_CONTROL_SWITCH_SIMULATION.md)。

**仍是切换点局部匹配，后继 ProgSim 是独立前提；不是整段 handler 全交错模拟或 GOOD_OS。** 6个根递归复核、新增7项回归通过；完整2738项回归保留437失败、1错误及原顺序。旧审计/空白失败保留，未迁移完整 WFInt/TaskSim、未完成初始化与同程序K1–K4；uCOS3未开始，目标active，未提交/推送。
<!-- control-switch-simulation-checkpoint-end -->

<!-- control-scheduler-checkpoint-start -->
## 局部进展：固定控制前端连接原高层任务切换

第309步保留原控制局部步，以显式事件连接原 `hswi_step`，证明旧任务 continuation 更新、`curtid` 变为最高就绪目标、三个控制字节及其他任务项保持。非空实际 Exit 前缀先选出目标并读回同一后继堆，再连接同一抽象任务状态的高层切换；同一固定 handler 支持 quiet、切换与当前已最高三种路径。详见[第309步中文说明](audit/STAGE309_CONTROL_SCHEDULER.md)。

**不是 raw port 执行或低高层模拟，也未迁移旧 WFInt/TaskSim/GOOD_OS。** 源码前缀仍停在缺失的 port112 前；完整初始化、统一中断模拟、同程序 K1–K4及uCOS3仍开放。实际复核和保留的旧失败见本步 verification.json，未提交/推送。
<!-- control-scheduler-checkpoint-end -->

<!-- builder-quiet-execution-checkpoint-start -->
## 局部进展：同一 builder 的全部不调度分支实际返回

第308步用同一程序连接未启动、嵌套、饱和、锁非零分支的完整 EOI/Enter/normalized Exit，并执行实际 pint/exint。原深度255的精确后继为254，不错误宣称原内存恒等；同一后继支持资源 snapshot、固定控制前端和旧 BuildintRet。六类非空实例及完成后的单因素观察见[第308步中文说明](audit/STAGE308_BUILDER_QUIET_EXECUTION.md)。

**仍是有限执行存在性，不是初始化、全交错 safety、TaskSim、统一 WFInt 或 GOOD_OS。** 需调度分支、同程序 K1–K4及uCOS3仍开放。实测复核和旧失败以本步 verification.json 为准；历史冻结证据保留，未提交/推送。
<!-- builder-quiet-execution-checkpoint-end -->

<!-- builder-nested-return-checkpoint-start -->
## 局部进展：同一 builder 的实际嵌套中断完整返回

第307步由原 `pint` 创建保存上下文，连接完整 EOI/Enter/normalized Exit 嵌套调用，再执行 `exint`。同一轨迹恢复整块原内存及原任务代码、caller、continuation、ISR与任务辅助状态；主接口明确要求入口和返回一步，避免零步 roundtrip。非空深度1/254及后置 caller 单因素观察见[第307步中文说明](audit/STAGE307_BUILDER_NESTED_RETURN.md)。

**限 running=1、原深度1..254，仍是有限执行存在性，不是初始化可达性、全交错 safety、TaskSim、统一 WFInt 或 GOOD_OS。** 同程序 K1–K4及uCOS3仍开放。构建、递归复核、回归及旧失败以本步 verification.json 为准；不改旧冻结证据，未提交/推送。
<!-- builder-nested-return-checkpoint-end -->

<!-- builder-nested-exit-checkpoint-start -->
## 局部进展：同一 builder 连接完整 Exit 嵌套调用

第306步复用 EOI/Enter 的同一后继堆执行 normalized `OSIntExit` 嵌套分支，完整调用/局部分配/临界栈/返回释放后，在同一堆恢复原深度资源。非空深度1/254实例及精确 fresh 块释放见[第306步中文说明](audit/STAGE306_BUILDER_NESTED_EXIT.md)。

**终点仍在 exint 前；原深度限1..254，不是 raw port、TaskSim、旧完整 WFInt 或 GOOD_OS。** 同程序 K1–K4及uCOS3仍开放。构建、递归复核、完整回归、305历史精确注册断言新增失败均以本步 verification.json 为准；不修改旧测试或冻结证据，未提交/推送。
<!-- builder-nested-exit-checkpoint-end -->

<!-- builder-enter-resources-checkpoint-start -->
## 局部进展：同一 builder 的 EOI/Enter 前缀保留后继资源

第305步从未过滤 `BuildintPre` 推出实际中断上下文，执行 EOI 与完整 Enter 调用，在同一后继内存保留 canonical ready/TCB/storage snapshot，并读回固定前端结果。非空资源深度0/254/255及后置 ISR 观察的单因素对照见[第305步中文说明](audit/STAGE305_BUILDER_ENTER_RESOURCES.md)。

**输入仍是 handler-entry，不是初始化/pint 可达性；有限局部执行不是 TaskSim 或 GOOD_OS。** 完整 Exit、旧 Inv/WFInt 和同程序 K1–K4 仍开放。构建、递归复核、回归及保留失败以本步 verification.json 为准；uCOS3未开始，目标 active，未提交/推送。
<!-- builder-enter-resources-checkpoint-end -->

<!-- builder-enter-call-checkpoint-start -->
## 局部进展：实际 builder 资源驱动完整 Enter 调用

第304步从未过滤 `BuildintPre` 提取绑定、三个控制字节、写权限及空间分离，直接构造完整 Enter 调用；读回与固定前端使用同一后继内存和同一输入 `getabst st`，不再由上层另给任意抽象状态。非空原 ready/TCB/storage 堆的0/254/255深度实例见[第304步中文说明](audit/STAGE304_BUILDER_ENTER_CALL.md)。

**这是 handler-entry 资源的环境/内存投影调用，不是 EOI/pint/TaskSim 或 GOOD_OS。** 未建立后继旧 Inv、统一 WFInt、初始化及同程序 K1–K4；uCOS3未开始，目标 active，未提交/推送。具体复核与旧失败见本步 verification.json。
<!-- builder-enter-call-checkpoint-end -->

<!-- enter-call-prefix-checkpoint-start -->
## 局部进展：完整 Enter 调用接入实际中断前缀

第303步从框架原中断入口创建保存上下文，执行 EOI 和完整 `OSIntEnter` 调用，停在 Exit 调用入口；同一后继内存读回固定 Enter 一步。非空堆、shadow caller、未启动/254/255及保留其他 ISR 位的用例见[第303步中文说明](audit/STAGE303_ENTER_CALL_PREFIX.md)。

**有限执行存在性，不是 TaskSim、完整 ISR 或 GOOD_OS。** builder/初始化关联、完整 Exit、统一旧 WFInt 与同程序 K1–K4 仍开放。10个新结论、8项新测试、递归复核及完整回归以本步 verification.json 为准；旧失败保留，uCOS3未开始，目标 active，未提交/推送。
<!-- enter-call-prefix-checkpoint-end -->

<!-- control-execution-checkpoint-start -->
## 局部进展：真实控制语句与固定前端共用同一后继内存

第302步从实际控制字节与可写权限构造 Enter 更新、Exit 递减和双 guard 的真实执行；同一后继内存读回固定 Enter/Exit 一步结果，并保留嵌套字节外的内存。非空真实堆的同程序锁位对照分别到 dispatch / skip；见[第302步中文说明](audit/STAGE302_CONTROL_EXECUTION.md)。

**仍是无交错源片段，不是完整函数、旧 WFInt 迁移或 GOOD_OS。** Exit 限 running=1 内部切点，enabled 停在任意 dispatch 入口；初始化、全局调度与完整中断上下文仍开放。16个新结论与7项新测试的实测、递归 coqchk、稳定重编译、三个隔离定义消融及失败尝试见本步 verification.json。全仓旧失败保留，不宣称全仓通过；uCOS3未开始，目标 active，未提交/推送。
<!-- control-execution-checkpoint-end -->

<!-- fixed-control-spec-checkpoint-start -->
## 局部进展：固定控制前端执行 Enter/Exit 决策

第301步把控制选择器推进为显式有状态的固定 Enter/Exit 前端，并复用真实 Enter updates / Exit decrement 的 Hoare 字节资源更新。相同新 Exit 操作、相同旧抽象任务状态的真实锁字节对照产生不同且精确的后继；原 Core 有限执行双向反射，不增加任选调度。见[第301步中文说明](audit/STAGE301_FIXED_CONTROL_SPEC.md)。

**不是已迁移的旧 osintspec/WFInt 或 GOOD_OS。** 新表类型不同；旧完整调用仍分别使用CCspec/QCspec；全局切换、C执行与前端模拟、初始化仍开放。18个新结论经递归coqchk通过，8项新测试通过，三个独立Coq单因素对照均拒绝错误变体；增量build通过，audit仍有旧证据身份失配。全回归及清理实测见本步verification.json。uCOS3未开始，目标active，未提交/推送。
<!-- fixed-control-spec-checkpoint-end -->

<!-- control-retention-checkpoint-start -->
## 局部进展：真实控制字节接入精确中断决策

第300步从未附加 quiet/最高就绪过滤的实际 `BuildintPre` 唯一捕获控制字节，提供确定性选择接口并连接真实 Exit 局部 guard。仅改锁字节的完整调用对照表明：当前不变式允许的同一抽象任务状态，可有相反的调度决定。见[第300步中文说明](audit/STAGE300_CONTROL_RETENTION.md)与[ADR-0011](docs/adr/0011-精确中断决策保留真实控制信息.md)。

**不是框架状态迁移、统一生产规格或 GOOD_OS。** 对照仍使用不同的 CCspec/QCspec，未证明初始化可达；新直积尚未进入旧 WFInt。20个新结论经递归 coqchk 复核，7项新测试通过；完整回归2670项首次445失败、1错误；恢复原缓存后436失败、1错误，旧失败顺序保留；增量构建通过，audit仍因旧证据身份失配失败。uCOS3未开始，目标 active，未提交/推送。
<!-- control-retention-checkpoint-end -->

<!-- quiet-sched-bridge-checkpoint-start -->
## 局部进展：当前已最高的 quiet 分支接入精确 sched 规格

第299步从实际 `BuildintPre` 出发，在同状态最高就绪条件下精确消耗一次 `sched`，再连接原完整 `EOI → OSIntEnter → OSIntExit → exint`。深度1和255的 typed 非空入口与 enabled dispatch 共用原 `sched ;; END None`、BDspec、Inv、LI；非最高 quiet 输入仍被该条件拒绝。见[第299步中文说明](audit/STAGE299_QUIET_SCHED_BRIDGE.md)。

**不是 unfiltered WFInt 或 GOOD_OS。** 已存在并复用的是特定三函数程序的内部 WFIFun，不是全内核环境。quiet 当前非最高、强 current 关联、一般中断上下文、统一生产规格/初始化及同程序 K1–K4 仍开放，uCOS3未开始。旧失败与冻结证据保留，目标 active；实测以本步 verification.json 为准，未提交/推送。
<!-- quiet-sched-bridge-checkpoint-end -->

<!-- quiet-isr-return-checkpoint-start -->
## 局部进展：quiet 中断返回保留其他 ISR 位

第298步从实际 builder 的 `isr_inv` 推出低位清空，EOI 后只关闭返回所需区间，不再要求全部 ISR 位为 false。完整 `EOI → OSIntEnter → OSIntExit → exint` 接口保持原 quiet 过滤、END None、Inv 与 LI；同堆仅激活另一 ISR 位的非空入口、完整包装及返回资源见[第298步中文说明](audit/STAGE298_QUIET_ISR_RETURN.md)。

**不是 unfiltered WFInt 或 GOOD_OS。** 返回资源是 exint 条件切点，两个独立端点不等于具体执行轨迹，也不证明初始化可达。enabled dispatch、强 current guard、统一高层规格和同程序 K1–K4 仍开放，uCOS3 未开始。旧失败/冻结证据保留；实测见本步 verification.json，未提交/推送。
<!-- quiet-isr-return-checkpoint-end -->

<!-- no-dispatch-checkpoint-start -->
## 局部进展：三类不调度分支共用完整调用接口

第297步将 running=0、嵌套未退尽和调度锁非零接入同一 `END None` API、同一 canonical storage Inv 和原 `RDYINV` 后置条件。非空原 AC 输入及只改锁字节的完整调用对照见[第297步中文说明](audit/STAGE297_EXIT_NO_DISPATCH.md)。

**这是不调度分支的统一，不是整个 OSIntExit。** enabled dispatch 仍是 `sched ;; END None`；未用任选调度的弱规格。一般中断上下文、强 current guard、统一高层规格、WFIFun/WFInt、GOOD_OS 和同程序 K1–K4 仍待完成，uCOS3 尚未开始。旧失败/冻结证据保留，目标 active，未提交/推送；实测以本步 verification.json 为准。
<!-- no-dispatch-checkpoint-end -->

<!-- quiet-storage-checkpoint-start -->
## 局部进展：running=0 完整调用接入可调度分支的同一 storage Inv

第296步支持 running 位于任意 storage 位置。仅将原非空 AC 堆的 running 字节1改0，证明其他地址不变，构造完整 quiet 客户端调用，并由 Coq 相等式确认其后置使用原 `ACinv`。见[第296步中文说明](audit/STAGE296_QUIET_STORAGE_CALL.md)。

**统一的是不变量，不是高层 API。** quiet 仍是 `END None`，enabled 仍是 `sched ;; END None`；不引入任选调度的弱规格。locked/nested canonical storage、统一 OSIntExit、一般中断上下文、强 current guard、WFIFun/WFInt、GOOD_OS 和同程序 K1–K4 仍待完成，uCOS3 未开始。旧失败与封存证据保留，目标 active，未提交/推送；以本步 verification.json 的实测为准。
<!-- quiet-storage-checkpoint-end -->

<!-- dispatch-call-checkpoint-start -->
## 局部进展：可调度 OSIntExit 的两种结果共用一个 sched API

第295步将 changed 与最高就绪仍是当前任务的完整客户端调用合并到 `V293_exit_dispatch_client_call_TaskSim`：两层相同 scall、同一 `sched ;; END None` 绑定，公开前提不再区分 highest/not-highest。self 分支从原资源推导抽象 current 并执行真实 `spec_sched_step`，再连接原完整低层入口。两份既有非空堆共用相同低层程序和 API；见[第295步中文说明](audit/STAGE295_EXIT_DISPATCH_CALL.md)。

**只统一 running=1、n=0/1、lock=0 的 enabled dispatch，不是整个 OSIntExit 统一规格或 WFIFun。** quiet/nested/locked、一般 IE/ISR 上下文、强 current guard、GOOD_OS 和同程序 K1–K4 缺口保留，uCOS3 未开始。只改抽象 current 的对照限定为 self-sched 单步，不冒充完整执行消融；旧失败与冻结证据保留，目标 active，未提交/推送，实测见本步 verification.json。
<!-- dispatch-call-checkpoint-end -->

<!-- equal-call-checkpoint-start -->
## 局部进展：最高优先级仍是当前任务时的完整客户端调用

第294步从两层相同 scall 出发，连接任意 fresh saved 分配/初始化、running、临界段、n=0/1 递减与双 guard、真实 helper、target 写入及相等比较，再退出/释放/返回。非空 EC 堆没有预分配 saved；后置仍为原 storage 家族 RDYINV，公开接口没有执行结果或下游 TaskSim 前提。见[第294步中文说明](audit/STAGE294_EXIT_EQUAL_CALL.md)。

**仍是分支专用 END None，尚未消费抽象 sched no-op，不是统一 OSIntExit/WFIFun。** 限定 IE=false、si=nil、ISR 全清及空 LINV；移除 API 绑定的对照只检查局部入口，不是完整执行消融。强 current guard、GOOD_OS 和同程序 K1–K4 缺口保留，uCOS3 未开始。旧失败及冻结证据不改，目标 active，未提交/推送；最终实测见本步 verification.json。
<!-- equal-call-checkpoint-end -->

<!-- equal-helper-checkpoint-start -->
## 局部进展：最高优先级仍是当前任务的 helper 调用后缀

第293步从真实 helper scall 切点出发，构造全部 fresh helper 局部分配/执行/返回，合并 decoder 权限，写 target，推导优先级相等并跳过切换，退出/释放/返回后恢复原 storage RDYINV。独立非空 EH 堆与只改 current 字节的局部比较对照见[第293步中文说明](audit/STAGE293_EXIT_EQUAL_HELPER.md)。

**是分支专用 END None 的 SKIP 残余切点，不是外层完整客户端调用，也没有消费抽象 sched no-op。** 外层 saved/running/encrit/nesting/lock 前缀待接；限定 IE=false、si=nil、ISR 全清及空 LINV，强 current guard 缺口不变。局部比较对照不是完整执行消融；统一规格、WFIFun/WFInt、GOOD_OS、同程序 K1–K4 未闭合，uCOS3 未开始。旧失败和冻结证据原样保留，目标 active，未提交/推送，实测见本步 verification.json。
<!-- equal-helper-checkpoint-end -->

<!-- locked-call-checkpoint-start -->
## 局部进展：调度锁非零时的完整客户端调用

第292步覆盖 running=1、nesting=0..255、lock=1..255：构造全部 saved 分配/初始化，真实临界区、饱和递减与双 guard、退出/释放/返回；后置仍为原 storage 家族 RDYINV。独立非空 LC 堆没有 helper 绑定或预分配 saved；只改单个锁字节的局部 guard 对照见[第292步中文说明](audit/STAGE292_EXIT_LOCKED_CALL.md)。

**仍是分支专用 END None，不是统一 OSIntExit/WFIFun 或整核证明。** 限定 IE=false、si=nil、ISR 全清、空 LINV；局部锁 guard 对照不是完整调用执行消融。等优先级与强 current guard 缺口保留，GOOD_OS、同程序 K1–K4 未闭合，uCOS3 未开始。旧失败和冻结证据原样保留；目标 active，未提交/推送，最终实测见本步 verification.json。
<!-- locked-call-checkpoint-end -->

<!-- quiet-call-checkpoint-start -->
## 局部进展：running=0 的不调度完整调用

第291步从相同客户端 scall 出发，构造 saved 分配/初始化、running false guard、释放及调用者恢复；不进入临界段，后置仍为原 storage 家族的 RDYINV。独立非空 QC 堆没有 helper 绑定或预分配 saved；只改单个 running 字节的局部 guard 对照见[第291步中文说明](audit/STAGE291_EXIT_QUIET_CALL.md)。

**这是分支专用 END None 规格，不是统一 OSIntExit/WFIFun 或整核证明。** 只覆盖 running=0、IE=false、si=nil、ISR 全清、空 LINV；不是 running=1 对照堆上的完整执行消融。锁阻塞、等优先级与强 current guard 缺口保留；GOOD_OS、同程序 K1–K4 未闭合，uCOS3 未开始。旧失败与第290步封存恢复证据原样保留；目标 active，未提交/推送，实测以本步 verification.json 为准。
<!-- quiet-call-checkpoint-end -->

<!-- nested-call-checkpoint-start -->
## 局部进展：嵌套未退尽时的不调度完整调用

第290步从相同客户端 scall 出发，连接 saved 分配/初始化、running、临界段、n=2..255 的递减与非零 guard，再释放并恢复返回；后置仍为原 storage 的 RDYINV。高层采用分支专用 END None，不调度。原非空 AC 堆和只省略递减的局部对照见[第290步中文说明](audit/STAGE290_EXIT_NESTED_CALL.md)。

**不是统一 OSIntExit/WFIFun 或整核证明。** 原 lock=0 所有权保留，未读 lock 或调用 helper；不把此结果推广到任意 lock/running。running=0、锁阻塞、等优先级及强 current guard 等缺口不变。局部 store/guard 对照不是完整调用执行消融。GOOD_OS、同程序 K1–K4 未闭合，uCOS3 未开始；旧失败与冻结证据保留，目标 active，未提交/推送。实测见本步 verification.json。
<!-- nested-call-checkpoint-end -->

<!-- client-call-checkpoint-start -->
## 局部进展：高低两层客户端调用已接入 API 入口证明

第289步从两层相同的 scall 起步，匹配客户端步骤，按显式 API 绑定进入高层 sched 规格，内部推导第288步完整 API-entry TaskSim；公开接口没有执行结果或下游 TaskSim 前提，后置仍为 RDYINV。非空原 AC 堆与仅删除 API 绑定的局部对照见[第289步中文说明](audit/STAGE289_EXIT_CLIENT_CALL.md)。

**只是 running=1、n=0/1、lock=0、changed 分支的客户端调用证明，不是整个 OSIntExit/WFIFun 或整核验证。** 没有修改框架 InOS 分类，也不改写第288步的未通过主门槛。一般 nesting、等优先级、强 current guard 等缺口不变；局部入口对照不是完整执行消融。GOOD_OS、同程序 K1–K4 未闭合，uCOS3 未开始；旧失败保留，目标 active，未提交/推送。实测见本步 verification.json。
<!-- client-call-checkpoint-end -->

<!-- active-api-entry-checkpoint-start -->
## 局部进展：saved 初始化与 running 判断已接入 API 入口

第288步从既有边界归一化 AST 的 sfexec 起步，覆盖全部 fresh Tint32 局部分配，构造 saved 写零与 running 判断，再连接第287步临界/helper/切换返回后缀。独立非空堆无需预分配 saved，固定 scheduler spec，后置为 RDYINV；另有同堆省略初始化的局部对照。见[第288步中文说明](audit/STAGE288_EXIT_ACTIVE_CALL.md)。

**原计划 scall 主门槛未完成，不能将 API 入口当作客户端完整调用。** 已证明具体客户端入口不属于 InOS，未加入矛盾前提。下一步需高低层客户端调用组合；一般 nesting、等优先级、强 current guard 等缺口不变。GOOD_OS、同程序 K1–K4 未闭合，uCOS3 未开始；旧失败与冻结证据保留，目标 active，未提交/推送。实测以本步 verification.json 为准。
<!-- active-api-entry-checkpoint-end -->

<!-- guard-helper-checkpoint-start -->
## 局部进展：原临界代码已接通 helper 与切换后缀

第287步将真实 encrit、n=0/1 递减与双 guard 接到第285步 helper/目标更新/切换后缀，消去 dispatch TaskSim continuation 前提。guard 完整所有权进入 storage；非空完整 decoder/guard 堆实例固定真实 scheduler spec，后置为 RDYINV。见[第287步中文说明](audit/STAGE287_GUARD_HELPER.md)。

**仍不是原完整活跃调用入口。** 外层 saved/running/call 与等优先级、一般 nesting 分支待接；局部权限对照不是完整执行消融。si=nil、ISR 全清、空 LINV、强 current guard 缺口及 ADR-0010 不变。GOOD_OS、同程序 K1–K4 未闭合，uCOS3 未开始；保留旧失败，目标 active，未提交/推送。实测见本步 verification.json。
<!-- guard-helper-checkpoint-end -->

<!-- critical-prefix-checkpoint-start -->
## 局部进展：临界原语与 nesting/lock 前缀已接入 TaskSim

第286步证明真实框架 encrit 的七类模拟义务：保持内存并压入 false；随后从 typed owned 字节构造 n=0/1 的饱和递减与双 guard。非空 synthetic sret 实例及只删除递减的同堆局部执行对照见[第286步中文说明](audit/STAGE286_CRITICAL_PREFIX.md)。

**显式保留 dispatch TaskSim continuation，尚未与第285步 helper 后缀整合，不是原完整函数入口。** synthetic 实例的 Post=True 不证明内核后置性质；局部消融不算完整调用消融。GOOD_OS、同程序 K1–K4 未闭合，uCOS3 未开始；si=nil、ISR 全清、空 LINV、强 current guard 缺口及 ADR-0010 不变。旧失败和证据保留，目标 active，未提交/推送；实测见本步 verification.json。
<!-- critical-prefix-checkpoint-end -->

<!-- helper-target-checkpoint-start -->
## 局部进展：helper 调用已接上目标赋值与需要切换的后缀

第285步消去第284步恢复后 caller TaskSim 前提：从真实 helper 调用切点，连接目标指针赋值、比较、计数及已有 handoff/switch/返回后缀。unmap 表保留另一半权限，返回后合并完整 storage；非空切点实例与局部权限对照见[第285步中文说明](audit/STAGE285_HELPER_TARGET.md)。

**不是原完整活跃调用入口可达性或等优先级分支证明。** 旧 trace 只有半份 unmap，新实例不冒充旧堆；外层完整表权限与 guards 待接。GOOD_OS、同程序 K1–K4 未闭合，uCOS3 未开始；si=nil、ISR 全清、空 LINV、强 current guard 缺口及 ADR-0010 边界不变。保留旧失败，目标 active，未提交/推送；实测以本步 verification.json 为准。
<!-- helper-target-checkpoint-end -->

<!-- helper-body-checkpoint-start -->
## 局部进展：原 helper 两赋值、释放与调用已接入 TaskSim

第284步将原 OS_SchedNew 两个赋值的求值/写入、真实局部释放与返回接到 TaskSim，并覆盖全部 fresh 分配后继；公开接口不再要求函数体 TaskSim，只保留恢复后 caller continuation。任意 fresh raw Vundef 局部的原函数体非空实例，以及只省略 high 赋值、其余步骤和输入不变的执行对照见[第284步中文说明](audit/STAGE284_HELPER_BODY.md)。

**仍不是完整外层活跃调用入口 TaskSim 或无条件 WFIFun。** 非空实例只覆盖原函数体；对照不冒充外层完整执行消融。GOOD_OS、同程序 K1–K4 未闭合，uCOS3 未开始。旧失败与冻结证据保留，目标 active，未提交/推送；实测以本步 verification.json 为准。
<!-- helper-body-checkpoint-end -->

<!-- helper-return-checkpoint-start -->
## 局部进展：helper 字节释放与返回已接入 TaskSim

第283步从局部字节所有权推导真实 free，在任意兼容 frame 下保留其他资源，并恢复调用者环境。唯一公开接口只保留恢复后的 caller continuation TaskSim；独立非空资源实例与物理堆选址消除控制见[第283步中文说明](audit/STAGE283_HELPER_RETURN.md)。

**仍不是完整 helper 或调用入口证明。** 第282步的函数体前提未消去，两个原赋值的 TaskSim 待连接；raw 返回非空实例不是原完整活跃调用可达性，写入后堆控制不冒充原函数体执行消融。GOOD_OS、同程序 K1–K4 未闭合，uCOS3 未开始。旧失败保留，目标 active，未提交/推送。
<!-- helper-return-checkpoint-end -->

<!-- helper-allocation-checkpoint-start -->
## 局部进展：helper 调用前缀覆盖所有合法局部分配

第282步连接真实 OS_SchedNew 无参调用、环境切换、单字节局部分配和原函数体入口。新桥从实际总堆后继分离 frame，覆盖全部 fresh block；独立反例证明单一固定选址无法覆盖真实分配。见[第282步中文说明](audit/STAGE282_HELPER_ALLOCATION.md)。

**公开接口仍要求每个合法选址后的函数体 TaskSim，不是完整 helper 或完整调用入口证明。** 尚未消去该前提，未连接第281步目标赋值；原活跃调用的非空入口 TaskSim 未建立。GOOD_OS、同程序 K1–K4 未闭合，uCOS3 未开始。旧失败保留，目标 active；没有提交/推送。
<!-- helper-allocation-checkpoint-end -->

<!-- target-tasksim-checkpoint-start -->
## 局部进展：目标指针赋值已接入原 TaskSim

第281步从 ready invariant 与抽象任务映射推导真实数组读取，再由目标单元所有权构造写入，接上比较/计数/handoff/switch。原完整分配调用实际到达赋值前切点，并在同一堆构造 TaskSim 分区；仅删除赋值的局部对照保持旧目标 Waiting，正常赋值改为 Ready，计数与其他块不变。见[第281步中文说明](audit/STAGE281_TARGET_TASKSIM.md)，实测以本步 verification.json 为准。

**不是完整调用入口 TaskSim，GOOD_OS 与同程序 K1–K4 未闭合，uCOS3 未开始。** helper/外层 guard 与等分支完整资源返回待接；si=nil、ISR 全清、空 LINV、ADR-0010 和强 current guard 缺口不变。局部消融不算完整调用消融，storage 列表置换等价未证明。保留旧失败，目标 active，未提交/推送。
<!-- target-tasksim-checkpoint-end -->

<!-- exit-changed-tasksim-checkpoint-start -->
## 局部进展：比较和切换计数已接入原 TaskSim

第280步把279的 handoff 模拟前推到优先级比较：从资源构造真实计数 store，覆盖任意32位计数值；同一完整分配调用到达的比较堆提供非空 TaskSim 分区。真实回绕与删除 increment 的同堆局部执行消融、等优先级跳过计数控制均已补齐。见[第280步中文说明](audit/STAGE280_EXIT_CHANGED_TASKSIM.md)，最终核查数据见本步 verification.json。

**不是完整调用入口 TaskSim，GOOD_OS 与同程序 K1–K4 未闭合，uCOS3 未开始。** 调度 helper/外层 guard 仍只有 trace、等分支完整返回模拟待接；si=nil、ISR 全清、空 LINV、ADR-0010、强 current guard 缺口不变。不把局部后缀消融算作完整程序消融；storage 列表置换等价未证明。保留所有旧失败，目标 active，未提交/推送。
<!-- exit-changed-tasksim-checkpoint-end -->

<!-- handoff-tasksim-checkpoint-start -->
## 局部进展：弱 storage TaskSim 前推至缓存复制入口

第279步把278的 switch 结论沿缓存复制的七个 C 语义小步前推，公开接口由所有权构造 store，不要求执行/TaskSim 结果；同一完整分配调用实际达到的 handoff 状态提供非空见证，saved(bs) 私有、saved98 与 RCframe 外部。见[第279步中文说明](audit/STAGE279_HANDOFF_TASKSIM.md)。

**仅 ADR-0010 已接受调用点解释中的 handoff 起点，不是完整调用入口 TaskSim，也不是原外部端口 refinement。** storage 列表换序是既有 Inv 家族的布局实例，未证明与278列表置换等价；cache=4、旧任务 blocked 的强 guard 缺口保留。保存区逻辑拒绝不是完整执行消融；ISR 全清、si=nil、空 LINV 限制不变。GOOD_OS、同程序 K1–K4 未闭合，uCOS3 未开始；目标 active，未提交/推送。旧失败保留，实测见本步 verification.json。
<!-- handoff-tasksim-checkpoint-end -->

<!-- storage-switch-tasksim-checkpoint-start -->
## 局部进展：实际旧任务 switch 的弱 storage TaskSim

第278步连接原 switch 的七类 TaskSim 义务：在同一共享子堆建立 SWINVt 与 SWPRE_NDEAD，saved(bs) 保留私有，交出共享资源后，对任意兼容归还资源复用277的双栈顶 pending 返回桥。276完整调用实际达到的旧任务切出堆提供非空见证，saved98 与 RCframe 保持外部。见[第278步中文说明](audit/STAGE278_STORAGE_SWITCH_TASKSIM.md)。

**是实际达到的原 switch 切出点 TaskSim，不是完整调用入口 TaskSim，也不是旧任务全局切回可达性。** 原共享资源归还仅提供一个兼容 callback 实例；旧任务仍 blocked、cache=4，强 current guard 缺口不变。保存区逻辑拒绝不是完整单因素执行消融；ISR 全清、si=nil、空 LINV、ADR-0010 不变。GOOD_OS、同程序 K1–K4 未闭合，uCOS3 未开始，目标保持 active；未提交/推送。旧失败及本步测试字面量修正前的失败均保留，实测见本步 verification.json。
<!-- storage-switch-tasksim-checkpoint-end -->

<!-- invariant-pending-checkpoint-start -->
## 局部进展：弱 storage 的 pending 返回 TaskSim

第277步抽取不变式无关的真实返回步骤，以同一套 suffix 支持保存栈顶 false/true，并实例化既有弱 storage 与强 current。旧任务实际切出堆可分离 saved(bs) 私有资源与外部 saved98/RCframe，得到弱 pending callback 的非空见证；没有把 TaskSim/执行/free 结果作为生产公开前提。见[第277步中文说明](audit/STAGE277_INVARIANT_PENDING_TASKSIM.md)。

**不是原 switch 的完整恢复义务或完整入口 TaskSim，更不是整核证明。** true 为同堆快照控制，不是旧任务全局切回可达性；cache=4 而旧任务 blocked 的强 guard 缺口仍保留。保存区必要性拒绝不冒充完整单因素执行消融。ISR 全清、si=nil、空目标 LINV、ADR-0010 不变；GOOD_OS、同程序 K1–K4 未闭合，uCOS3 未开始，未提交/推送。旧失败保留，实测以本步 verification.json 为准。
<!-- invariant-pending-checkpoint-end -->

<!-- old-switch-packet-checkpoint-start -->
## 局部进展：真实旧任务切出点的共享 SWPRE

第276步从原完整活跃调用达到的旧任务 switch 状态，在同一共享子堆同时构造弱 storage SWINVt 与 SWPRE_NDEAD：saved(bs) 留旧任务，目标 saved98 与 RCframe 保持外部。一般接口只用真实目标读取、任务映射与最高 ready 条件，不把执行/TaskSim 当生产前提。见[第276步中文说明](audit/STAGE276_OLD_SWITCH_PACKET.md)。

**不是第275步强 current 前提的入口见证，也不是完整入口 TaskSim。** 同一达到堆仍证明 cache=4 而旧任务 blocked，强 guard 拒绝。必要条件拒绝控制不冒充逐项非空反模型或完整执行消融。GOOD_OS、同程序 K1–K4 未闭合，uCOS3 未开始；ISR 全清、si=nil、ADR-0010 不变，未提交/推送。旧失败保留，实测以本步 verification.json 为准。
<!-- old-switch-packet-checkpoint-end -->

<!-- switch-return-tasksim-checkpoint-start -->
## 局部进展：切换边界 TaskSim 与任意兼容共享资源上的恢复

第275步直接构造原 TaskSim 的 switch 恢复义务：saved 留在旧任务，交出共享 SWINVt；任意兼容 Mc'/Oc' 归还后，匹配真实高层 done 步，再执行两栈顶 pending 返回。见[第275步中文说明](audit/STAGE275_SWITCH_RETURN_TASKSIM.md)。

**尚未接通真实活跃切出前缀。** SWPRE 必须由上层在共享 Mc 上交付；独立非空见证仅覆盖已选目标快照的恢复资源。新反例保留“旧 current=blocked、cache 已复制为4”时强 current guard 不成立的连接缺口，不用新任务返回替代旧任务切回。ISR 全清、si=nil、空 LINV、ADR-0010 不变。GOOD_OS、同程序 K1–K4 未闭合，uCOS3 未开始，未提交／推送。旧失败保留，实测以本步 verification.json 为准。
<!-- switch-return-tasksim-checkpoint-end -->

<!-- enabled-pending-tasksim-checkpoint-start -->
## 局部进展：IE=true 的 pending 返回资源交接与原 TaskSim

第274步补齐保存栈顶 true 分支：excrit 保持总堆与总抽象状态不变，将 Core 从任务转交共享 INV；后续 sret/free/caller 只由任务拥有 saved 与 CurTid，并量化任意兼容共享堆及外部 frame。见[第274步中文说明](audit/STAGE274_ENABLED_PENDING_TASKSIM.md)。

**true 独立实例是同一达到堆上的栈顶快照控制，不是原完整入口的 true 可达性证明。** ISR 全清、si=nil、空目标 LINV、已有 pending；原任务仍 blocked，ADR-0010 不变。不是切换前 TaskSim、任意中断交错或整核 GOOD_OS；同程序 K1–K4 未闭合，uCOS3 未开始，未提交／推送。旧证据及失败保留，实测以本步 verification.json 为准。
<!-- enabled-pending-tasksim-checkpoint-end -->

<!-- pending-return-tasksim-checkpoint-start -->
## 局部进展：目标 pending 返回前接入原 TaskSim

第273步从切换后目标已有 pending 的 SKIP/excrit 开始，连接 sret、目标保存区真实释放及原 caller，建立原 TaskSim。量化任意可分离外部 frame，独占 saved98，不把 whole-heap free 当作任务所有权；复用同一完整调用实际到达堆并构造非空前提见证。见[第273步中文说明](audit/STAGE273_PENDING_RETURN_TASKSIM.md)。

**仅保存栈顶 false、si=nil、ISR 全清的路径**，空目标 LINV；IE=true 资源交接尚未证明，栈顶/所有权边界不冒充完整路径覆盖。原任务仍 blocked，pending 已存在、typed 非初始化、ADR-0010 不变。不是切换前 TaskSim、任意交错或整核 GOOD_OS；同程序 K1–K4 未闭合，uCOS3 未开始，未提交／推送。旧失败及冻结材料保留，实测以本步 verification.json 为准。
<!-- pending-return-tasksim-checkpoint-end -->

<!-- return-client-tasksim-checkpoint-start -->
## 局部进展：真实返回状态接入原框架 TaskSim

第272步从271同一返回资源分离，建立共享 INV、目标 RDYINV/LINV 与外部 frame 的精确分区，并构造既有有限 client 家族的原 TaskSim；不要求 InitTaskSt，不重置实际 IE/保存栈。同一完整调用的实际终止 caller 及同达到堆栈顶双执行均交付该端点 TaskSim。见[第272步中文说明](audit/STAGE272_RETURN_CLIENT_TASKSIM.md)。

**只覆盖返回后的有限 client，不是 pending 返回之前或整核模拟。** 实例沿用空局部候选；旧 saved/RCframe 仍外部，不转给目标。原任务仍 blocked，目标 pending 已存在、typed 非初始化、ADR-0010 不变。GOOD_OS、任意交错、同程序 K1–K4 未闭合；uCOS3 未开始，未提交／推送。旧失败不改，实测以本步 verification.json 为准。
<!-- return-client-tasksim-checkpoint-end -->

<!-- return-invariant-split-checkpoint-start -->
## 局部进展：实际返回资源分离为原框架 INV 与 RDYINV

第271步把270的返回共享 core、CurTid 与完整 frame，按恢复 IE 分离为同一个既有 INV 与 RDYINV。IE=true 时 core 属于 INV；IE=false 时 core 属于 RDYINV，不重复所有权。复用同完整调用及同达到堆保存栈双执行，两支均交付该分离。见[第271步中文说明](audit/STAGE271_RETURN_INVARIANT_SPLIT.md)。

**是候选不变式的端点资源分离，不是整核 Inv 保持。** ISR 位全 false；仅 IE=false 要求 top<=INUM。原任务仍 blocked；目标 pending 已存在、typed 非初始化、frame 非 LINV。尚非 TaskSim/任意交错、GOOD_OS、同程序 K1–K4；uCOS3 未开始，未提交／推送。旧证据不改，实测以本步 verification.json 为准。
<!-- return-invariant-split-checkpoint-end -->

<!-- shared-switch-return-checkpoint-start -->
## 局部进展：共享资源贯穿实际调度切换与目标 pending 返回

第270步从切换前弱 storage 候选，接通最高 ready 目标的原 switch、共享 current 重封装及 excrit/sret/free/caller，交付不要求 IE=false 的既有共享 core、CurTid 和完整 frame。独立实例复用267同一完整调用入口；同一达到堆仅删除目标保存栈顶的实际双执行，最终物理堆与共享 core 相同，但恢复 IE 不同。见[第270步中文说明](audit/STAGE270_SHARED_SWITCH_RETURN.md)。

**不是旧任务切回的完整共享循环。** 旧任务仍 blocked，268环境切回不是调度选择；目标 pending 已存在、共同 si、typed high=88，非初始化可达。返回 core 不等于完整 Inv 或 ProgSim。GOOD_OS、WFInt、K1–K4 未闭合，uCOS3 未开始，未提交／推送。旧失败证据不改，实测见本步 verification.json。
<!-- shared-switch-return-checkpoint-end -->

<!-- exit-shared-reclose-checkpoint-start -->
## 局部进展：真实调度切换后重新封装共享资源

第269步把实际源码级 OSIntExit boundary 调用、调度、比较、计数、复制与 switch，接到现有 current 候选不变式的共享资源重封装；saved 与保留 frame 保持分离。独立实例使用非空 storage，同堆只省略复制的实际对照表明：**两条路径均可重封装，但只有复制路径缓存一致**，两项结论不混为一谈。见[第269步中文说明](audit/STAGE269_EXIT_SHARED_RECLOSE.md)。

**候选重封装不是完整 Inv 保持或整核验证。** 端点仍在 switch 后，typed high=88 不是初始化可达证据；未与268切回闭成共享 Inv 循环。GOOD_OS、WFInt、K1–K4 未闭合，uCOS3 未开始，未提交／推送。旧代码、反例、测试和冻结证据不改；本步实测以 verification.json 为准。
<!-- exit-shared-reclose-checkpoint-end -->

<!-- active-call-return-checkpoint-start -->
## 局部进展：旧任务从真实分配入口切出，再显式切回并释放返回

第268步新增原 OSIntExit 两个 kseq 续体的生产切回适配器。在独立双任务实例中，从 sfexec 与 fresh saved 分配开始，执行完整活跃路径、第一次切换、环境读取 table[6] 并切回，随后释放同一次分配的旧任务保存区、恢复 caller。另有同堆仅删除保存栈顶的真实双执行，恢复不同 IE。见[第268步中文说明](audit/STAGE268_ACTIVE_CALL_RETURN.md)。

**环境任务不是实际调度器，切回不是公平性保证。** 初态不同于267，不继承其同入口 ProgSim；A仍抽象 blocked，cache未恢复，IE=false、high=88，不是 full Inv/初始化可达。GOOD_OS、WFInt、K1–K4 未闭合，uCOS3 未开始，未提交／推送。本步只新增一个生产接口及其登记，旧失败/证据不改；实测见 verification.json。
<!-- active-call-return-checkpoint-end -->

<!-- active-call-trace-checkpoint-start -->
## 局部进展：同入口活跃调用的实际有限执行与挂起资源

第267步在第266步同一 FWtasks/FWos 入口上，新增原框架有限全局执行：sfexec、任意给定 fresh saved 分配、完整活跃路径、实际 switch、目标已有 pending 返回和释放；同时成立原 ProgSim。目标保存区释放，切出任务保存区、环境、临界栈与 pending 保留。见[第267步中文说明](audit/STAGE267_ACTIVE_CALL_TRACE.md)。

**这是特定 typed 双任务路径，不是整核验证。** 目标 pending 已存在，切出任务未恢复；IE=false，high=88 不是完整 Inv/初始化可达。GOOD_OS、WFInt、K1–K4 未闭合，uCOS3 未开始，未提交／推送。本步不改生产证明或工程登记；实测以 verification.json 为准，旧失败证据保留。
<!-- active-call-trace-checkpoint-end -->

<!-- active-call-witness-checkpoint-start -->
## 局部进展：完整活跃 OSIntExit 调用的同堆独立实例

第266步从 sfexec 入口接通任意 fresh saved 分配、running/encrit/nesting、完整调度与目标已有 pending 返回。主定理没有 ProgSim 前提；资源均在同一物理堆链上构造，并证明入口条件可满足。见[第266步中文说明](audit/STAGE266_ACTIVE_CALL_WITNESS.md)。

**这是特定活跃路径实例，不是所有路径或整核验证。** 目标 pending 已存在，切出任务仍挂起；IE=false，typed high=88 不是完整 Inv/初始化可达。GOOD_OS、WFInt、K1–K4 未闭合，uCOS3 未开始，未提交／推送。旧生产证明、工程登记、测试及冻结证据不改；本步实测见 verification.json，不沿用历史通过状态。
<!-- active-call-witness-checkpoint-end -->

<!-- exit-active-call-progsim-checkpoint-start -->
## 局部进展：完整活跃 OSIntExit 调用的条件模拟接口

第265步把 sfexec/scall 查找、任意 fresh saved 分配、初始化、running=true、encrit 和 nesting/lock 守卫，接到既有完整 dispatch 与目标已有 pending 返回；主接口仅保留最终 caller 模拟，不再公开中间模拟。见[第265步中文说明](audit/STAGE265_EXIT_ACTIVE_CALL_PROGSIM.md)。

**生产条件接口不是独立完整调用见证。** 独立核查覆盖任意 fresh 分配/初始化/目标saved不别名，以及同堆仅改nesting的实际分支对照；不能拼接成完整全局调用实例。目标 pending 已存在，切出任务仍挂起；IE=false，沿用 ADR-0005/0010。typed high=88 不是完整 Inv/初始化可达。GOOD_OS、WFInt、K1–K4 未闭合，uCOS3 未开始，未提交／推送。旧证明和失败不改；新增工程登记的旧身份门差分如实保留，实测见 verification.json。
<!-- exit-active-call-progsim-checkpoint-end -->

<!-- dispatch-resume-witness-checkpoint-start -->
## 局部进展：完整内层调度前缀与目标 pending 返回的独立实例

第264步直接实例化既有生产接口，不新增冗余生产封装。在同一 typed 非空堆上，从 OS_SchedNew 调用前接通目标指针更新、实际比较、计数回绕、优先级复制、switch、目标 pending 的 excrit/sret/free/caller；同时证明原有限全局执行与无 ProgSim 前提的原 ProgSim。见[第264步中文说明](audit/STAGE264_DISPATCH_RESUME_WITNESS.md)。

**这是完整内层 dispatch，不是完整 OSIntExit 函数调用。** 目标 pending 已存在，当前任务环境为空、切出任务仍挂起；尚未接入外层 saved 分配、running、encrit 与 nesting。IE=false、目标栈顶=false，沿用 ADR-0005/0010；high=88 不是完整 Inv 或初始化可达证据。GOOD_OS、WFInt、K1–K4 未闭合，uCOS3 未开始，未提交／推送。旧证明与失败证据保留，实测见本步 verification.json。
<!-- dispatch-resume-witness-checkpoint-end -->

<!-- resumed-return-progsim-checkpoint-start -->
## 局部进展：切换至已有 pending 续体后接通退出临界区与返回

第263步把原 switch、目标任务已保存的 OSIntExit pending 续体、excrit、sret、局部释放与 caller 恢复连接到原 ProgSim。生产调度调用接口只要求最终 caller 模拟，不再要求 switch 后的中间模拟；独立双任务 typed 实例在同一物理堆上同时证明实际有限执行与原 ProgSim，且没有 ProgSim 前提。见[第263步中文说明](audit/STAGE263_RESUMED_RETURN_PROGSIM.md)。

**pending 必须已经存在；切出任务仍挂起，最终 caller 端点模拟仍是生产条件。** 独立实例从物理 switch 开始，不是完整 OSIntExit 调用实例。IE=false、保存栈顶=false，沿用 ADR-0005/0010；high=88 不是完整 Inv 或初始化可达。不是完整中断返回、WFInt 或 GOOD_OS。K1–K4 未闭合，uCOS3 未开始，未提交／推送。实测见本步 verification.json，下方历史原文不变。
<!-- resumed-return-progsim-checkpoint-end -->

<!-- exit-quiet-call-progsim-checkpoint-start -->
## 局部进展：完整非调度函数路径连接分配、初始化、running 与返回

第262步把实际 OSIntExit 归一化函数的 sfexec 查找、任意 fresh Tint32 分配、saved 初始化、running 判断与已证 quiet 返回接到原 ProgSim。停止／运行两个非空 typed 独立实例无 ProgSim 前提，单字节对照得到 nesting 保持2／减至1；释放后的完整堆不依赖分配选择。见[第262步中文说明](audit/STAGE262_EXIT_QUIET_CALL_PROGSIM.md)。

**生产最终 caller 端点模拟仍是公开条件。** 原 InOS 限制保留：独立实例从 sfexec 开始，scall 只在已有 OS caller 上下文中覆盖；不是任意 client 调用桥接。IE=false，沿用 ADR-0005/0010，typed high=88 不是完整 Inv 或初始化证据。调度后旧任务恢复未闭合；不是所有路径 OSIntExit、完整中断返回、WFInt 或 GOOD_OS。K1–K4 未闭合，uCOS3 未开始，未提交／推送。实测见本步 verification.json，下方历史原文不变。
<!-- exit-quiet-call-progsim-checkpoint-end -->

<!-- critical-return-progsim-checkpoint-start -->
## 局部进展：非调度临界区已连接实际返回、释放与 caller 恢复

第261步在原 ProgSim 上接通 encrit、实际 nesting/lock 禁用分支、excrit、sret、Tint32 局部释放和 caller 环境恢复；独立 typed 非空实例没有 ProgSim 前提。原语栈顶改变／空栈对照检查实际恢复和异常，而非只做语法拒绝。见[第261步中文说明](audit/STAGE261_CRITICAL_RETURN_PROGSIM.md)。

**生产最终 caller 端点模拟仍是公开前提。** 入口 IE=false，沿用 ADR-0005/0010；实例为终止 caller，typed high=88 不是完整 Inv 或初始化可达证据。调度切换后的旧任务仍可能挂起；不是完整 OSIntExit／中断返回、任意 client、WFInt 或 GOOD_OS。K1–K4 未闭合，uCOS3 未开始，未提交／推送。实测与原失败差分见本步 verification.json，下方历史原文不变。
<!-- critical-return-progsim-checkpoint-end -->

<!-- exit-nesting-progsim-checkpoint-start -->
## 局部进展：实际 nesting／lock 分支接到内层调度模拟

第260步将原 OSIntExit 的饱和减一和更新后 nesting／lock 判断接到第259步实际调用至 switch 的 ProgSim；不再要求内层调度入口模拟。生产覆盖全部字节 nesting，独立 typed 实例从1减至0后恢复整个原堆，并无 ProgSim 前提地连接实际调度与有限 client。见[第260步中文说明](audit/STAGE260_EXIT_NESTING_PROGSIM.md)。

**最终端点模拟与高层匹配仍是生产前提。** IE=false、沿用 ADR-0010；禁用分支仍要求调用方端点，typed high=88 不是初始化可达或完整 Inv。不是完整 OSIntExit／中断返回、任意 client、WFInt 或 GOOD_OS；K1–K4 未闭合，uCOS3 未开始，未提交／推送。实测见本步 verification.json，下方历史原文不变。
<!-- exit-nesting-progsim-checkpoint-end -->

<!-- exit-call-dispatch-progsim-checkpoint-start -->
## 局部检查点：真实调度调用、目标指针更新与内层切换模拟接通

第259步把 OS_SchedNew 的完整实际调用与 OSTCBHighRdy 指针更新接到既有比较、计数、复制和 switch，消除了调用返回点的中间 ProgSim 前提。同一原始 typed 堆上的独立有限 client 实例没有 ProgSim 前提；两种分支均有生产条件接口。见[第259步中文说明](audit/STAGE259_EXIT_CALL_DISPATCH_PROGSIM.md)。

**最终端点模拟与高层匹配仍是生产前提。** IE=false，沿用 ADR-0010；typed 实例不是初始化可达或完整 Inv 证据，相等分支尚无独立完整调用实例。不是完整 OSIntExit／OS_Sched／中断返回、任意 client、WFInt 或 GOOD_OS。K1–K4 未闭合，uCOS3 未开始，未提交／推送；实测及旧失败精确差分见本步 verification.json，下方历史原文不变。
<!-- exit-call-dispatch-progsim-checkpoint-end -->

<!-- sched-call-progsim-checkpoint-start -->
## 局部检查点：OS_SchedNew 实际函数体、释放和返回已接入原 ProgSim

第258步把所有合法新鲜局部块上的两次赋值、sret/free 和 caller 恢复接入原模拟，完整调用定理不再要求任意新鲜块上的函数体模拟，只要求返回后的 caller 后续模拟。独立 typed 实例对任意 fresh 块执行完整调用，释放后完整堆不依赖分配选择。见[第258步中文说明](audit/STAGE258_SCHED_CALL_PROGSIM.md)。

**caller 后续模拟仍是公开条件。** IE=false；不是完整 OS_Sched／OSIntExit／中断返回、任意 client、WFInt 或 GOOD_OS。K1–K4 未闭合，uCOS3 未开始。实测与旧失败差分见本步 verification.json；原证据保留，未提交／推送。下方历史原文保持不变。
<!-- sched-call-progsim-checkpoint-end -->

<!-- sched-call-entry-progsim-checkpoint-start -->
## 局部检查点：调度调用入口覆盖所有合法分配后继

第257步在原 `ProgSim` 层连接 OS_SchedNew 的调用、局部环境清空、字节分配和实际函数体入口。后续条件按所有合法新鲜块量化；同堆双分配对照证明后继不唯一，不能套用唯一后继助手。见[第257步中文说明](audit/STAGE257_SCHED_CALL_ENTRY_PROGSIM.md)。

**任意新鲜局部块上的函数体后续模拟尚未独立建立。** IE=false，不是完整调度调用／中断返回、任意 client、WFInt 或 GOOD_OS；K1–K4 未闭合，uCOS3 未开始。旧证明、测试和冻结失败保留；实测见本步 verification.json。未提交／推送，下方历史原文不变。
<!-- sched-call-entry-progsim-checkpoint-end -->

<!-- exit-dispatch-progsim-checkpoint-start -->
## 局部检查点：实际比较与计数接通复制至切换模拟

第256步把原 `ProgSim` 的起点推进到 OSIntExit 优先级比较，接通 UINT32 计数增量、skip、复制及原 switch；相等分支另有接口。typed 实例由真实调度前缀构造，计数从 mone 回绕到 0，不复用已增量的端点。见[第256步中文说明](audit/STAGE256_EXIT_DISPATCH_PROGSIM.md)。

**生产仍显式要求高层匹配与后续模拟，区间中断关闭。** 调度调用的全局模拟、局部环境变化和完整中断返回尚未接通；不是任意 client、WFInt 或 GOOD_OS。旧中间 guard 拒绝和原失败保留；K1–K4 未闭合，uCOS3 未开始。验证见本步 verification.json；未提交／推送，下方历史原文不变。
<!-- exit-dispatch-progsim-checkpoint-end -->

<!-- handoff-progsim-checkpoint-start -->
## 局部检查点：同一续体上的完整复制至切换模拟

第255步在原 `ProgSim` 层连接优先级复制的七个微步与原 switch，逐步覆盖全部后继、输出和异常分支。typed 非空实例使用同一 `CGpending ## CGouter`，切换目标仍有两条 skip 待执行；有限 client 的后续模拟独立建立。见[第255步中文说明](audit/STAGE255_HANDOFF_PROGSIM.md)。

**生产接口仍显式要求高层匹配与后续 ProgSim，且区间中断关闭。** 不是任意 client、完整中断返回、WFInt 或 GOOD_OS；不修改原不变量或框架规则。旧 guard 中间态拒绝、高层 current 更新及 IE 单因素对照保留；K1–K4 未闭合，uCOS3 未开始。旧失败不改，实测见本步 verification.json。未提交／推送，下方历史原文不变。
<!-- handoff-progsim-checkpoint-end -->

<!-- nonterminal-saved-contract-checkpoint-start -->
## 局部检查点：独立建立未结束 client 的恢复契约

第254步对原两条 skip 序列独立证明 InitTaskSt、目标私有 LINV、CurLINV 和 TaskSim，保留原 task_sim 全部七项义务；在真实 typed 复制／切换见证上，不再假设该有限 client 的 saved TaskSim。见[第254步中文说明](audit/STAGE254_NONTERMINAL_SAVED_CONTRACT.md)。

**仅覆盖该有限纯 client，目标为初始形状 true/nil/nil。** 非空中断栈／临界区栈不能冒充 InitTaskSt；任意暂停 client、完整全局返回、WFInt 和 GOOD_OS 均未闭合，K1–K4 未闭合，uCOS3 未开始。旧失败保留；实际验证见本步 verification.json。未提交／推送，下方历史原文不变。
<!-- nonterminal-saved-contract-checkpoint-end -->

<!-- current-ready-resume-checkpoint-start -->
## 局部检查点：切换后的就绪资源转移与恢复契约

第253步复用原 `swi_rdy_inv'`，在新 GHinv 下证明切换后的 INV/RDYINV 资源重分配，保持物理／抽象总资源及私有 frame。目标代码与中断开关不再要求已终止／关闭；typed 同堆见证包含未结束任务、中断开启及非空合法中断栈。见[第253步中文说明](audit/STAGE253_CURRENT_READY_RESUME.md)。

**暂停任务的 TaskSim 恢复契约仍是显式前提，尚未独立建立。** 不是任意 client、完整复制至返回链、WFInt 或 GOOD_OS；K1–K4 未闭合，uCOS3 未开始。旧源码、证明、测试及失败不改；验证结果见本步 verification.json。未提交／推送，下方历史原文不变。
<!-- current-ready-resume-checkpoint-end -->

<!-- switch-semantic-bridge-checkpoint-start -->
## 局部检查点：原物理 switch 的 ProgSim 桥

第252步直接在框架原 `ProgSim` 层证明 switch：穷尽全部后继，另证 progress、无输出和无异常；高层匹配及后续模拟显式保留。第251步真实复制后的同一 typed 堆上，原 guard 仍拒绝，但经真实 sched 切换可建立非空有限上下文模拟；省略高层当前任务更新的对照被拒绝。见[第252步中文说明](audit/STAGE252_SWITCH_SEMANTIC_BRIDGE.md)。

**新任务已终止且中断关闭；不是任意 client 或完整复制至返回链。** 未迁移 Exit/Sched 环境，不是 WFInt／GOOD_OS，K1–K4 未闭合，uCOS3 未开始。C/config/AST/framework 与旧 Inv/LI/BDspec 不改，原失败保留；实测见本步 verification.json。未提交／推送，下方历史原文不变。
<!-- switch-semantic-bridge-checkpoint-end -->

<!-- current-guard-handoff-checkpoint-start -->
## 局部检查点：Exit 真实赋值前缀与切换前闭合障碍

第251步在任意 ambient Inv 下证明实际计数增量／skip／当前优先级复制前缀，并实例化新候选。typed 真实复制后，旧 Inv 仍可关闭，新候选在任意分离 frame 下均不可关闭；物理 switch 后新候选又成立。障碍是复制与抽象切换之间的瞬态，不是 GoodI 或资源拆分失败。见[第251步中文说明](audit/STAGE251_CURRENT_GUARD_HANDOFF.md)。

**没有完成 Exit/Sched 环境迁移。** 反驳的是当前 typed 中间态的 switch_rule 闭合前提，不是所有 InfRules 推导或初始化可达内核安全性。不是 WFInt／GOOD_OS，K1–K4 未闭合，uCOS3 未开始。固定源码与旧证据不改；验证与旧失败见本步 verification.json。未提交／推送，下方历史原文不变。
<!-- current-guard-handoff-checkpoint-end -->

<!-- current-guard-entry-checkpoint-start -->
## 局部检查点：新不变量接通实际中断入口与 OSIntEnter

第250步从新候选的实际 `BuildintPre` 直接证明 EOI → OSIntEnter，保留同堆当前优先级条件，不额外要求强 snapshot，不复制字节所有权。真实 Enter 函数环境在同一新 Inv 下成立；typed Waiting 入口非空，固定堆／frame 的单字节对照由 Coq 检查。见[第250步中文说明](audit/STAGE250_CURRENT_GUARD_ENTRY.md)。

**只完成 Enter 纵向连接，Exit/Sched 三函数环境及完整返回尚未迁移。** 不是 WFInt、初始化或 GOOD_OS；K1–K4 未闭合，uCOS3 未开始。旧失败与新增身份失败分开保留，实测见本步 verification.json。未提交／推送，下方历史原文不变。
<!-- current-guard-entry-checkpoint-end -->

<!-- switch-compatible-current-checkpoint-start -->
## 局部检查点：切换兼容的当前优先级候选

第249步新增独立不变量：原 ready/TCB/storage 资源加“当前字节关联，或当前任务已最高就绪”。完整 GoodI（含 live/deleted 切换）和 same 比较下原精确 sched 已闭合；原 typed 反例检查两分支及整个 guard 的必要性，并给出新切换后状态非空见证。见[第249步中文说明](audit/STAGE249_SWITCH_COMPATIBLE_CURRENT.md)。

**尚未迁移函数 Hoare 到新候选 Inv。** 旧活动 Inv/LI/BDspec 不改；不是全部 builders、WFInt、初始化或 GOOD_OS。K1–K4 未闭合，uCOS3 未开始。全仓旧失败保留，新增身份失败单列，实测以本步 verification.json 为准。未提交／推送，下方历史原文不变。
<!-- switch-compatible-current-checkpoint-end -->

<!-- quiet-builder-return-checkpoint-start -->
## 局部检查点：实际 builder 的非调度完整中断返回

第248步从实际 `BuildintPre` 与同堆控制字节过滤的普通合取出发，在原 bound LI/Inv/BDspec 下连接 EOI/Enter/Exit/exint。去掉原计数必须恢复的限制，255入口返回254；typed 非空、单字节对照和调度入口拒绝均由 Coq 检查。见[第248步中文说明](audit/STAGE248_QUIET_BUILDER_RETURN.md)。

**仍限 quiet/spec_done 和 all-clear 返回边界。** 不是 WFInt、启动可达或 GOOD_OS；当前优先级关联障碍及 K1–K4 未闭合，uCOS3 未开始。新生产模块注册到 `_CoqProject`，旧测试/证据不改，新增身份失败与旧失败分别记录；以本步 verification.json 为准。未提交／推送，下方历史原文不变。
<!-- quiet-builder-return-checkpoint-end -->

<!-- current-switch-obstruction-checkpoint-start -->
## 局部检查点：全程当前优先级关联与切换闭包不相容

第247步通过非空 typed 入口和真实 GoodI 第三子句证明：若候选保留旧关联正确的 Waiting 入口，且所有 SWINVt 都蕴含当前任务／优先级关联，它就不满足 GoodI。原 PPinv 的 GoodI 正对照仍成立。见[第247步中文说明](audit/STAGE247_CURRENT_SWITCH_OBSTRUCTION.md)。

**不能仅补全程等式，但并非所有可能 Inv 都不可行。** 本步不是可达漏洞、WFInt、初始化或 GOOD_OS；K1–K4 未闭合，uCOS3 未开始。旧423失败、1错误及 audit/whitespace 失败保留；实测以本步 verification.json 为准，未提交／推送，下方历史原文不变。
<!-- current-switch-obstruction-checkpoint-end -->

<!-- builder-current-counterexample-checkpoint-start -->
## 局部检查点：实际中断入口不蕴含当前优先级关联

第246步通过 typed 单字节反例确认：只把当前优先级从6写成4，修改前后都满足同一个实际 BCpre，但当前任务／优先级关联由真变假。完整内存与 frame、其它字节和抽象状态保持由 Coq 检查。见[第246步中文说明](audit/STAGE246_BUILDER_CURRENT_COUNTEREXAMPLE.md)。

**当前候选 Inv 不能直接补足第245步 same 附加条件。** 这是证明边界反例，不是可达内核漏洞；尚非所有入口、WFInt、初始化或 GOOD_OS。K1–K4 未闭合，uCOS3 未开始；旧423失败、1错误及 audit/whitespace 失败保留。实测见本步 verification.json，未提交／推送，下方历史原文不变。
<!-- builder-current-counterexample-checkpoint-end -->

<!-- common-dispatch-spec-checkpoint-start -->
## 局部检查点：changed / same 共用精确 sched 入口

第245步通过当前任务最高就绪证明和框架原生抽象调度规则，让 same 与 changed 共用 `sched;;done`，接入同一 BCintspec 的实际 builders 与原 BDspec 连续 wrapper。两分支分别有 typed 非空见证，CurTid 单因素调度适用性对照由 Coq 检查。见[第245步中文说明](audit/STAGE245_COMMON_DISPATCH_SPEC.md)。

**same 显式增加当前任务／优先级关联纯条件；quiet 尚未合并。** 仅强入口到 builder 的单向连接，不是全入口、WFInt、初始化或 GOOD_OS；K1–K4 未闭合，uCOS3 未开始。旧423失败、1错误及 audit/whitespace 失败保留，实测见本步 verification.json。未提交／推送，下方历史原文不变。
<!-- common-dispatch-spec-checkpoint-end -->

<!-- bound-dispatch-entry-checkpoint-start -->
## 局部检查点：changed 和 same 强入口接入实际 BuildintPre

第244步从原强 snapshot 的同一堆资源关闭 ready/TCB/storage Inv，证明同一 typed 状态也满足实际 bound-LI BuildintPre，并接原 BDspec 连续 wrapper。固定具体状态仅更换抽象入口的 Coq 负对照拒绝不匹配 builder，不能直接替换两种 ISR 规格。见[第244步中文说明](audit/STAGE244_BOUND_DISPATCH_ENTRY.md)。

**仅 strong snapshot 到 builder 的单向连接，不是全部入口、WFInt 或初始化可达。** 向量0与原 all-clear 连续返回边界不扩大；GOOD_OS、K1–K4 未闭合，uCOS3 未开始。旧423失败、1错误及 audit/whitespace 失败保留；实际验证见本步 verification.json。未提交／推送，下方历史原文不变。
<!-- bound-dispatch-entry-checkpoint-end -->

<!-- bound-dispatch-continuous-checkpoint-start -->
## 局部检查点：bound LocalInv 的 changed/same 连续中断返回

第243步将原 changed/same 的 EOI/Enter/dynamic Exit/exint wrapper 接到第241步同一 bound-LI 候选函数环境；只复用旧断言资源引理，不跨 LI 搬运 Hoare 结论。返回保留绑定，same 的只读半份重组后关闭原 storage Inv。见[第243步中文说明](audit/STAGE243_BOUND_DISPATCH_CONTINUOUS.md)。

**仍是条件强 snapshot，不是所有 BuildintPre、WFInt 或初始化可达。** changed 的 sched 抽象入口不同于 same/quiet，尚非统一 ISR 规格；GOOD_OS、K1–K4 未闭合，uCOS3 未开始，未提交／推送。旧423失败、1错误及 audit/whitespace 失败保留；实测见本步 verification.json，下方历史原文不变。
<!-- bound-dispatch-continuous-checkpoint-end -->

<!-- bound-quiet-continuous-checkpoint-start -->
## 局部检查点：bound LocalInv 的 quiet 连续中断返回

第242步在同一动态 Enter/Exit/Sched 候选规格下接通原 EOI/Enter/Exit/exint wrapper，返回保留地址绑定；running 拆半后重组，旧资源引理仅作断言变换，不作 LI 间 Hoare transport。typed 入口同时满足实际 BuildintPre，返回侧资源也有独立非空见证。见[第242步中文说明](audit/STAGE242_BOUND_QUIET_CONTINUOUS.md)。

**仍从条件 quiet snapshot 出发，不是所有 BuildintPre、WFInt 或初始化可达。** Room/Quiet/all-clear 与 spec_done 限制未消除；GOOD_OS、K1–K4 未闭合，uCOS3 未开始，未提交／推送。旧423失败、1错误及 audit/whitespace 失败保留；最终结果见本步 verification.json，下方历史原文不变。
<!-- bound-quiet-continuous-checkpoint-end -->

<!-- bound-exit-dynamic-checkpoint-start -->
## 局部检查点：同一 bound LocalInv 下的动态 Exit 三路径

第241步把 changed、quiet、same 三条真实函数体契约接入同一候选 bound-LI 动态 Exit；通过同 LI 的 joint Sched 规格嵌入建立 Enter/Exit/Sched 的 WFFunEnv/WFIFun，统一 builders、实际 scall 与返回 p_local。三路径 typed 非空、字面边界及返回绑定单因素弱化见[第241步中文说明](audit/STAGE241_BOUND_EXIT_DYNAMIC.md)。

**候选 Enter 边界仍不同于旧 local-storage Enter，不能称旧完整环境只改了 LI。** 不是所有 BuildintPre、iret、WFInt 或初始化可达；GOOD_OS、K1–K4 未闭合，uCOS3 未开始，未提交／推送。旧423失败、1错误及 audit/whitespace 失败保留，六门94/1/1/1/1/0。最终实测以本步 verification.json 为准；下方历史原文不变。
<!-- bound-exit-dynamic-checkpoint-end -->

<!-- bound-exit-body-checkpoint-start -->
## 局部检查点：bound LocalInv 的完整 changed Exit 与三函数候选环境

第240步接通 saved 清零、running 分支、临界区、nesting 递减、实际 dispatch、excrit 和返回；从原资源推导绑定不变量，返回保存 bound p_local。通用 builders/实际调用和 Enter、Exit、精确 Sched 的同 LI/Inv 候选 WFFunEnv/WFIFun 已实现。typed 非空、字面后置、运行时代码身份及单因素后置弱化见[第240步中文说明](audit/STAGE240_BOUND_EXIT_BODY.md)。

**候选环境的 Exit 仅 changed-case，旧动态 quiet/same 三函数环境未迁移。** 不是 WFInt、初始化可达或 GOOD_OS；K1–K4 未闭合，uCOS3 未开始，未提交／推送。六门94/1/1/1/1/0，旧423失败、1错误及 audit/whitespace 失败保留；最终实测以本步 verification.json 为准，下方历史原文不变。
<!-- bound-exit-body-checkpoint-end -->

<!-- bound-exit-dispatch-checkpoint-start -->
## 局部检查点：地址绑定 LocalInv 接入实际 changed dispatch

第239步重证依赖 LocalInv 的真实调度前缀与 counter++/copy/switch，实例化为与 Enter 相同的地址绑定 LocalInv；从原 bodydata 的既有资源建立前置，不外加 globals 或中间 Hoare 结论。typed 非空状态同时满足原 bodydata 和新前置，字面后置与恢复后的 CurLINV 已作 Coq 检查。见[第239步中文说明](audit/STAGE239_BOUND_EXIT_DISPATCH.md)。

**仅 changed dispatch，不是整个 Exit/builders、旧三函数环境迁移、iret、WFInt 或初始化可达。** 旧单绑定负对照不替代新片段证明。GOOD_OS、同程序 K1–K4 未完成，uCOS3 未开始；六门94/1/1/1/1/0，旧423失败、1错误及 audit/whitespace 失败保留，未提交／推送。最终实测以本步 verification.json 为准；下方历史原文不变。
<!-- bound-exit-dispatch-checkpoint-end -->

<!-- interrupt-bindings-checkpoint-start -->
## 局部检查点：地址绑定纳入 LocalInv，入口不再外加 globals

第238步在框架既有 LocalInv 中保存三控制变量的地址绑定，证明合法性、零资源足迹和同一原 Inv 的 GoodI。从真实 BuildintPre 本身连接 EOI 与精确 Enter；真实 Enter 本体/builders、单函数 WFFunEnv/WFIFun 及 typed 非空入口均检查。只改错 running 全局绑定的固定状态对照显示：旧 Aemp builder 仍成立，新 builder 拒绝。见[第238步中文说明](audit/STAGE238_INTERRUPT_BINDINGS.md)。

**这是候选 LocalInv 的入口接入，不是原三函数环境迁移完成；不是 Exit/iret、WFInt 或初始化可达。** 固定状态对照不是两次执行。GOOD_OS、同程序 K1–K4 未完成，uCOS3 未开始；六门94/1/1/1/1/0，旧423失败、1错误及 audit/whitespace 失败保留，未提交／推送。实测以本步 verification.json 为准，下方历史原文不变。
<!-- interrupt-bindings-checkpoint-end -->

<!-- interrupt-entry-general-checkpoint-start -->
## 局部检查点：实际 EOI/Enter 支持非全清 ISR

第237步去掉第236步多余的 ISR 全清要求，真实 builder 控制值开包后连续接 EOI/精确 Enter，精确保留其他活动位与两栈；同一 typed 堆上的非全清 builder 非空且前缀成立，原三函数环境不变。另以 Coq 证明精确“内存 nesting=ISR 栈长”不能直接作为包含全清状态的 Inv，并给出实际 builder 的 load=1/栈长2见证。见[第237步中文说明](audit/STAGE237_INTERRUPT_ENTRY_GENERAL.md)。

**仍有显式 globals frame；仅前缀，不是 Exit/iret、WFInt 或初始化可达。** 精确深度等式的放置限制不是运行时反例；生产 LocalInv、lookup/current 对应仍开放。GOOD_OS、同程序 K1–K4 未完成，uCOS3 未开始；六门94/1/1/1/1/0，旧423失败、1错误及 audit/whitespace 失败保留，未提交／推送。实测以本步 verification.json 为准，下方历史原文不变。
<!-- interrupt-entry-general-checkpoint-end -->

<!-- interrupt-entry-control-checkpoint-start -->
## 局部检查点：从实际 BuildintPre 取得控制值并接 Enter

第236步打开原 ready/TCB/storage Inv，提取 running/nesting/lock 的字节值与界限，连续连接 EOI 和同一 QCspec 的精确 Enter；后置保留旧 nesting 与 nest_after 的关系。具体 typed 字节堆见证实际 builder 前置加地址绑定非空，原三函数环境不变。见[第236步中文说明](audit/STAGE236_INTERRUPT_ENTRY_CONTROL.md)。

**地址绑定仍是显式附加 frame；仅 EOI/Enter 前缀，不是全部入口、Exit/iret 或 WFInt。** lookup 内容、current priority/TCB 与 nesting/ISR 栈关系仍需落实；fixture 为常 Aemp LocalInv，不是初始化可达。GOOD_OS、同程序 K1–K4 仍开放，uCOS3 未开始；六门94/1/1/1/1/0，旧423失败、1错误及 audit/whitespace 失败保留，未提交／推送。实测见本步 verification.json，下方历史原文保留。
<!-- interrupt-entry-control-checkpoint-end -->

<!-- interrupt-same-continuous-checkpoint-start -->
## 局部检查点：same 的连续 EOI/Enter/Exit/iret

第235步把实际 Enter 的 nesting=0→1 接到原 same 动态精确 Exit：lookup/rows/group、priority table、current priority、running 的完整权限拆半并在返回后重组，精确 p_local 与 Inv 用 CurTid 分开保留；关闭同一 ready/TCB/storage Inv 后返回。具体 typed 字节入口 current=Ready/priority=4/bitmap=16 一致，复用原三函数程序与共同 WFFunEnv/WFIFun。见[第235步中文说明](audit/STAGE235_INTERRUPT_SAME_CONTINUOUS.md)。

**quiet/changed/same 均只是条件强入口，不是全 BuildintPre、WFInt、生产 ISR 规格或初始化可达；fixture 仍用常 Aemp LocalInv。** GOOD_OS、同程序 K1–K4 仍开放，uCOS3 未开始。旧423失败、1错误及 audit/whitespace 失败保留，六门94/1/1/1/1/0，总目标 active，未提交／推送。实测见本步 verification.json，下方历史原文保留。
<!-- interrupt-same-continuous-checkpoint-end -->

<!-- interrupt-changed-continuous-checkpoint-start -->
## 局部检查点：changed 的连续 EOI/Enter/Exit/iret

第234步把实际 Enter 的 nesting=0→1 接到原动态 changed Exit：当前指针拆为两半，保留 typed half，返回后证明类型一致再重组完整权限；真实调度合同归还精确 p_local，关闭同一 ready/TCB/storage Inv 后返回。具体字节堆证明强入口非空，复用原三函数程序与共同 WFFunEnv/WFIFun。见[第234步中文说明](audit/STAGE234_INTERRUPT_CHANGED_CONTINUOUS.md)。

**只是 changed 强入口，不是全部 BuildintPre、WFInt、生产 ISR 规格或初始化可达；fixture 仍使用常 Aemp LocalInv。** same 连续路径、GOOD_OS、同程序 K1–K4 仍开放，uCOS3 未开始。保留旧423失败、1错误及 audit/whitespace 失败，六门94/1/1/1/1/0，总目标 active，未提交／推送；实测见本步 verification.json，下方历史原文保留。
<!-- interrupt-changed-continuous-checkpoint-end -->

<!-- interrupt-quiet-continuous-checkpoint-start -->
## 局部检查点：quiet 的连续 EOI/Enter/Exit/iret

第233步从实际 Enter 更新到 builders/call 保留精确控制值，在原三函数环境中连续连接 quiet wrapper；running 半权限跨 Exit 保留并重组，同一 ready/TCB/storage Inv 关闭后返回。具体字节堆给出非空强入口。见[第233步中文说明](audit/STAGE233_INTERRUPT_QUIET_CONTINUOUS.md)。

**仅限未饱和等条件下的 quiet 强入口，不是 WFInt、全部 ISR 或初始化可达；LocalInv fixture 仍为常 Aemp。** changed/same 连续路径、GOOD_OS、同程序 K1–K4 仍开放，uCOS3 未开始。旧423失败、1错误及 audit/whitespace 失败保留，六门94/1/1/1/1/0，总目标 active，未提交／推送；实测见本步 verification.json，下方历史原文保留。
<!-- interrupt-quiet-continuous-checkpoint-end -->

<!-- exit-same-exact-dynamic-checkpoint-start -->
## 局部检查点：same 精确合同接入原动态三函数环境

第232步以真实 same builders 调用第231步完整本体；共同 scheduler 的 critical/ISR 两臂均保精确资源，使用 assertion equality embedding。原 changed/quiet 前后置字面保持，原两级 codec、原 Enter/Exit/SchedNew 程序与同一 Inv 不变；新 Spec 的 WFFunEnv/WFIFun、实际 same call 和 typed table/target 非空 builders 已连接。见[第232步中文说明](audit/STAGE232_EXIT_SAME_EXACT_DYNAMIC.md)。

**same 新前置也更强；局部 fixture 使用常 Aemp LocalInv，不是完整生产 ready/TCB/storage Inv 或初始化可达。** 固定状态断言对照不是两次执行；三条 admissible 路径采用精确合同不等于任意输入全覆盖。连续 EOI/Enter/Exit/iret、WFInt、GOOD_OS、同程序 K1–K4 仍开放，uCOS3 未开始。旧423失败、1错误及 audit/whitespace 失败保留；六门94/1/1/1/1/0。实测以本步 verification.json 为准，总目标 active，未提交／推送；下方历史原文保留。
<!-- exit-same-exact-dynamic-checkpoint-end -->

<!-- exit-same-exact-body-checkpoint-start -->
## 局部检查点：same Exit 精确资源贯穿真实 scheduler 与完整本体

第231步保持原 C/config/AST 与 ISR codec/context，证明精确 scheduler 的真实 builders/本体、单函数 WFFunEnv、call_rule 和 target update，并接通完整 same-priority OSIntExit 本体；保留精确 p_local、counter、ISR 与两栈，允许 IE 两值。实际字节堆重新构造精确入口并有非空栈见证。见[第231步中文说明](audit/STAGE231_EXIT_SAME_EXACT_BODY.md)。

**新 same 前置也更强，尚未替换动态三函数 Spec 的 same 合同；fixture 不是完整生产 ready/TCB/storage Inv，也不是初始化可达。** 固定状态局部断言和 saved-load 对照不是两次执行。完整连续 ISR、WFInt、GOOD_OS、同程序 K1–K4 仍开放，uCOS3 未开始；保留旧423失败、1错误及 audit/whitespace 失败，六门仍94/1/1/1/1/0。实测以本步 verification.json 为准，总目标 active，未提交／推送。下方历史原文保留。
<!-- exit-same-exact-body-checkpoint-end -->

<!-- exit-quiet-exact-checkpoint-start -->
## 局部检查点：quiet Exit 精确资源贯穿真实本体与三函数环境

第230步为 quiet 分支引入诚实更强的精确 p_local 入口，从原 nondispatch 本体经 builders 到实际 call 保资源；复用原两级 codec，仅替换 quiet，changed/same 字面保持。同一原 Enter/Exit/SchedNew 程序、原 Inv 和新 Spec 已证明 WFFunEnv/WFIFun，并有五块实际内存的 builder/call 非空见证。见[第230步中文说明](audit/STAGE230_EXIT_QUIET_EXACT.md)。

**same 仍弱；最小 quiet footprint 不是生产完整 ready/TCB/storage ISR 入口，也不是初始化可达。** 固定状态局部断言对照不是两次执行。完整连续 ISR、GOOD_OS、同程序 K1–K4 仍开放，uCOS3 未开始；保留旧423失败、1错误及 audit/whitespace 失败，六门仍94/1/1/1/1/0。实测以本步 verification.json 为准，总目标 active，未提交／推送。下方历史原文保留。
<!-- exit-quiet-exact-checkpoint-end -->

<!-- exit-exact-dynamic-checkpoint-start -->
## 局部检查点：动态精确 Exit 联合原三函数程序

第229步复用原动态 codec、前置及 ready/TCB/storage Inv，将精确 changed 返回、精确 Enter 和 exact-critical／原 ISR 联合 scheduler 接入原 Enter／Exit／SchedNew 三函数程序。证明同一新 Spec 的 WFFunEnv/WFIFun、真实 Exit call，以及同一物理入口的字面精确后置；embedding 保持 assertion equality。见[第229步中文说明](audit/STAGE229_EXIT_EXACT_DYNAMIC.md)。

**quiet/same 仍为原弱后置，尚未连续连接完整 ISR，也未证明初始化可达。** counter 单因素对照只检查逻辑快照／实际 load 边界，不是两次完整执行。GOOD_OS／同程序 K1–K4 仍开放，uCOS3 未开始；旧423失败、1错误和 audit/whitespace 失败保留，六门仍94/1/1/1/1/0。实测以本步 verification.json 为准，总目标 active，未提交／推送。下方历史原文保留。
<!-- exit-exact-dynamic-checkpoint-end -->

<!-- exit-exact-internal-checkpoint-start -->
## 局部检查点：精确 OSIntExit 接入真实函数边界

第228步复用原入口，把精确 changed body 包入真实 BuildPreI/BuildRetI，返回同一 Inv、精确 p_local、两栈与 globals；局部槽交还 builder，不用 Atrue 吞资源。证明同一 Spec 的 Exit+SchedNew 双函数 WFFunEnv 与真实 call_rule，使用同一 typed TCB/full lookup/control 非空见证。见[第228步中文说明](audit/STAGE228_EXIT_EXACT_INTERNAL.md)。

**限 changed/running=1/lock=0/nest<=1/clearISR/IE=false；未替换动态三函数 Spec，未闭合完整 ISR。GOOD_OS、同程序 K1–K4 仍开放，uCOS3 未开始。** 实测核验以本步 verification.json 为准；旧423失败、1错误及 audit/whitespace 失败保留，六门仍94/1/1/1/1/0，总目标 active，未提交/推送。下方历史原文保留。
<!-- exit-exact-internal-checkpoint-end -->

<!-- exit-exact-body-checkpoint-start -->
## 局部检查点：精确资源贯穿 OSIntExit 优先级变化本体

第227步把精确 scheduler 前缀接到真实比较、计数、copy、switch、excrit 和 return，返回同一 ready/TCB/storage Inv、精确 p_local、两栈与绑定；新 private 不再额外附加 Atrue，不从旧弱后置逆推。见[第227步中文说明](audit/STAGE227_EXIT_EXACT_BODY.md)。

同一真实 typed TCB/full lookup/control 状态给出非空入口，字面后置和同一精确 callee Spec 的单函数 WFFunEnv 接到原归一化完整 changed body。**限 running=1、lock=0、nest<=1、different priority、clear ISR、原 IE=false；切换后共享值不冻结。尚未接 Exit builders/替换原三函数 Spec，不是完整 ISR，GOOD_OS/K1–K4 仍开放，uCOS3 未开始。**

实测结果以本步 verification.json 为准；保留旧423失败、1错误和 audit/whitespace 失败，六门仍94/1/1/1/1/0，总目标 active，未提交/推送。下方历史原文保留。
<!-- exit-exact-body-checkpoint-end -->

<!-- sched-exact-prefix-checkpoint-start -->
## 局部检查点：真实调度前缀保留精确资源并归还存储

第226步把第225步精确 scheduler call 接到原目标指针赋值，从既有 closed storage entry 借出并归还完整数组权限，保留精确 p_local、共享抽象槽、两栈和名称绑定；不从旧弱后置反推强后置。见[第226步中文说明](audit/STAGE226_SCHED_EXACT_PREFIX.md)。

同一真实物理状态满足 closed entry 与借出后的 exact entry，接通原单函数 WFFunEnv 和真实两语句前缀。fixture 使用 Tptr Tvoid；两种任务模式不是单因素消融。复核既有 local-only 单因素对照，不冒充完整前置反例。**返回 opened storage；尚未替换原三函数 Spec，精确资源尚未贯穿 OSIntExit/dispatch/switch；完整 ISR/WFInt/初始化、GOOD_OS 和同程序 K1–K4 仍开放，uCOS3 未开始。**

实测核验以本步 verification.json 为准；历史423失败、1错误及 audit/whitespace 失败保留，六门仍94/1/1/1/1/0，总目标 active，未提交/推送。下方历史原文保留。
<!-- sched-exact-prefix-checkpoint-end -->

<!-- sched-exact-local-checkpoint-start -->
## 局部检查点：原 OS_SchedNew 保留精确局部资源

第225步不改原程序/旧证明，从两次真实赋值、return 到真实 builders、单函数 WFFunEnv 与 call_rule 保留精确 p_local；SWINV/两栈在契约内，复用原 codec 和 generic-common 后置定义。见[第225步中文说明](audit/STAGE225_SCHED_EXACT_LOCAL.md)。

真实原 scheduler 字节 fixture 给出非空 builders；owned CI 使用既有 Inv 空尾，仅是可满足性 fixture，ambient RI 仍任意，不等于生产 ISR 联合非空。复核第224步固定状态局部断言单因素反例，不称完整前置反例或两次执行。**新 scheduler 契约尚未替换三函数 Spec，精确资源尚未贯穿 Exit/dispatch/switch；完整 ISR/WFInt/API/初始化、GOOD_OS 与同程序 K1–K4 仍开放，uCOS3 未开始。**

实测以本步 verification.json 为准；旧423失败、1错误及 audit/whitespace 失败保留，六门仍94/1/1/1/1/0，总目标 active，未提交/推送。下方历史原文保留。
<!-- sched-exact-local-checkpoint-end -->

<!-- interrupt-ready-local-checkpoint-start -->
## 局部检查点：精确局部资源贯穿 Enter 与真实 EOI 前缀

第224步保持同一 ready/TCB/storage Inv、原三函数程序及 Exit/SchedNew 契约，从低层更新到完整 Enter、本体 builders、实际调用一直保留精确 p_local；接通 EOI→Enter 两语句前缀，并恢复原返回规则所需的资源蕴含。见[第224步中文说明](audit/STAGE224_INTERRUPT_READY_LOCAL.md)。

真实 typed TCB/full lookup 给出精确入口的数学子堆见证，不称初始化可达；固定状态只换局部断言的单因素对照，证明 CurLINV 不能随意反推 p_local，不声称完整边界反例或两次执行。**只闭合 Enter 段精确资源；含 Exit/调度的完整 ISR、生产 LocalInv/控制值/lookup、WFInt/API/初始化、GOOD_OS 与同程序 K1–K4 仍开放，uCOS3 未开始。**

实测核验见本步 verification.json；保留历史423失败、1错误及既有 audit/whitespace 失败，不称全绿。六门仍94/1/1/1/1/0，总目标 active，未提交/推送；下方历史原文保留。
<!-- interrupt-ready-local-checkpoint-end -->

<!-- interrupt-ready-environment-checkpoint-start -->
## 局部检查点：新 Enter 契约联合原动态三函数环境

第223步保持原三函数程序、动态 Exit/SchedNew 契约和同一 ready/TCB/storage Inv，仅替换 Enter 条目；证明三函数 WFFunEnv/WFIFun、实际 Enter call 与真实非空 builders。见[第223步中文说明](audit/STAGE223_INTERRUPT_READY_ENVIRONMENT.md)。

单条目规格对照固定状态、程序与新逻辑实参，旧条目因无法解码而提前拒绝；只检验入口适配，不说明下游执行。**已联合三函数 Spec，但尚未连续连接 EOI→Enter→Exit→iret 或重建原 ISR 精确 p_local；生产控制值/lookup、WFInt/API/初始化、GOOD_OS 与同程序 K1–K4 仍开放，uCOS3 未开始。**

实测核验见本步 verification.json；保留历史423失败、1错误及旧audit/whitespace失败，不称全绿。六门仍94/1/1/1/1/0，总目标 active，未提交/推送；下方历史原文保留。
<!-- interrupt-ready-environment-checkpoint-end -->

<!-- interrupt-ready-enter-checkpoint-start -->
## 局部检查点：共享就绪边界接入真实 OSIntEnter

第222步从同一 ready/TCB/storage Inv 中提取任意合法 running/nesting 字节，证明完整原 OSIntEnter 本体、真实 BuildPreI/BuildRetI、单函数 WFFunEnv 和实际 call_rule；两栈放在契约内而非 GoodFrm。第221步 EOI 后的 closed 边界加真实名称绑定可接入此调用。见[第222步中文说明](audit/STAGE222_INTERRUPT_READY_ENTER.md)。

真实 TCB 物理资源给出非空 builder；只改 running 的一个字节，两侧入口合法，原 guard 实际求值不同。**对照不是两次完整执行或初始化可达；新 Enter 契约尚未联合旧三函数 Spec、精确 ISR 返回资源重建尚未完成；完整 ISR/WFInt/API/初始化、生产控制值/lookup 语义、GOOD_OS 与同程序 K1–K4 仍开放，uCOS3 未开始。**

实测构建、递归内核检查和回归结果记录在本步 verification.json；历史423失败、1错误及旧审计/空白失败保留。六门仍94/1/1/1/1/0，总目标 active，未提交/推送；下方历史原文保留。
<!-- interrupt-ready-enter-checkpoint-end -->

<!-- interrupt-ready-boundary-checkpoint-start -->
## 局部检查点：真实中断入口与返回的就绪资源边界

第221步用原 BuildintPre／eoi_ieoff_rule 和 BuildintRet／iret_rule，在同一 ready/TCB/storage Inv 下证明 ISR 包装两端；保留真实线程资源，向量0按框架闭区间定义也包含 ready core。见[第221步中文说明](audit/STAGE221_INTERRUPT_READY_BOUNDARY.md)。

真实类型 TCB/存储子堆给出两端 builder 的满足实例；这使用局部环境／辅助状态的断言稳定性，不是初始化可达或完整 ISR 执行。单因素只改 incoming ISR 的向量1位，向量0 EOI 后它仍为true；两向量均合法，只是位代数对照。**仅 incoming 全clear边界；生产 ISR 规格、中间调用及其控制值/lookup语义、WFInt/API/初始化、GOOD_OS 和同程序 K1–K4 仍开放，uCOS3 未开始。**

核验实测见本步 verification.json；保留全量历史423失败、1错误及旧audit/whitespace失败，不称全绿。六门仍94/1/1/1/1/0，总目标 active，未提交/推送；下方历史原文保留。
<!-- interrupt-ready-boundary-checkpoint-end -->

<!-- ready-dynamic-environment-checkpoint-start -->
## 局部检查点：动态快照与统一函数环境接入就绪共享不变量

第220步把运行快照移入逻辑实参，在同一 ready/TCB/storage Inv 下连接 quiet/same/changed 完整归一化退出本体、真实 builders 和三函数 WFFunEnv/WFIFun，并证明实际 GoodI。复用已有 codec，删除不再影响新 Inv 的额外 table_length 因子，保留真实13项表约束。见[第220步中文说明](audit/STAGE220_READY_DYNAMIC_ENVIRONMENT.md)。

真实 TCB/完整 lookup 的动态 changed 入口非空，覆盖 nesting=0/1、任意 counter/critical stack。同一最大 counter 物理状态只改逻辑快照，两个 codec 都合法，错误快照由实际 load 排除；仅入口对照，非两份完整执行。**changed 仍限 running=1/lock=0/不同优先级/clearISR/原IE=false；quiet/same 尚未新增共布局非空入口。生产 Inv 控制值/lookup语义、ISR/WFInt/API/初始化、GOOD_OS 与同程序 K1–K4 开放，uCOS3 未开始。**

18根/递归coqchk/两次构建通过；新5项回归通过，全量2264项仍423失败、1错误，旧ID与顺序保持，旧audit/whitespace失败保留。六门仍94/1/1/1/1/0，总目标 active，未提交/推送；下方历史原文保留。
<!-- ready-dynamic-environment-checkpoint-end -->

<!-- ready-exit-builders-checkpoint-start -->
## 局部检查点：就绪共享不变量接入真实函数 builders

第219步将第218步完整归一化不同优先级退出本体接到真实 BuildPreI/BuildRetI；外部 GoodFunAsrt 不依赖 localenv，单 saved domain 在内部推出不遮蔽，局部单元在返回时归还，共享 ready/TCB/storage 使用同一 Inv，恢复后不冻结共享值。见[第219步中文说明](audit/STAGE219_READY_EXIT_BUILDERS.md)。

真实类型 TCB、完整 lookup 和实际控制字节给出非空 builder 入口、最高就绪不同任务、nesting=0/1 及最大 counter。saved→running 单因素对照保持物理字节和两个有效前置，只验证名称边界，不是两份完整函数执行。**仍限 running=1/lock=0/不同优先级/clear ISR/原 IE=false；动态快照/统一 Spec 尚未迁移新 Inv，生产 ISR/WFInt/初始化、GOOD_OS 和同程序 K1–K4 开放，uCOS3 未开始。**

六门仍94/1/1/1/1/0；本步 verification.json 记录实测核验和保留旧失败。总目标 active，未提交/推送；下方历史原文保留。
<!-- ready-exit-builders-checkpoint-end -->

<!-- ready-exit-body-checkpoint-start -->
## 局部检查点：同一就绪共享不变量下的完整退出本体

第218步在同一 ready/TCB/storage Inv 下连接完整归一化 `OSIntExit` 的 saved 初始化、running guard、encrit、nesting/lock guards、真实 dispatch、恢复后的 excrit 与 return。共享资源关闭到 Inv，恢复后不冻结共享值。见[第218步中文说明](audit/STAGE218_READY_EXIT_BODY.md)。

独立真实类型 TCB、完整 lookup 与控制字节构造非空入口，量化覆盖 nesting=0/1 和最大 counter。excrit 单因素对照只检查最后原语，不是两份完整函数执行。**仍限 running=1/lock=0/不同优先级/clear ISR/原 IE=false；新 Inv 的 builders/统一 Spec、控制值/lookup 语义、生产 ISR/WFInt/初始化、GOOD_OS 与同程序 K1–K4 开放，uCOS3 未启动。**

六门仍94/1/1/1/1/0；本步 verification.json 记录实测核验和保留的旧失败。总目标 active，未提交/推送；下方历史原文保留。
<!-- ready-exit-body-checkpoint-end -->

<!-- ready-exit-handoff-checkpoint-start -->
## 局部检查点：就绪共享不变量接入真实退出调度与切换尾段

第217步在同一 ready/TCB/storage Inv 下证明实际 increment/skip/copy/switch，并连接真实 `OS_SchedNew` 调用、目标赋值和不同优先级 guard。切换前共享 ready/TCB、dispatch/control 资源关闭到 Inv，恢复后不冻结共享快照。见[第217步中文说明](audit/STAGE217_READY_EXIT_HANDOFF.md)。

独立真实前缀给出非空入口；同一堆只删除 copy，两侧均实际切换并保持新 Inv，缓存分别为4/6。这是 handoff 局部后缀消融，不是两份完整函数执行。**完整退出本体/builders/统一 Spec 尚未迁移；控制值/lookup 语义、生产 ISR/WFInt/初始化、GOOD_OS 与同程序 K1–K4 仍开放，uCOS3 未启动。**

六门仍94/1/1/1/1/0；实测构建、递归内核检查和保留旧失败见本步 verification.json。总目标 active，未提交/推送；下方历史原文保留。
<!-- ready-exit-handoff-checkpoint-end -->

<!-- ready-storage-invariant-checkpoint-start -->
## 局部检查点：就绪语义与调度存储使用同一不变量

第216步建立同一 Inv 持有 ready/TCB 语义资源和 dispatch/control 存储，证明实际 `GoodI`、原 switch 保持及真实就绪选择提取。实际源码前缀给出非空入口；只清零 ready 低字节、保留其他字节和 TCB/控制存储的消融排除错误语义。见[第216步中文说明](audit/STAGE216_READY_STORAGE_INVARIANT.md)。

原 switch 不自动更新优先级缓存，具体执行验证新 Inv 不蕴含 cache/current 一致。**这是数据所有权候选，尚未迁移第215步 builders/统一 Spec；lookup/控制值语义、生产 ISR/WFInt/初始化、GOOD_OS 和同程序 K1–K4 仍开放，uCOS3 未启动。**

六门仍94/1/1/1/1/0；实际构建、内核检查和保留旧失败见本步 verification.json。总目标 active，未提交/推送；下方历史原文保留。
<!-- ready-storage-invariant-checkpoint-end -->

<!-- dynamic-exit-snapshot-checkpoint-start -->
## 局部检查点：退出规格使用动态运行快照

第215步把 changed 的计数器、就绪/任务表、嵌套层数等移入逻辑实参；固定地址、类型与表长度。实际 builders/完整归一化本体及三函数 WFFunEnv/WFIFun 使用一个动态 Spec、同一 storage Inv。见[第215步中文说明](audit/STAGE215_DYNAMIC_EXIT_SNAPSHOT.md)。

同一最大 counter 物理状态下，匹配快照前置非空，冻结 counter=1 的前置由实际内存读取排除；两快照 codec 均合法。这是入口资源对照，不是两个完整变体执行。quiet/same 仍是另一具体地址夹具。**changed 仍限 clear ISR/原 IE=false；生产 Inv/ISR/WFInt/初始化、GOOD_OS、同程序 K1–K4 开放，uCOS3 未启动。**

六门仍94/1/1/1/1/0；实际核验和旧失败见本步 verification.json。总体目标 active，未提交/推送；下方历史原文保留。
<!-- dynamic-exit-snapshot-checkpoint-end -->

<!-- scheduler-spec-unification-checkpoint-start -->
## 局部检查点：三条退出路径使用同一规格与不变量

第214步用精确逻辑实参嵌入连接 quiet/same/changed，证明实际归一化本体及三函数 WFFunEnv/WFIFun 使用一个调度 lookup、同一 storage Inv。真实 callee 的联合 builders 契约已逐支证明；未修改运行时代码、框架或冻结证明。见[第214步中文说明](audit/STAGE214_SCHEDULER_SPEC_UNIFICATION.md)。

嵌入规则仅覆盖无 scalle 的语句；实际本体满足此条件。独立旧字节夹具接入各联合入口；tag 单因素对照只验证编码选择边界，不是两份完整执行。**changed 仍限原 IE=false/ISR 全清，快照仍为模块参数；生产 Inv/ISR/WFInt/初始化、GOOD_OS、同程序 K1–K4 开放，uCOS3 未启动。**

六门仍94/1/1/1/1/0；实际核验与旧失败见本步 verification.json。总目标 active，未提交/推送；下方历史原文保留。
<!-- scheduler-spec-unification-checkpoint-end -->

<!-- interrupt-exit-changed-builders-checkpoint-start -->
## 局部检查点：不同优先级退出接入真实 builders

第213步把第212步完整归一化本体接到真实 BuildPreI/BuildRetI；外部断言带 GoodFunAsrt，不依赖局部环境，saved 单局部 domain 在内部推出不遮蔽。恢复后共享值不冻结，仍归还同一 storage Inv。见[第213步中文说明](audit/STAGE213_INTERRUPT_EXIT_CHANGED_BUILDERS.md)。

独立实际字节证明入口非空并实例化完整契约，覆盖 nesting=1/0 与最大 counter；单因素 saved→running 对照保持物理内存相同、两侧 builder 前置有效，检验遮蔽边界，不是完整变体执行。BuildPreI 拒绝非空实参，BuildRetI 不检查该数量。**仍限原 IE=false/ISR 全清；统一全部退出路径规格/生产函数环境/Inv/ISR/WFInt/初始化、GOOD_OS 与同程序 K1–K4 开放，uCOS3 未启动。**

六门仍94/1/1/1/1/0；实际核验见本步 verification.json，旧失败保留。总目标 active，未提交/推送；下方历史原文保留。
<!-- interrupt-exit-changed-builders-checkpoint-end -->

<!-- interrupt-exit-changed-body-checkpoint-start -->
## 局部检查点：不同优先级退出的完整归一化本体

第212步在同一条 InfRules 中连接 saved 初始化、running guard、实际 encrit、nesting 递减/guards、第211步真实 dispatch、原线程恢复后的 excrit 和 return。running/nesting/lock 完整字节归还同一 storage Inv，不保留切换前共享值快照。见[第212步中文说明](audit/STAGE212_INTERRUPT_EXIT_CHANGED_BODY.md)。

独立字节内存给出 nesting=1/0、不同任务及最大 UINT32 计数器的非空入口和实际定理实例。删除 excrit 的对照仅检查最后的临界栈尾段，不是两份完整函数执行。**当前仍限 clear ISR/原 IE=false、已打开资源及已分配局部；不同任务真实 builders、统一生产函数环境/Inv/ISR/WFInt/初始化、GOOD_OS 和同程序 K1–K4 仍开放；uCOS3 未启动。**

六门仍94/1/1/1/1/0；核验实测以本步 verification.json 为准，旧失败保留。总目标 active，未提交/推送；下方历史原文保留。
<!-- interrupt-exit-changed-body-checkpoint-end -->

<!-- interrupt-exit-dispatch-hoare-checkpoint-start -->
## 局部检查点：真实调度前缀连接不同优先级退出分支

第211步从同一打开资源状态连接真实 OS_SchedNew 调用、目标指针赋值、不同优先级 guard 与第210步 increment/skip/copy/switch 尾段；完整就绪输入和优先级指针表归还同一 storage Inv，不留作切换后的共享快照。见[第211步中文说明](audit/STAGE211_INTERRUPT_EXIT_DISPATCH_HOARE.md)。

独立实际字节与任务表构造非空入口、不同任务/最高就绪及最大 UINT32 实例；比较对照只改变同状态表达式参数，不冒充完整执行。**完整外层退出前缀、真实 builders、任意 ISR/统一生产 Inv/初始化、GOOD_OS 和同程序 K1–K4 仍开放；uCOS3 未启动。** 通用缓存—当前任务关系未建立，不能仅由 guard 推出不同任务。

六门仍94/1/1/1/1/0；实际核验和旧失败保留见本步 verification.json。总目标active，未提交/推送；下方历史原文保留。
<!-- interrupt-exit-dispatch-hoare-checkpoint-end -->

<!-- interrupt-exit-handoff-hoare-checkpoint-start -->
## 局部检查点：不同任务退出尾段的所有权 Hoare

第210步直接连接实际 counter increment → skip → 优先级缓存 copy → switch，将 high/current/counter 的完整写权限与共享抽象表交回同一 storage Inv；切换 frame 只保留环境与线程私有资源。后置描述原线程恢复，所有共享值存在化，不冻结切换前快照。见[第210步中文说明](audit/STAGE210_INTERRUPT_EXIT_HANDOFF_HOARE.md)。

独立实际字节内存与任务表给出不同任务、最高就绪及 UINT32 最大计数器的非空前置；此前冻结的删除 copy 完整切换消融是另一见证，不冒充本步恢复执行。**仍未连接退出前缀到此接口、完整不同任务 builders 或生产 Inv/ISR/WFInt/初始化；GOOD_OS、同程序 K1–K4 开放，uCOS3 未启动。**

六门仍94/1/1/1/1/0；实际核验、回归及保留旧失败以本步 verification.json 为准。目标active，未提交/推送；下方历史原文保留。
<!-- interrupt-exit-handoff-hoare-checkpoint-end -->

<!-- interrupt-exit-unified-builders-checkpoint-start -->
## 局部检查点：不调度与同优先级退出统一到真实 builders

第209步把完整不调度归一化本体接到真实 BuildPreI/BuildRetI，从 saved 单局部 domain 推导三个全局名不遮蔽；再以纯逻辑路径标签合并第208步 same 契约，在同一增强 Spec 下直接闭合 OSIntExit/OSIntEnter/OS_SchedNew 的 WFFunEnv/WFIFun。见[第209步中文说明](audit/STAGE209_INTERRUPT_EXIT_UNIFIED_BUILDERS.md)。

具体实际 builder 前置见证覆盖 nesting≥2、lock>0、run≠1，并保留 same 路径非空；IE 单字段对照两侧有效解码，只检查现场身份，不冒充完整执行消融。**仍不覆盖不同任务 handoff；生产 Inv/ISR/WFInt、初始化、GOOD_OS 与同程序 K1–K4 开放，uCOS3 未启动。**

六门仍94/1/1/1/1/0；核验、回归与保留旧失败见本步 verification.json。总目标active，未提交/推送；下方历史原文保留。
<!-- interrupt-exit-unified-builders-checkpoint-end -->

<!-- interrupt-exit-same-builders-checkpoint-start -->
## 局部检查点：真实退出 builders 与受限三函数环境

第208步把同优先级退出完整归一化本体接到真实 BuildPreI/BuildRetI；外部断言不提供局部环境，由 saved 单局部 domain 推导不遮蔽。OSIntExit/OSIntEnter/OS_SchedNew 在同一增强 Spec 下直接闭合 WFFunEnv/WFIFun，未假设退出本体正确。见[第208步中文说明](audit/STAGE208_INTERRUPT_EXIT_SAME_BUILDERS.md)。

独立具体内存证明真实前置非空；有效解码的 IE 单字段对照检查现场身份，不冒充两份执行。非空实参由 BuildPreI 拒绝；BuildRetI 本身不检查形参数量，已单独记录。**退出规格仍仅覆盖 running=1、nesting≤1、lock=0、同优先级路径；不是完整 OSIntExit、生产 ISR 或 GOOD_OS。**

六门仍94/1/1/1/1/0；生产 Inv/初始化/GOOD_OS/同程序 K1–K4 开放，uCOS3未启动。递归核验及旧失败保留见本步 verification.json；目标active，未提交/推送。下方历史原文保留。
<!-- interrupt-exit-same-builders-checkpoint-end -->

<!-- interrupt-exit-same-priority-checkpoint-start -->
## 局部检查点：完整同优先级退出归一化本体

第207步连接 saved 初始化、running 检查、真实 encrit/excrit、nesting 递减、增强契约下的真实调度调用、任务指针更新及 return None。主定理只有一个 InfRules，没有假设整个中段或 callee Hoare；原 IE 两值及 ISR/两栈参数化。见[第207步中文说明](audit/STAGE207_INTERRUPT_EXIT_SAME_PRIORITY.md)。

独立字节内存给出前置非空见证，并明确覆盖原 IE 两值和非空两栈。saved 对照仅是赋值边界，不是完整变体执行。**已分配局部单元的归一化本体不等于全部实际退出 builders；不同任务 handoff、增强 Spec 的三函数统一、生产 Inv 提供全局数据仍开放。**

六门仍94/1/1/1/1/0；生产 ISR/完整 Inv/初始化/GOOD_OS/同程序 K1–K4 未完成，uCOS3 未启动。实测核验与旧失败保留以本步 verification.json 为准；目标 active，未提交/推送。下方历史原文保留。
<!-- interrupt-exit-same-priority-checkpoint-end -->

<!-- scheduler-isr-context-checkpoint-start -->
## 局部检查点：调度调用保持 ISR 与临界资源

第206步用动态函数契约承载任意 ISR/两栈及已持有的低层 ISR 不变量，直接证明原 OS_SchedNew 的真实 builders 与单函数 WFFunEnv，再接入 OSIntExit nesting 递减→两 guard→真实调用→最高任务指针赋值→同优先级不 handoff 的中段。没有把这些资源强称为 GoodFrm，也没有假设整个中段正确。见[第206步中文说明](audit/STAGE206_SCHEDULER_ISR_CONTEXT.md)。

独立非空正控及仅改临界栈逻辑字段的对照均成功解码；对照检查规格/现场身份，不是两份完整执行。具体见证 held=false；增强 Spec 尚未接入原三函数环境，完整调度退出 builder、不同任务 handoff 和生产 Inv 资源提供仍开放。核验及回归结果以本步 verification.json 为准。

六门仍94/1/1/1/1/0；生产 ISR/完整 Inv/初始化/GOOD_OS/同程序 K1–K4 未完成，uCOS3 未启动。目标 active，未提交/推送；下方历史原文保留。
<!-- scheduler-isr-context-checkpoint-end -->

<!-- interrupt-exit-nondispatch-checkpoint-start -->
## 局部检查点：中断退出非调度路径的完整本体 Hoare

第205步直接证明归一化 OSIntExit 的 saved 初始化、running guard、真实临界规则、nesting 递减、调度跳过及 return None。run=1 时要求 nesting≥2 或 lock>0；run≠1 时不进入临界区。原 IE 两值及 ISR/栈参数化，实际取得的不变量保持并归还，没有假设中段或 callee 正确。见[第205步中文说明](audit/STAGE205_INTERRUPT_EXIT_NONDISPATCH.md)。

具体非空见证覆盖 lock=0/嵌套路径及未运行路径；只删 excrit 的单因素对照是尾段控制，不冒充完整函数变体。**仍未证明调度路径、全部真实 builder 或三函数 WFFunEnv；调用者拥有的 nesting/lock 如何来自生产 Inv 也未解决。**

六门仍94/1/1/1/1/0；生产ISR/完整Inv/初始化/GOOD_OS/同程序K1–K4开放，uCOS3未启动。递归核验、回归及保留旧失败以本步 verification.json 为准；目标active，未提交/推送。下方历史原文保留。
<!-- interrupt-exit-nondispatch-checkpoint-end -->

<!-- interrupt-exit-environment-checkpoint-start -->
## 局部检查点：退出函数调用闭合，函数本体义务仍开放

第204步按已接受的源码抽象，把 OSIntExit 与 OSIntEnter/OS_SchedNew 放入同一三函数 P/Spec，证明域匹配、语法及实际静态 callee 全部有定义；提取精确的 WFFunEnv iff 退出本体真实 builder→InfRules 义务。见[第204步中文说明](audit/STAGE204_INTERRUPT_EXIT_ENVIRONMENT.md)。

**没有证明 iff 右侧，故没有完成三函数 WFFunEnv/WFIFun。** 原非空 builder 保持；仅省略切换映射／仅删除调度函数的单因素对照检查链接边界，不冒充执行或端口 refinement。递归核验、回归及旧失败以本步 verification.json 为准。

六门仍94/1/1/1/1/0；生产 ISR/WFInt、完整任务不变量、初始化、GOOD_OS 与同程序 K1–K4 尚未完成；uCOS3未启动。目标active，未提交/推送。下方历史原文保留。
<!-- interrupt-exit-environment-checkpoint-end -->

<!-- interrupt-function-environment-checkpoint-start -->
## 局部检查点：中断进入与调度的共同函数环境

第203步在同一内部 P/Spec 下直接构造 OSIntEnter、OS_SchedNew 的真实 builder→InfRules，建立 WFFunEnv/WFIFun，并接入原三时间 API 与同一 name-only LocalInv/partial GoodI。见[第203步中文说明](audit/STAGE203_INTERRUPT_FUNCTION_ENVIRONMENT.md)。

同一兼容 GE 下的两个独立非空 builder 状态排除前置空洞，不宣称同时拥有资源或初始化可达。仅删进入定义／仅改返回类型的单因素对照分别检查域和类型边界，不冒充执行消融。数值实例实际查到五个不同函数；通用 API 标识仍允许左优先覆盖。

**尚未接入 OSIntExit、生产 ISR/WFInt、完整任务不变量、初始化或 GOOD_OS。** 递归核验及新回归结果以本步 verification.json 为准；旧失败与审计问题保留。六门94/1/1/1/1/0，uCOS3未启动，总目标active，未提交/推送。下方历史原文保留。
<!-- interrupt-function-environment-checkpoint-end -->

<!-- interrupt-source-roundtrip-checkpoint-start -->
## 局部检查点：真实中断进入、两次完整调用与原现场恢复

第202步由原 pint_step/li_step 实际生成 kint，连接显式 EOI→OSIntEnter→OSIntExit→exint，同任务 nesting0→1→0，恢复被中断的 code/exprcont/env/ISRstack 和原 T/les/aus，saved四字节释放。见[第202步中文说明](audit/STAGE202_INTERRUPT_SOURCE_ROUNDTRIP.md)。

独立非空 ready4/waiting6 资源给出完整正控及 counter/canary/caller 保持。IE 单因素仅测准入；EOI 单因素两侧都实际准入，到相同调用前缀端点而 ISR 位不同，未冒充两份完整 ISR 返回消融。逻辑前置在 cleared-IR/pushed-stack 视图；只对特定 byte/cell frame 做结构性传递，不宣称任意 GoodInvAsrt 可跨 ISR 栈变化。

**显式框架包装器不是生产平台 ISR/refinement；只是一条同任务存在性 trace，不是生产 LocalInv/WFFunEnv/全交错/初始化或 GOOD_OS。** 22根递归核验、回归和旧失败保留以本步 verification.json 为准。六门94/1/1/1/1/0，uCOS3未启动，目标active，未提交/推送；下方历史原文保留。
<!-- interrupt-source-roundtrip-checkpoint-end -->

<!-- interrupt-resumed-return-checkpoint-start -->
## 局部检查点：完整调用切换到已有目标现场并返回

第201步连接完整 OSIntExit 抽象调用→实际 switch→目标任务 excrit/return；恢复目标自己的 IE/caller，释放目标 saved，原 waiting 任务的现场与 saved 仍挂起。见[第201步中文说明](audit/STAGE201_INTERRUPT_RESUMED_RETURN.md)。

独立 waiting6/ready4 资源先 fresh alloc/store 构造目标 saved，再做两初始 IE/两目标 IE 完整正控。尾段仅删 critical-stack 顶位的两侧都真正返回，恢复 IE 相反、free 结果相同；独立显式 exint 正控恢复被中断现场并强制 IE=true，裸 kint 无局部自动弹栈。没有把尾段消融冒充两份完整函数变体，也不声称任意 R 在中断栈 pop 后保持。

**目标现场来源仍是输入边界，沿用 ADR0010 源码抽象；不是原端口 refinement、原等待任务唤醒/返回、生产 ISR/全交错或 GOOD_OS。** 递归核验、回归和旧失败保留以本步 verification.json 为准。六门94/1/1/1/1/0，uCOS3未启动，总目标active，未提交/推送。下方历史原文保留。
<!-- interrupt-resumed-return-checkpoint-end -->

<!-- interrupt-switch-boundary-checkpoint-start -->
## 局部检查点：显式源码级边界下的完整调用与实际切换

第200步将完整 OSIntExit 调用接到原框架的真实 switch：正常程序复制最高就绪优先级到当前缓存，再切换执行者和当前指针。新建独立调用点抽象，不安装或编造原 OSIntCtxSw 的函数体。见[第200步中文说明](audit/STAGE200_INTERRUPT_SWITCH_BOUNDARY.md)与[ADR-0010](docs/adr/0010-中断切换调用点采用显式源码级抽象.md)。

独立 waiting6/ready4 资源使用同一物理输入；初始 IE 两值均完整切换。仅删除缓存赋值的对照也实际切换，指针均到 ready4、counter均为20，但正常缓存4一致，对照缓存6不一致。原缺失端口模型仍停顿。旧任务 excrit/return/caller/kint 保留挂起，saved四字节仍存活；目标任务的原 code/env/aux 保持，不能把旧任务的 IE 当成新任务 IE。

**这是显式源码抽象的一条不交错执行，不是原端口 refinement、旧任务完整返回、生产 ISR/WFFunEnv 或 GOOD_OS。** 逐根递归核验及回归实测见本步 verification.json；旧423失败1错误与审计失败保留。六门94/1/1/1/1/0，uCOS3未启动，总目标active，未提交/推送。下方历史原文保留。
<!-- interrupt-switch-boundary-checkpoint-end -->

<!-- interrupt-global-entry-checkpoint-start -->
## 局部检查点：已有中断现场中的真实全局前缀

第199步把第198步完整不同任务前缀接到原 `lpstep`，从真实已有的 `T/les/aus` 绑定出发，保留 `kint` 和待恢复的 excrit/return/caller；其他任务 code/env/aux 逐点保持，客户状态和当前执行者不变。见[第199步中文说明](audit/STAGE199_INTERRUPT_GLOBAL_ENTRY.md)。

独立非空 waiting6/ready4 正控在同堆只改初始IE时，两侧都完整到原 sfexec112；实际IE=false，原IE压栈，fresh saved四字节存活，caller同名saved23/local running0保持。端口缺失且关中断时证明无任何全局下一步。独立 ci=nil 边界只改IE：false全局停顿，true实际执行原中断规则；不把此控制冒充完整前缀端点的中断执行。

**已有 kint 是输入，仍是存在的一条不交错 trace；没有生产 ISR 安装、端口实现、实际 switch/cache 同步或完整不同任务返回，更不是 GOOD_OS。** 递归检查和两轮全量回归的实际结果见本步 verification.json；旧423失败1错误和审计失败保留。六门94/1/1/1/1/0，uCOS3未启动，总目标active，未提交/推送。下方历史原文保留。
<!-- interrupt-global-entry-checkpoint-end -->

<!-- interrupt-switch-entry-checkpoint-start -->
## 局部检查点：不同任务中断退出至切换调用入口

第198步将不同任务路径接为真实scall/sfexec、fresh saved分配、encrit、nesting1→0、OS_SchedNew调用及目标更新、同一task map推导比较true、counter模递增和真实OSIntCtxSw调用入口。主接口无trace/callee/分配/store/free/eval答案前提。见[第198步中文说明](audit/STAGE198_INTERRUPT_SWITCH_ENTRY.md)。

独立非空资源中当前waiting6、ready4，物理当前指针/优先级缓存与同一任务表一致。相同program/heap只改初始IE，两侧均到sfexec112，实际IE=false并保存原IE；fresh saved4字节仍存活，caller同名saved23/local running0保持。仅删counter递增的同输入尾段两侧均到同一sfexec，counter分别20/19；不是完整变体函数的返回消融。

**端点仍停在OSIntCtxSw的sfexec；没有端口实现、实际switch或完整不同任务返回，不能把指针切换冒充OSPrioCur同步。** 生产ISR/LocalInv、WFFunEnv、初始化与GOOD_OS仍开放。20根递归检查、两轮2154项及旧423失败1错误的结果见本步verification.json。六门94/1/1/1/1/0，uCOS3未启动，目标active，未提交/推送。下方历史原文保留。
<!-- interrupt-switch-entry-checkpoint-end -->

<!-- interrupt-dispatch-call-checkpoint-start -->
## 局部检查点：最后一层中断的完整同任务调用

第197步将 n=1、lock=0、当前已经最高就绪的路径接成真实 scall/sfexec、fresh局部分配、临界区、真实OS_SchedNew、目标更新、原比较false、退出与返回释放；比较由同一task map关系推出，主接口没有trace/callee/分配/store/free/eval前提。见[第197步中文说明](audit/STAGE197_INTERRUPT_DISPATCH_CALL.md)。

独立非空ready/task/table正控在同一program/物理堆只改初始IE，两侧完整恢复IE/栈尾/caller；同名不同类型saved23、局部running0（全局1）、counter19/canary99保持，fresh四字节释放。只删除调度callee lookup的无下一步证明仅用于边界，不能替代完整正控。

**空间前/后置明确在false IE逻辑视图；任意IE的实际trace恢复不等于生产SWINV/ISR闭合。仍是ADR-0005局部不交错抽象，不是原端口语义保持或GOOD_OS。** 不同优先级真实switch、ISR/LocalInv、WFFunEnv、初始化和模拟仍开放。19根递归检查、两轮2149项与旧423失败1错误的精确结果见本步verification.json；六门94/1/1/1/1/0，uCOS3未开始，目标active，未提交/推送。下方历史原文保留。
<!-- interrupt-dispatch-call-checkpoint-end -->

<!-- interrupt-dispatch-execution-checkpoint-start -->
## 局部检查点：OSIntExit 最后一层中断的真实调度前缀

第196步从物理 nesting=1/lock=0 的独立 ready/task/table 资源出发，实际执行1→0、两级 guards、OS_SchedNew 调用及局部分配/释放、目标指针更新，停在原优先级比较。主接口不固定当前优先级，也不要求整个语句、callee、分配或存储执行前提。见[第196步中文说明](audit/STAGE196_INTERRUPT_DISPATCH_EXECUTION.md)。

同优先级独立正控完整执行中段到 skip，计数器19/canary99保持；只改 nesting 字节、只删除递减、只改 current 字节的对照分别证明真实跳过/分支选择。两项输入变化均有除单字节外的全堆等式。不同优先级只到 true 分支入口，不执行 counter++/OSIntCtxSw，不能当作任务切换已证。

**仍是 ADR-0005 显式抽象的局部不交错中段，不是 nesting=1 完整调用、原端口语义保持或 GOOD_OS。** 生产 ISR/LocalInv、switch、全环境/初始化与模拟仍开放。26根递归检查、两轮2144项测试的实际结果见本步 verification.json；旧423失败1错误保留。六门94/1/1/1/1/0，uCOS3未启动，目标active，未提交/推送。下方历史原文保留。
<!-- interrupt-dispatch-execution-checkpoint-end -->

<!-- interrupt-call-execution-checkpoint-start -->
## 局部检查点：OSIntExit 真实调用入口与局部分配

第195步把第194步嵌套 body 接到实际 scall/sfexec、fresh 局部分配、返回释放和 caller 恢复，主接口不再要求调用方提供 store／NoDup／callcont／分配执行前提。running=1、2≤nest<256 时，实际计数递减、任意 IE／既有栈尾恢复，新块4字节释放；独立非空 program 覆盖边界2与255，以及同名不同类型 saved／局部 running=0 的 caller。见[第195步中文说明](audit/STAGE195_INTERRUPT_CALL_EXECUTION.md)。

删除唯一函数定义、添加一个有类型运行实参，分别由真实 sfexec 无下一步证明；它们只授权入口拒绝，完整下游执行由独立正控另证。块外 frame 排除 fresh 块与 nesting 块，不声称更强全堆等式。

**这仍是 ADR-0005 抽象程序的局部不交错执行，不是原端口语义保持或 GOOD_OS。** n=1调度／真实switch、生产 ISR/LocalInv、初始化／全环境及模拟仍开放。9根递归检查、两轮全量回归以本步 verification.json 为准；旧423失败1错误保留。六门94/1/1/1/1/0，uCOS3未启动，目标active，未提交／推送。下方历史原文保留。
<!-- interrupt-call-execution-checkpoint-end -->

<!-- interrupt-nested-execution-checkpoint-start -->
## 局部检查点：OSIntExit 嵌套路径连续执行

第194步证明显式临界宏抽象后的 OSIntExit 在 running=1、2≤nest<256 时，从已分配局部变量的 body 连续执行 saved:=0、物理计数递减、encrit/excrit 与 return/free，恢复任意初始 IE、既有栈尾及调用者环境；独立非空见证覆盖2→1和255→254。见[第194步中文说明](audit/STAGE194_INTERRUPT_NESTED_EXECUTION.md)。

相同物理输入的临界中段仅删除 excrit，实际执行后留下不同 IE/栈状态；这不是完整变体函数的入口到返回消融，冻结协议的较窄落实范围另行记录。正常完整 body 到返回另证。空 callee program 只用于证明嵌套路径不调用调度器，非生产函数环境。

**这是 ADR-0005 显式抽象程序的局部不交错 trace，不是原端口语义保持或 GOOD_OS。** 入口分配、n=1调度分支、生产 ISR/LocalInv、完整环境与模拟仍开放。14根独立检查及全量回归见本步 verification.json；旧423失败1错误保留。六门94/1/1/1/1/0，uCOS3未启动，目标active，未提交／推送。下方历史原文保留。
<!-- interrupt-nested-execution-checkpoint-end -->

<!-- interrupt-uniform-internal-checkpoint-start -->
## 局部检查点：原 OSIntExit 的统一内部函数规格

第193步将 running／动态快照接入同一 fpre/fpost，稳定接口对 vl/lg/tid/pre/post 统一量化，经实际 BuildPreI/BuildRetI 复用第192步完整原 body；动态 ready/task/table 不变量从 pure 前置抽出，不再捕获为逐次标量规格。见[第193步中文说明](audit/STAGE193_INTERRUPT_UNIFORM_INTERNAL.md)。

同一非生产 Spec 覆盖不同／同优先级、嵌套禁调度及非运行；独立物理入口对任意有界 run/current/nest 和任意 counter／saved 旧值非空。同堆仅改 running 或 counter 的合法逻辑解释由真实 load 排除，替代输入另有匹配物理见证；running 块外 frame 单证。非空实参由真实 dnil builder 拒绝，不是 fpre 拒绝。

**统一契约不是 WFFunEnv；callee 域／实现仍缺，identity switch 不是生产效果，非 GOOD_OS。** Out／Sw、任意 IE、生产 ISR/LocalInv、初始化／环境及模拟仍开放；idle fixture 不声称完整 current-task 一致性。24根递归检查、两轮2129项测试见 verification.json；旧423失败1错误及有序ID保留。六门94/1/1/1/1/0；uCOS3未启动，目标active，未提交／推送。下方历史原文保留。
<!-- interrupt-uniform-internal-checkpoint-end -->

<!-- interrupt-switch-call-checkpoint-start -->
## 局部检查点：OSIntExit 消除 switch 语句级前提

第192步用真实无实参 `call_rule` 与同一 Spec 的 switch lookup，接回原完整 body 和实际 `BuildPreI/BuildRetI`；saved 地址只作为逻辑见证，不增加 C 实参。主接口不再有语句级 Hoare 前提。见[第192步中文说明](audit/STAGE192_INTERRUPT_SWITCH_CALL.md)。

同一非生产 Spec 的完整 builder 覆盖不同优先级启用切换、同优先级和嵌套禁调度；独立非空物理入口／switch 前置及实际 load 分别排除同堆错误 counter／saved 地址，块外 frame 单证。另由真实 EqDom 反证该 fixture 没有完整 WFFunEnv。

**lookup 不是 callee 实现；identity switch 契约不是任务切换效果，非生产环境或 GOOD_OS。** Out／Sw、任意 IE 保存恢复、生产 ISR／LocalInv、全环境／初始化及模拟仍开放；current=0 fixture 不声称完整 TCB 优先级一致性。协议笔误以单独勘误保留。24根递归检查、三轮2124项测试见 verification.json；旧423失败1错误及有序ID保留。六门94/1/1/1/1/0；uCOS3未启动，目标active，未提交／推送。下方历史原文保留。
<!-- interrupt-switch-call-checkpoint-end -->

<!-- interrupt-resource-codec-checkpoint-start -->
## 局部检查点：OSIntExit 的动态资源编码与完整 builder

第191步用现有 logicvar 编码12项动态元数据，在实际调用任务／指针索引下解码资源，roundtrip 自动消除第190步的四个资源匹配前提，接回原完整 body 与真实 BuildPreI/BuildRetI。唯一语句残余仍是带递增 counter、对所有 saved block 量化的真实 switch。见[第191步中文说明](audit/STAGE191_INTERRUPT_RESOURCE_CODEC.md)。

同一 Spec 的完整 builder 分别覆盖嵌套2→1禁调度、1→0且同优先级启用调度的 Hoare 推导；没有不同优先级切换实例。独立非空物理入口与实际 load 排除同堆错误 counter／nest，另证块外字节保持。解码形状控制不能代替后续语义；快照不是端口执行 trace，编码的五个自然数字段须有界。

**这是局部静态布局的资源编码／条件契约，非生产端口实现、全任务环境或 WFFunEnv／GOOD_OS。** Out／Sw continuation、任意 IE 的真实保存恢复、生产 ISR 等仍开放。31根／递归检查和两轮2119项测试见 verification.json；旧423失败1错误及有序ID保留。六门94/1/1/1/1/0；uCOS3未启动，目标active，未提交／推送。下方历史原文保留。
<!-- interrupt-resource-codec-checkpoint-end -->

<!-- interrupt-indexed-port-checkpoint-start -->
## 局部检查点：原 OSIntExit 接入任务／逻辑参数索引临界规格

第190步用同一个资源族读取实际调用任务和逻辑参数，经真实 call_rule、原完整 body、已证明中段及实际 BuildPreI/BuildRetI 纵向连接，不再固定 owner／空lg。四个运行分支特化等式仍显式开放，唯一语句级残余仍是带递增counter的实际switch。见[第190步中文说明](audit/STAGE190_INTERRUPT_INDEXED_PORT.md)。

独立物理load分别排除错误任务索引、逻辑参数和saved值；块外字节保持另证。完整运行builder实例嵌套2→1、入口非空，但不覆盖启用调度／switch；非运行在全None Spec、lg=nil使callee资源为Afalse时仍闭合。快照不是执行trace，空LocalInv不是生产ISR。

**仅泛型索引条件契约，不是生产资源编码／端口实现或 WFFunEnv／GOOD_OS。** 逐根／递归检查与两轮测试见本步verification.json；保留旧423失败1错误及有序ID。六门94/1/1/1/1/0，uCOS3未启动，总目标active，未提交／推送。下方历史原文保留。
<!-- interrupt-indexed-port-checkpoint-end -->

<!-- interrupt-function-builders-checkpoint-start -->
## 局部检查点：原 OSIntExit 接通真实函数构造器

第189步把完整原 body 接到实际 `BuildPreI/BuildRetI`。函数内部再取出 saved 的任意旧值／地址，外部 fpre/fpost 满足 GoodFunAsrt；从完整单局部 domain 推导不遮蔽，返回仍保留可写局部单元与同一完整 domain。运行分支直接复用188完整body，唯一语句残余仍为带已递增counter的实际中断切换，对内部所有saved block量化。见[第189步中文说明](audit/STAGE189_INTERRUPT_FUNCTION_BUILDERS.md)。

独立非空资源验证 Vundef／整数旧值、15／17局部地址与真实 &saved、实际builder拒绝非空实参，以及全None Spec下非运行完整body。地址对照仅搬移局部绑定及对应单元，不声称整堆相同；返回非空快照不是执行trace，空LocalInv不是生产ISR。

**这是实际builder条件契约，不是 WFFunEnv 或 GOOD_OS。** 实际分配／释放执行、全任务生产临界接口、真实switch、生产ISR/LocalInv及全环境仍开放。逐根／递归检查与两轮测试见本步verification.json；旧423失败1错误及有序ID保留。六门94/1/1/1/1/0，uCOS3未启动，总目标active，未提交／推送。下方历史原文保留。
<!-- interrupt-function-builders-checkpoint-end -->

<!-- interrupt-full-body-checkpoint-start -->
## 局部检查点：原 OSIntExit 完整函数体的条件证明

第188步把真实 saved:=0、OSRunning==1 的实际 load／类型、真实 enter／已证明中段／exit 与 sret 接成完整原 body 的 Hoare 证明。运行分支直接复用第187步资源桥，不把整个分支或中段作为前提；唯一语句级残余是启用且不同优先级时的实际 OSIntCtxSw，counter 已递增。见[第188步中文说明](audit/STAGE188_INTERRUPT_FULL_BODY.md)。

另证不运行路径无须任何 callee lookup；即使 Spec 全为 None，仍初始化 saved 并返回 None。完整非空物理堆固定其他资源只改 running=0/1/2/255，只有1使真实表达式为真；同环境同堆的错误 saved 值由 load 排除，块外字节保持。快照不是执行 trace，空 LocalInv 不是生产 ISR。

**仅完整 body 条件证明，非函数 builder 或 GOOD_OS。** saved 真实分配／BuildPreI／BuildRetI／WFFunEnv、全任务生产 port、真实 switch、生产 ISR／LocalInv 与全环境仍开放。稳定编译、逐根假设、递归 coqchk 与两轮测试见 verification.json；旧423失败1错误及有序 ID 保留。六门94/1/1/1/1/0，uCOS3未启动，总目标active，未提交／推送。下方历史原文保留。
<!-- interrupt-full-body-checkpoint-end -->

<!-- interrupt-resource-bridge-checkpoint-start -->
## 局部检查点：OSIntExit 调度资源接入真实临界调用

第187步双向拆分第185步联合资源：callee持有物理ready/table/TCB/计数/嵌套/锁及saved，caller保留全局绑定与局部不遮蔽事实。稳定接口实际组合enter／已证明的中段／exit，**不再把整个中段作为Hoare前提**，仅留下启用且不同优先级时真实OSIntCtxSw调用的义务，其前置counter已经递增。见[第187步中文说明](audit/STAGE187_INTERRUPT_RESOURCE_BRIDGE.md)。

同一物理堆仅改局部遮蔽，callee仍接受、caller拒绝；这是名称边界对照，不是调度语义。相同环境仅改counter时，错误旧值由实际load排除，块外字节保持。完整acquired/tail非空快照不等于执行trace，空LocalInv不是生产ISR。固定owner／空逻辑参数的port契约仍非全任务生产Spec。

编译／逐根假设／递归coqchk与两轮完整测试见verification.json；旧423失败1错误及全部有序ID保留。**仍非完整函数或GOOD_OS。** 端口实现、真实switch、saved分配／初始化连接、running守卫／builder、生产ISR/LocalInv及全环境仍开放。六门94/1/1/1/1/0；uCOS3未启动，总目标active，未提交／推送。下方历史原文保留。
<!-- interrupt-resource-bridge-checkpoint-end -->

<!-- interrupt-critical-calls-checkpoint-start -->
## 局部检查点：OSIntExit 的 saved 初始化与真实指针调用边界

第186步从caller局部绑定推导真实 &saved 的值／类型，通过实际call_rule隔离caller名称与callee物理资源，证明saved:=0，并按真实AST组合enter／中段／exit。四段资源可不同，两个实际Spec lookup保持显式。见[第186步中文说明](audit/STAGE186_INTERRUPT_CRITICAL_CALLS.md)。

同一物理堆仅改局部绑定的对照保持类型/domain合法；仅改saved值时地址保持，错误旧值由实际load排除，另证块外字节保持。非identity契约两端非空不等于实际执行或CPU_SR编码；移除lookup只作输入层检查，空LocalInv不代表生产ISR。

**仍有整个中段在新资源下的Hoare前提；第185步联合资源的caller名称剥离桥尚未闭合，非完整函数或GOOD_OS。** 实际临界契约／实现、OSIntCtxSw、running守卫、builder、生产ISR/LocalInv、初始化／环境及simulation仍开放。编译／逐根假设／递归coqchk与两轮测试见verification.json；旧423失败1错误及全部ID保留。六门94/1/1/1/1/0；uCOS3未启动，总目标active，未提交／推送。下方历史原文保留。
<!-- interrupt-critical-calls-checkpoint-end -->

<!-- interrupt-exit-dispatch-checkpoint-start -->
## 局部检查点：OSIntExit 的真实调度分支与计数／守卫联合资源

第185步把原OSIntExit的真实OS_SchedNew调用、最高任务指针发布、实际!=分支、32位模递增和空trace接到上一轮递减／两个守卫。稳定接口不再假设整个dispatch正确，只在启用且不同优先级时留下带已更新资源的实际OSIntCtxSw调用义务；关闭分支无需调度器lookup或CPU调用证明。见[第185步中文说明](audit/STAGE185_INTERRUPT_EXIT_DISPATCH.md)。

同一物理堆和TCB表接受完整联合入口／tail快照。固定其他资源只改当前优先级或counter，比较／回绕均来自真实物理load；错误旧counter在同一domain及堆上由load排除。块外字节保持另证。fixture不是执行trace；数值优先级对照不声称完整current-task一致性，空LocalInv不代表生产ISR。

编译／递归coqchk／逐根假设／两轮完整测试见verification.json；保持旧423失败1错误及全部ID，调试失败证据保留。**仅条件片段连接，非完整函数或GOOD_OS。** 实际OSIntCtxSw、临界调用、saved局部与builder、生产ISR/LocalInv、初始化／全环境、全交错simulation和同程序K1–K4仍开放。六门94/1/1/1/1/0；uCOS3未开始，总目标active，未提交／推送。下方历史原文保留。
<!-- interrupt-exit-dispatch-checkpoint-end -->

<!-- interrupt-exit-checkpoint-start -->
## 局部检查点：原 OSIntExit 的真实递减与后续两个守卫

第184步重放固定源码预处理并建模完整原 AST；实际片段证明字节计数仅在大于0时减1，0保持，后续守卫读取减后的计数与调度锁。稳定接口仅在减后计数和锁均0时要求真实dispatch的残余Hoare证明；计数仍嵌套或锁非0时，无需dispatch前提。经RuleSound连接同一片段RuleSem，但不消除残余调度／中断切换义务。见[第184步中文说明](audit/STAGE184_INTERRUPT_EXIT.md)。

真实物理字节堆证明入口非空；固定其他输入只改变run、nest、lock，另证各变化块外的每个字节保持。同一堆上的错误post直接由计数物理load排除，不靠domain早拒。旧nest=0且lock=0也进入调度分支，这是原源码行为。独立前后fixture不是执行trace，空LocalInv不是生产ISR不变式。

编译／假设／递归coqchk及两轮完整测试见本步verification.json；保持旧423失败1错误及其全部ID，失败调试证据保留。**完整AST不等于完整函数Hoare，更不是GOOD_OS。** saved局部／真实builder、临界调用、启用分支／OSIntCtxSw、ISR、生产LocalInv、初始化／全局环境、全交错simulation和同程序K1–K4仍开放；六门94/1/1/1/1/0，uCOS3未开始，目标active，未提交／推送。下一步继续该原函数的调用资源与完整契约。下方历史原文保留。
<!-- interrupt-exit-checkpoint-end -->

<!-- interrupt-enter-checkpoint-start -->
## 局部检查点：原 OSIntEnter 的全字节分支与真实 builder

第183步重放固定源码预处理，证明原 `OSIntEnter` 在 `IE=false` 下：仅当 `OSRunning=1` 且嵌套值小于255时递增；255保持，不回绕，其他运行字节不写。稳定接口接真实 `BuildPreI/BuildRetI`、完整原body及单函数 `WFFunEnv`。见[第183步中文说明](audit/STAGE183_INTERRUPT_ENTER.md)。

独立字节堆接受实际完整入口；固定nest只改run、固定run只改254/255的对照从物理字节求值。错误post对照保持同一堆/domain/run/action，直接由nest物理load排除；不是domain早拒。输出见证不是执行trace，空LocalInv仅为探针fixture。函数在冻结清单仍属public/external，本步internal规则打包不是完整API/ISR安装。

编译、递归coqchk／假设闭包、完整旧失败ID对照见本步verification.json；旧失败与所有调试快照保留。**仅局部函数纵向连接，不是完整ISR、CPU hook或GOOD_OS。** 生产LocalInv、全局初始化/环境、全交错simulation、同程序K1–K4仍开放；六门94/1/1/1/1/0，uCOS3未开始，总目标active，未提交／推送。下一步继续真实OSIntExit与中断调用资源；下方历史原文保留。
<!-- interrupt-enter-checkpoint-end -->

<!-- tick-function-environment-checkpoint-start -->
## 局部检查点：tick 与调度器共用环境，CPU hook 义务精确分离

第182步把原 tick 与原 OS_SchedNew body 接入同一 Spec、强 ready/time Inv 和 name-only LocalInv；稳定接口证明该局部 map 的 WFFunEnv **当且仅当**实际 CPU hook 满足同环境下真实声明、builder及全部body义务。没有合成空hook，也没有假设整个环境已验证。三个时间API的WFAPI/GoodI使用相同Spec/Inv/LocalInv，并证明实际API/内部标识不冲突。见[第182步中文说明](audit/STAGE182_TICK_FUNCTION_ENVIRONMENT.md)。

旧非空tick物理fixture在新环境下接受真实builder和原body。移除hook只在domain层拒绝；保留入口仅改返回类型时domain明确通过而WFFunEnv拒绝；Tvoid入口仍须完整body残余义务，不能把早拒当下游语义有效。非空见证不承诺同时满足调度器caller，也不是一次完整执行。

编译、17根假设与递归coqchk、完整旧失败ID比较见本步verification.json。**这只是局部环境连接，不是生产hook/ISR或整核已完成。** 生产LocalInv、完整初始化/环境、全交错simulation、同程序K1–K4及GOOD_OS仍开放；六门94/1/1/1/1/0，uCOS3未开始，总目标active；不提交/推送，旧证据不改写。下一步接真实hook/ISR与生产资源。下方历史原文保留。
<!-- tick-function-environment-checkpoint-end -->

<!-- time-api-refinement-checkpoint-start -->
## 局部检查点：时间 API 的临界抽象步与精确返回资源

第181步从原程序和同一未分配局部槽的TRmemory执行实际call／body，在临界复制后的实际Mc推导合法spec_step：setter更新ostmid，getter保持整个O。真实退出／释放／返回后的同一Mf保留强Ccore与精确caller资源CurTid ct，不再用Atrue替代最终余下所有权。见[第181步中文说明](audit/STAGE181_TIME_API_REFINEMENT.md)。

只省去setter抽象同步的对照保持同一Mc、END None和IRQ快照：新物理clock与旧ghost不一致时强core拒绝，同步后接受；不是action早拒。仅改源实参的两次完整调用各自更新物理／抽象clock；getter返回实际clock、两局部真实释放。中间关闭IRQ状态仅展示core投影，最终精确frame受GoodFunAsrt及can_change_aop限制，不宣称任意frame可运输。

编译、21根假设、递归coqchk、完整旧失败ID比较见本步verification.json；保留全部失败诊断。**有限无交错执行与临界点单步规格连接，不是全并发simulation、整个全局Inv或GOOD_OS。** 生产LocalInv／完整环境、初始化、tick-hook-ISR与同程序K1–K4仍开放；六门94/1/1/1/1/0，第一阶段未完成、uCOS3未开始、总目标active，未提交／推送。下一步接生产调用上下文与环境。下方历史原文不改写。
<!-- time-api-refinement-checkpoint-end -->

<!-- time-api-lifecycle-checkpoint-start -->
## 局部检查点：原时间 API 的完整有限调用与返回路径

第180步从第179步同一未分配局部槽的旧堆和同一程序出发，真实调用／分配后继续执行原OSTimeGet／OSTimeSet函数体，构造saved初始化、临界读写、两个local的真实释放与caller恢复。getter返回实际clock，setter最终物理clock等于实参；同一实际入口Ma仍满足强core与精确caller pre。见[第180步中文说明](audit/STAGE180_TIME_API_LIFECYCLE.md)。

只改setter实参的两次完整调用均写出对应时钟，错误旧值由物理load独立排除。caller同名ticks从150被callee160遮蔽，真实返回后恢复150且160／161均释放；其他非修改块字节保持。生产body接口量化原IE／si／ci和frame，探针快照仍true／空栈。稳定编译、递归coqchk、假设闭包及完整旧失败ID比较见本步verification.json；失败诊断保留，不宣称旧全套全绿。

**仅无中断交错的有限loststep路径存在性，不是最终强Inv／抽象action同步或GOOD_OS。** 探针剩余资源投影Atrue并另验物理frame；未把它冒充全程序并发契约。生产LocalInv／完整环境、初始化、tick-hook-ISR与同程序K1–K4仍开放；六门94/1/1/1/1/0，第一阶段未完成、uCOS3未开始、总目标active，未提交／推送。下一步接抽象action与返回资源。下方历史原文不改写。
<!-- time-api-lifecycle-checkpoint-end -->

<!-- time-api-call-checkpoint-start -->
## 局部检查点：时间 API 从真实 call 分配到联合入口

第179步从没有API局部槽的旧堆出发，执行原OSTimeGet的5步调用／分配、原OSTimeSet的7步实参求值／分配／真实参数写入。两者在上一轮同一程序环境到达原body入口，同一实际Mf满足强core与精确BuildPreA'；BuildRetA'与原body契约沿用既有同Spec／Inv。见[第179步中文说明](audit/STAGE179_TIME_API_CALL.md)。

两条仅改setter实参的实际调用均接受各自正确pre、保留强core和clock；错误局部值由物理load独立排除，不靠action早拒。同名caller变量保存在kcall，所有非160／161块字节保持。生产空间frame在最终callee环境评价，不运输任意caller断言。稳定编译、17根假设、两入口递归coqchk与完整旧失败ID比较见本步verification.json，不宣称全套全绿。

**只完成真实调用准备，不是完整call-body-return或最终GOOD_OS。** 生产LocalInv／函数环境、初始化、tick-hook-ISR和同程序K1–K4仍开放；六门94/1/1/1/1/0，第一阶段未完成、uCOS3未开始、总目标active，未提交／推送。下一步从实际Mf继续原body及返回连接。下方历史原文不改写。
<!-- time-api-call-checkpoint-end -->

<!-- time-ready-entry-checkpoint-start -->
## 局部检查点：同一物理堆上的时间 API caller 与强共享 core

第178步构造实际联合内存：保留旧TCB／ready／table／clock，分配两个不相交编码local，并从当前指针全权限拆出两份兼容只读半权限。真实getter／setter的BuildPreA'、BuildRetA'、原body契约与 `strong core ** caller pre` 接到同一个精确pre；不是两份独立fixture的合取。见[第178步中文说明](audit/STAGE178_TIME_READY_ENTRY.md)。

只改clock时caller仍接受而强core拒绝；只改setter参数槽时强core仍接受而固定n的caller拒绝，clock保持；getter接受Vundef等任意raw初值。具体正控使用taskmap内实际ready任务。上下文运输和字节堆比较不是机器步骤，尚未证明真实call分配或完整APItrace。稳定编译、27根假设、两个入口递归coqchk和全套旧失败ID比较见本步verification.json，不宣称全套全绿。

**这只是已分配入口资源兼容性，不是全局初始化或最终GOOD_OS。** name-only LocalInv、生产函数环境／tick-hook-ISR、同程序K1–K4仍开放；六门94/1/1/1/1/0，第一阶段未完成、uCOS3未开始、目标active，未提交／推送。下一步接真实call分配与生产环境。下方历史原文不改写。
<!-- time-ready-entry-checkpoint-end -->

<!-- time-ready-api-checkpoint-start -->
## 局部检查点：三API和内部调度器共用tick的时间／任务／就绪表Inv

第177步重证原OSTimeGet／OSTimeSet在既有 `V293_time_ready_inv` 下的真实builder契约，保留TCB／bitmap／priority-table所有权并在退出临界区前恢复同一强Inv。稳定接口 `V293_ready_clock_components_checked` 将原OSVersion／TimeSet／TimeGet与内部OSSchedNew的GoodI、WFAPI、WFIFun及disjoint义务接到同一Spec／Inv／name-only LocalInv；不新增Inv或修改源码／AST／框架。见[第177步中文说明](audit/STAGE177_TIME_READY_API.md)。

独立强core物理见证和分别只改clock／ready字节的对照；ready负控显式复用旧冻结store，不能把clock早拒当作ready有效。真实builder和抽象返回检查不冒充执行trace；尚无完整APIcaller与强core的联合分配见证。最终编译、25根假设闭包、递归coqchk及全套旧失败ID对照见本步verification.json，不宣称全套全绿。

**只是局部组件统一不变量，不是完整全程序或tick／hook／ISR已安装。** 完整初始化、生产LocalInv与函数环境、同程序K1–K4及GOOD_OS仍开放。六门94/1/1/1/1/0，第一阶段未完成、uCOS3未开始、目标active；未提交／推送。下一步补联合资源可满足性并继续连接生产环境；旧证据不改写。下方历史原文保留。
<!-- time-ready-api-checkpoint-end -->

<!-- tick-shared-snapshot-checkpoint-start -->
## 局部检查点：固定 Spec 接收 ct／es／si／ci 共享快照

第176步在175的clock／run基础上，继续使用已有lg构造子选择当前任务、事件映射、中断栈和临界区栈。稳定接口 `V293_tick_shared_internal_contract` 量化所有vl／lg，内部检查ct=tid、run范围和topis边界，连接真实BuildPreI／BuildRetI、原完整body及call_rule；未添加空hook。详见[第176步中文说明](audit/STAGE176_TICK_SHARED_SNAPSHOT.md)。

同一个SNspec下，完整入口对任意有效es／si／ci独立非空；同一非空端点分别只改es、si、ci，由实际事件槽、Ais、Acs拒绝，错误si=[2]仍在范围内。ct负控只归于身份门，实际curtid另有独立读取证据。fixture的事件槽替换及aux运输不是kernel／ISR执行，不证明等待队列全局一致性；物理owner非空实例目前仅WhileReady。缺失hook无下一步且直接反证EqDom，不能推导WFFunEnv或完整trace。

本步生产／探针编译与构建通过；最终29根假设闭包、递归coqchk和完整测试核对结果以[verification.json](audit/logs/stage176-tick-shared-snapshot/verification.json)为准。保留旧423失败／1错误，不修改原coverage identity和六行whitespace问题；全部编译诊断与快照保留。未改C／配置／AST／框架／旧证明测试和冻结证据。

**这里只统一共享快照的条件规格，不是生产ISR／hook或全局规格安装，更不是最终GOOD_OS。** bindings／地址／R仍固定，IE=false／isr全清、有限未挂起链与旧LocalInv不变。六门94/1/1/1/1/0，第一阶段和同程序K1–K4未完成、uCOS3未开始、总目标active，不提交／推送。下一步接可变任务资源、生产边界与全程序环境；本步已解决的es／si／ci固定Spec缺口不重复计作未完成。下方历史原文保持。
<!-- tick-shared-snapshot-checkpoint-end -->

<!-- tick-uniform-spec-checkpoint-start -->
## 局部检查点：固定 Spec 内以逻辑参数选择 clock／run

第175步不再随 clock／run 更换 hook 规格：复用框架已有 lg 通道，同一个 hook／tick Spec 连接真实 call_rule、原完整 body 和 BuildPreI／BuildRetI。稳定接口 `V293_tick_uniform_internal_contract` 对全部 vl／lg 量化；有效索引证明原 body，错误 lg／run>=256 前置为 Afalse。其他固定资源参数与既有不变量前提不变。详见[第175步中文说明](audit/STAGE175_TICK_UNIFORM_SPEC.md)。

同一真实分配后完整入口独立非空；只改 clock37→38 时由实际 ostmid 槽拒绝，只改 run0→255 时由物理 Tint8 load 拒绝。后者两者 ghost code 完全相同，避免以不同分支的早拒绝冒充 downstream 检查。停机完整 None post 独立非空，同一端点只换 Some 即拒绝；仍只是 ghost END fixture，未执行 hook／clock++，运行 post 独立非空和完整 trace 不在本步。当前程序仍缺 hook，探针直接反证 EqDom，不能推导 WFFunEnv。

生产／探针及构建通过；24根假设检查、两个新入口及递归依赖 coqchk 通过，565份 Coq 输入检查期间不变，允许假设集合未扩大；不是全部旧入口重检。新增5项回归通过；全套2038项保留旧423失败／1错误及完全相同完整ID。13次编译、9次非零诊断及全部快照保留。旧 coverage identity 与六行 whitespace 问题不改写；清理及最终核对见[verification.json](audit/logs/stage175-tick-uniform-spec/verification.json)。

**这里只统一 clock／run，不是全局可变 task／ISR 规格已安装，也不是 CPU hook 实现或最终 GOOD_OS。** bindings、ct/es、全局地址、R 与 IRQ snapshot 仍为固定外部参数；保持 IE=false／ISRclear、合法有限未挂起链与旧 LocalInv。未改 C／配置／AST／框架／旧证明／旧测试／旧冻结证据。六门94/1/1/1/1/0，无新增无条件整函数信用；生产 ISR／hook、初始化／WFIFun／GOOD_OS 与同程序 K1–K4 仍开放。第一阶段未完成，uCOS3 未开始，总目标 active，不提交／推送。下一步连接可变共享状态、生产 ISR／hook 和全程序函数环境；本步 clock／run 固定规格缺口不再重复计作未完成。下方历史原文保持。
<!-- tick-uniform-spec-checkpoint-end -->

<!-- tick-builder-locals-checkpoint-start -->
## 局部检查点：任意 raw local 初值接真实函数 builder

第174步把原 tick 完整 body 接到框架真正的 `BuildPreI`／`BuildRetI`：saved／scan 均接受任意 raw 初值，真正赋值 saved=0；hook 只持共享资源，两个 local 留在 caller frame。稳定接口为 `V293_tick_builder_internal_contract`，仍明确依赖 hook Spec、环境与既有不变量等前提。详见[第174步中文说明](audit/STAGE174_TICK_BUILDER_LOCALS.md)。

实际分配后完整 builder pre 独立非空；同一端点只改 scan 见证即拒绝。另在同一分配内存独立 store scan=idle 后，新完整入口及 builder pre 成立，旧 Vundef 接口在同一新 Ms 拒绝。该 store 只是 fixture，不是新增 C 初始化。完整停机 builder None post 独立非空，同一状态只换 Some 即拒绝；它仅指定 ghost END，未执行 clock++／hook，运行完整 post 独立非空仍未建立，不能拼成完整 tick trace。

生产／探针、28根假设检查、两个新入口及递归依赖的 coqchk 通过，563份 Coq 输入检查期间不变，允许假设未扩大；不是全部旧入口重检。新增5项回归通过，全套2033项保留旧423失败／1错误及相同完整ID。27次编译、20次非零诊断全部保留。注释禁用词触发结构测试后，没有削弱门；停止首次 trust、只改注释，再重编译并完整重跑，失败及中断证据保留。构建、清理及最终核对见[verification.json](audit/logs/stage174-tick-builder-locals/verification.json)；旧 coverage identity 与六行 whitespace 失败不改写。

**这是外部 clock／run 等参数固定的契约族中的条件函数 builder 义务，不是统一全局规格、WFFunEnv、CPU hook 实现或最终 GOOD_OS。** 未改 C／配置／AST／框架／旧证明；仍限 IE=false／ISRclear、合法有限未挂起链及旧 LocalInv。六门94/1/1/1/1/0，不授予无条件整函数信用。下一步处理生产共享资源／ISR、真实 hook 的保持与返回、全程序函数环境；本步 builder 局部缺口不再重复计作未完成。初始化／WFIFun／GOOD_OS 与同程序 K1–K4 仍开放，第一阶段未完成、uCOS3 未开始、总目标 active，不提交／推送。下方历史原文保持。
<!-- tick-builder-locals-checkpoint-end -->

<!-- tick-body-hoare-checkpoint-start -->
## 局部检查点：原 tick 完整 body 的条件 Hoare 连接

第173步把真实 `cpu_sr=0`、原 hook 调用契约、完整原后缀及 `sret` 接成精确 body 的 `InfRules`，并实例化条件 `RuleSem`。入口 raw saved 可为实际分配的 `Vundef`；独立真实 call→两分配→赋值 trace 已组合到 hook 调用点。初始化前同一Mi接受Vundef／拒绝0，赋值后同一Ms接受0／拒绝Vundef，canary99与caller槽保持。详见[第173步中文说明](audit/STAGE173_TICK_BODY_HOARE.md)。

完整返回断言仅接受None；停机完整post独立非空，同一状态只将None改Some即拒绝；给定该post能执行真实返回并释放两local全部字节。停机fixture只指定ghost END，未执行clock++或hook，运行完整post独立非空未建立；不能拼成完整tick实际trace。

生产／探针及构建通过；20个根、两个新入口及递归依赖的coqchk通过，561份Coq输入检查期间不变，允许假设未扩大（本步实际使用既有classic、functionalext与Eqdep），不是全入口重检。新增5项回归通过；全套2028项保留旧423失败／1错误及完整相同ID集合。16次编译、12次非零诊断与快照全部保留；一次性材料清理与最终核对见[verification.json](audit/logs/stage173-tick-body-hoare/verification.json)。旧coverage identity及六行whitespace失败不改写。

**这是带明确hook Spec的body级证明，尚未连接BuildPreI／BuildRetI，不是WFFunEnv、CPU hook实现或最终GOOD_OS。** raw builder可表示Vundef，但任意scan初值与函数级资源组织仍需连接。未改C／配置／AST／框架／旧证明；仍限IE=false／ISRclear、合法有限未挂起链及旧LocalInv。六门94/1/1/1/1/0，无整函数信用。下一步补builder前后条件连接；CPU hook、生产ISR、初始化／WFIFun／GOOD_OS与同程序K1–K4仍开放。第一阶段未完成，uCOS3未开始，总目标active，不提交／推送。下方历史原文保持。
<!-- tick-body-hoare-checkpoint-end -->

<!-- tick-return-tail-checkpoint-start -->
## 局部检查点：原 tick 后缀接真实返回及两个 local 释放

第172步从原 `scan_switch_result` 拆出两个 local 与精确剩余资源，执行真实 `sret/free`，恢复 caller 环境；不假设释放成功。覆盖 getaddr 两种顺序，两槽各4字节在同一终点全部清空，SWINV、链残余、globals 与 caller frame 保持。callee 绑定仅在蕴含空资源时剥离，其他资源先证 GoodFun 再运输环境。详见[第172步中文说明](audit/STAGE172_TICK_RETURN_TAIL.md)。

同一实际分配Ms上的独立返回fixture保留canary90=99与旧槽70；同一Mf上分别只额外要求已释放scan或saved所有权均拒绝。完整停机post另证可满足并驱动稳定返回接口；该fixture只放置ghost END，未执行clock++或缺失hook。prefix与tail是两段独立trace，不能拼成完整tick；运行分支完整post的非空实例本步未建立。

生产／探针、构建通过；20个根及两新入口连同递归依赖的coqchk通过，559份Coq输入检查期间不变，允许假设未扩大，不是全入口重检。新增5项回归通过；全套2023项保留旧423失败／1错误及完全相同ID集合。16次编译、10次非零诊断全部保留。逐项核对后清理9项一次性材料697870字节、恢复两份既有缓存，保留可复用证明产品。最终核对见[verification.json](audit/logs/stage172-tick-return-tail/verification.json)。

**CPU hook实现保持／返回、完整tick函数级证明、生产ISR、初始化／WFIFun／GOOD_OS和同程序K1–K4仍未闭合。** 不改C／配置／AST／框架／旧证明；仍限IE=false／ISRclear、合法有限未挂起链与旧LocalInv。六门94/1/1/1/1/0，无整函数信用；旧coverage identity失败及六行whitespace保留。下一步把真实返回尾部接到函数级接口，同时保留外部hook义务。第一阶段未完成，uCOS3未开始，总目标active，不提交／推送。下方历史原文保持。
<!-- tick-return-tail-checkpoint-end -->

<!-- tick-hook-contract-checkpoint-start -->
## 局部检查点：真实 tick hook 调用契约接入原后缀

第171步以真正 `call_rule` 连接 `scall hook []` 与已有原 tick 后缀；callee 资源单独证明 `GoodFunAsrt`，局部绑定保留在 caller frame。使用170实际分配后同一 Ms，核对 scan=`Vundef`、saved=0、canary99及原caller槽。固定资源／frame分别只改空参数或void返回即拒绝；saved0→1负控与局部绑定非GoodFun检查独立。另证固定程序缺失 hook body 时 `sfexec` 无下一步、不能返回，不把 Spec 当作实现。见[第171步中文说明](audit/STAGE171_TICK_HOOK_CONTRACT.md)。

生产／探针编译及构建通过；19根假设检查和两个新入口连同递归依赖的 `coqchk` 通过，557份 Coq 输入在检查期间未变，允许假设未扩大。这不是此前400入口全部重检。新增5项回归通过；全套2018项保留旧423失败／1错误及完整相同ID集合。16次编译、14次非零的快照／日志保留；逐项确认后清理9项一次性材料697557字节、恢复既有两缓存，保留可复用证明产品。构建、旧审计及最终文件核对见[verification.json](audit/logs/stage171-tick-hook-contract/verification.json)。

**hook资源保持和返回仍是外部实现义务，本步只有带明确Spec条件的逻辑调用连接，没有实际hook返回trace。** 未改C／配置／AST／框架／旧证明；仍限IE=false、ISRclear、有限合法未挂起链和旧LocalInv。完整tick返回／释放、生产ISR、初始化／WFIFun／GOOD_OS和同程序K1–K4尚未闭合；六门94/1/1/1/1/0，没有新整函数信用。`make audit`旧coverage identity失败及旧六行whitespace保留。下一步沿真实函数返回和局部释放连接，不凭空补hook body。第一阶段未完成，uCOS3未开始，总目标active，不提交／推送。下方历史原文保持。
<!-- tick-hook-contract-checkpoint-end -->

<!-- tick-call-context-checkpoint-start -->
## 局部检查点：真实 tick 调用分配接入共享后缀入口

第170步把真实 `OSTimeTick` 调用、两 local 分配与 `cpu_sr=0` 初始化接到第169步共享后缀入口：同一实际分配后内存上，scan171为 `Vundef`、saved172为0，原槽70仍是 caller 数据。新 callee 绑定独立建立，只对已证明 `GoodFunAsrt` 的空间资源运输环境，不搬运旧 `ptcb→70` 绑定。没有新 Inv、执行 oracle 或 C／AST／旧证明修改。详见[第170步中文说明](audit/STAGE170_TICK_CALL_CONTEXT.md)。

同一实际端点核对完整入口、两新槽、canary90=99、原槽70及只将 saved 见证0→1后的完整错误入口拒绝；旧绑定负控只声称局部绑定资源拒绝。run=1、0/255及最大clock入口均实例化；最大clock入口不冒充本步回绕执行。后缀正式 InfRules 保留 saved0 frame，并由 RuleSound 导出 RuleSem。

23个新增证明根、340活动＋60探针模块独立检查通过，555份Coq输入在检查期间不变，允许假设未扩大。新增5项回归通过；全套2013项保留旧423失败／1错误，完整ID集合及最终核对见[verification.json](audit/logs/stage170-tick-call-context/verification.json)。15次编译快照与12次非零结果全部保留。逐项确认后仅清理8项一次性材料689181字节，恢复两份既有缓存，保留证据与可复用产品；旧审计identity及六行whitespace问题不改写。

**真实trace只到CPU hook调用点，尚未证明hook返回；不是完整tick／生产ISR或初始化证明。** 资源前提明确在最终callee环境评价，不等于任意caller断言运输。仍限IE=false、ISRclear、合法有限未挂起链与旧空LocalInv。六门94/1/1/1/1/0，无新增整函数信用；完整函数／API／ISR、初始化／WFIFun／GOOD_OS及同程序K1–K4仍开放。下一步连接真实hook调用契约、资源保持与返回。第一阶段未完成，uCOS3未开始，总目标active，不提交／推送。下方历史原文保持。
<!-- tick-call-context-checkpoint-end -->

<!-- tick-scan-slot-checkpoint-start -->
## 局部检查点：原 tick 接受真正未初始化的扫描槽

第169步修正第168步共享入口仍要求 typed scan 的缺口。真实 `OSTimeTick` 的 `ptcb` 未初始化；新接口用 raw `Amapsto` 拥有 `Vundef`，而非假装它是 pointer。run=1 先安全覆盖 scan 再接原完整 while；run=0/255 保留 `Vundef`。时钟与 task／ready 资源仍取还同一个 `V293_time_ready_inv`，没有新 Inv、执行 oracle 或源码改动。详见[第169步中文说明](audit/STAGE169_TICK_SCAN_SLOT.md)。

新入口从原四任务真实字节资源以保持权限的 `store Vundef` 独立构造；它是 fixture，不是实际 callee allocation。相同 M 独立执行原后 hook，核对 scan、clock、链／bitmap／idle字段、canary99与残余；运行／停机／最大时钟回绕均检查。同一初始堆只把 scan 见证换成 idle 指针即拒绝，typed Vundef 也拒绝；同一新停机 Mf 更新抽象 clock 可恢复完整新 SWINV 入口，只中和该 clock 后连 time-ready core ** Atrue 也拒绝。任务中和对照仍是明确标识的旧端点，不冒充新 RuleSem 执行。

生产及完整探针编译、构建及清理后构建退出0；30个新增证明根、339活动＋59探针模块独立检查通过，553份 Coq 输入在检查期间不变，允许假设集合未扩大。新增5项回归通过；全套2008项保留旧423失败／1错误，逐轮完整 ID 比较及旧文件核对见[verification.json](audit/logs/stage169-tick-scan-slot/verification.json)。20次编译快照、17次非零结果全部保留，其中主动性能中断和证明搜索超时不当作语义反例。逐项确认后清理10项一次性材料696645字节、恢复两份既有缓存；诊断证据与可复用 Coq 产品保留。旧审计 identity 及六行 whitespace 问题不变。

**尚未把真实两 local 分配及 CPU hook 接到本步共享入口，也不是生产 ISR／初始化或完整 tick 的证明。** SWINV 仍限 IE=false／ISRclear、合法未挂起有限链及旧空 LocalInv；完整 API／ISR、初始化／WFIFun／GOOD_OS 和同程序 K1–K4 仍开放。六门94/1/1/1/1/0，无新增整函数信用。下一步连接实际局部分配、callee 环境与 hook 返回，不能再假设初始 scan 为指针。第一阶段未完成，uCOS3未开始，总目标 active，不提交／推送。下方历史原文保持。
<!-- tick-scan-slot-checkpoint-end -->

<!-- tick-switch-boundary-checkpoint-start -->
## 局部检查点：原 tick 后 hook 从既有共享 SWINV 取还资源

第168步将前一步完整原后 hook 接到已有 `V293_time_ready_inv` 的 `SWINV` 边界：按同一抽象槽对齐隐藏见证，取出 task／ready／clock 资源，执行真实 clock++、运行判断、head 赋值和原 while，最后归还同一个共享不变量及精确 scan／residual／globals／frame。caller 不再提前提供拆开的 canonical core；只用 additive view 观察同一抽象 map，并显式提供缺失链字段补片。没有新 Inv、执行 oracle 或将中断标志非法放入 GoodFrm。详见[第168步中文说明](audit/STAGE168_TICK_SWITCH_BOUNDARY.md)。

独立四任务实际字节堆构造新 SWINV 入口，不调用新 opening／主定理。只改 view clock 37→38 或 view taskmap 为空，固定同一 Inv／物理堆／实际抽象槽／补片后均拒绝；不是修改 bitmap 的早拒。run=1、0/255 及最大时钟入口均实例化；原操作执行明确复用167。在同一个实际停机 Mf 上，正确抽象时钟能恢复新完整 SWINV 入口，只中和抽象 clock 后连 SWINV ** Atrue 也被拒绝。任务负控明确保留旧执行端点身份，不冒充新 RuleSem 运行。

正式源及完整探针编译、构建退出0；24个新增证明根、338活动＋58探针模块独立检查通过，551份 Coq 输入检查期间不变，允许假设未扩大。新增5项回归全部通过，三轮全套2003项保持旧423失败／1错误及完整旧 ID 集合。已逐项清理8份临时材料689123字节，恢复两份既有缓存，清理后构建退出0。旧文件与上一步冻结 manifest 核对及最终验收结果见[本步 verification.json](audit/logs/stage168-tick-switch-boundary/verification.json)，编译失败快照全部保留。旧审计 identity 与六行 whitespace 保持，不改写旧失败刷绿。

**本步只覆盖 SWINV 固有 IE=false／ISRclear 边界，非 enabled=true 首次借出或统一生产 ISR 安装。** 既有不变量 GoodI、有限未挂起链及旧空 LocalInv 不等于初始化可达。生产 Inv／LocalInv／ISR、CPU hook、完整 tick／API、初始化／WFIFun／GOOD_OS及同程序 K1–K4 仍开放；六门94/1/1/1/1/0，无新增整函数信用。第一阶段未完成，uCOS3未开始，总目标 active，不提交／推送。下一步将当前共享边界接到真实中断与完整函数上下文。下方历史原文保持。
<!-- tick-switch-boundary-checkpoint-end -->

<!-- tick-post-hook-core-checkpoint-start -->
## 局部检查点：同一共享 core 连接完整原 tick 后 hook 路径

第167步将第166步 canonical task／ready／clock 入口接到原完整后 hook 后缀：真实 clock++ 与抽象时钟同步，再读取真实 OSRunning；仅 run=1 时赋值 head 并执行原 while，run=0/255 只更新时间。运行路径归还更新后的共享 core、scan、全部残余与 frame，不预设执行／求值成功。详见[第167步中文说明](audit/STAGE167_TICK_POST_HOOK_CORE.md)。

新四任务同块字节堆独立构造入口，实际13项优先级表、在任务表内的 readonly current、canary99、合法栈顶1及两种初始 IE 均保留；初始 scan=idle 不等于非空 head。原操作语义在新堆上检查完整后缀及最大时钟回绕。停机路径在同一真实 Mf 上，正确抽象时钟可恢复完整 canonical core；只中和 ostmid 后由实际 clock agreement 拒绝，其他资源不变。任务更新中和负控明确复用第165步，分别命名两个执行端点，不冒充新 RuleSem 运行。

实测：生产和最终探针编译、构建与清理后构建退出0；39个新增根、337活动＋57探针模块独立检查通过，549份 Coq 输入检查期间不变，允许假设未扩大。新增5项回归通过；三轮全套1998项均保持旧423失败／1错误，完整旧 ID 集合相同。34次编译快照及29次非零结果保留，其中5次主动性能中断不当作语义反例。逐项确认后清理8项691141字节，恢复两份既有缓存；核对29407份旧文件和第166步冻结 manifest。验收见[verification.json](audit/logs/stage167-tick-post-hook-core/verification.json)；旧审计 identity 及六行 whitespace 问题保留，不改写旧失败刷绿。

caller 仍先持有 canonical core，尚非生产 IRQ 借出；仍限制合法未挂起有限链，LocalInv 为空旧见证而非初始化可达。生产 Inv／LocalInv、CPU hook、完整 tick／API／ISR、初始化／WFIFun／GOOD_OS及同程序 K1–K4 仍开放；六门94/1/1/1/1/0，无新增整函数信用。下一步连接生产不变量的真实资源转移与函数前后文。第一阶段未完成，uCOS3未开始，总目标 active，不提交／推送。下方历史原文不改写。
<!-- tick-post-hook-core-checkpoint-end -->

<!-- tick-chain-open-checkpoint-start -->
## 局部检查点：从同一 canonical 共享资源打开完整 tick 任务链

第166步补上第165步的入口缺口：从同一canonical task／ready／clock联合资源打开完整合法混合链，接原完整while的正式InfRules与有序抽象更新，无损归还共享core、scan、全部residual和frame。caller不再提前提供全链raw，只提供canonical真正缺失的Next、time pend、ready delay／pend。详见[第166步中文说明](audit/STAGE166_TICK_CHAIN_OPEN.md)。

四任务同块字节堆直接打包新canonical入口，不调用旧raw入口或新opening来制造入口。只把事件pend提示7改为99，入口／taskmap／抽象程序／补片不变；正式打开后用真实load及有界byte单射性得到实际pend=7。分别只改time／ready pend补片7→99时，同一堆上的错误入口均拒绝。实际13项table、readonly current=ready4且在taskmap内、clock37、canary99和合法栈顶1保持；两种初始IE均实例化。原操作执行及同Mf抽象更新中和负控明确复用165，不冒充新RuleSem运行。

实测：生产及完整探针编译、构建及清理后重建退出0；26个新增根、336活动＋56探针模块独立检查通过，547份Coq输入检查期间不变，允许假设未扩大。新增7项回归通过；三轮全套1993项仍为旧423失败／1错误，完整旧ID集合保持。24次编译快照及18次非零结果保留，其中一次主动性能中断不当作语义反例。逐项确认后清理8项688632字节，恢复两份既有缓存；核对29280份旧文件及第165步冻结manifest。验收见[verification.json](audit/logs/stage166-tick-chain-open/verification.json)，旧审计identity及六行whitespace问题保持，不改写旧失败刷绿。

范围仍是合法未挂起链、完整任务域匹配链加idle；不是任意生产任务状态。两种初始IE不等于生产IRQ借出，LocalInv仍旧空见证而非初始化可达。生产Inv／LocalInv、CPU hook、完整tick／API／ISR、初始化／WFIFun／GOOD_OS及同程序K1–K4仍开放；六门94/1/1/1/1/0，无新增整函数信用。下一步将canonical入口与精确残余接到生产不变量及后hook路径。第一阶段未完成，uCOS3未开始，总目标active，不提交／推送。下方历史原文不改写。
<!-- tick-chain-open-checkpoint-end -->

<!-- tick-while-core-checkpoint-start -->
## 局部检查点：完整原 while 同步抽象任务链并归还共享 core

第165步将完整原 `swhile` 的正式 InfRules 与既有逐节点有序抽象链接通，更新同一任务表后，无损归还 task／ready／table／clock core、scan、全部链残余和 caller frame。未引入 batch primitive 或执行成功 oracle；详见[第165步中文说明](audit/STAGE165_TICK_WHILE_CORE.md)。

新四任务同块 encoded bytes 联合实际13项优先级表、readonly current、clock37、canary99及合法栈顶1构造入口，当前 ready4 确实在任务表内。混合链包含事件到期、时间倒计时、ready 与 idle；两种初始 IE 的独立原操作语义执行检查 row16／20、group3 和精确残余。在同一个真实 Mf 上只中和抽象任务更新，由 priority10 的 task／ready 不一致拒绝，而非空 bitmap 早拒。独立执行不是新 RuleSem 的运行实验。

实测：生产与完整探针编译、构建及清理后重建退出0；27个新增根、335活动＋55探针模块独立检查通过，545份Coq输入检查期间不变，允许假设集合未扩大。新增7项回归通过；全套1986项仍为旧423失败／1错误，完整旧ID集合比较见各轮日志。20次正式编译（17次非零）与13次隔离编译（11次非零）的源码快照／日志均保留；先确认再清理20项一次性文件3734158字节，恢复两份既有缓存。最终核对29124份旧文件，旧审计identity及六行whitespace问题保持；见[本步证据目录](audit/logs/stage165-tick-while-core/)及其中 verification.json。不重写旧冻结证据以制造全绿。

入口仍要求 caller 持有全链 raw 字段，尚无任意 canonical core 到整链 raw 的打开证明；两种 IE 局部规则不等于生产 IRQ 借出。LocalInv 仍为旧空见证，非初始化可达性。CPU hook、完整 tick／API／ISR、生产 Inv／LocalInv、初始化／WFIFun／GOOD_OS 和同程序 K1–K4 仍开放；六门94/1/1/1/1/0，无新增整函数信用。下一步从同一 canonical taskmap 打开全链，只将真正缺失的字段留给补片。第一阶段未完成，uCOS3 未开始，总目标 active，不提交／推送。下方历史原文不改写。
<!-- tick-while-core-checkpoint-end -->

<!-- tick-core-focus-checkpoint-start -->
## 局部检查点：从完整共享 core 取出真实等待节点

第164步不再要求caller提前拆出focused节点：按同一抽象任务表的真实lookup，从完整canonical records取出等待记录和隐藏ready／pend见证，执行原tick单次迭代，再归还同一clock/task/ready core及全部残余和frame。事件pend来自记录自身，time pend及Next等缺失字段仍须显式提供。详见[第164步中文说明](audit/STAGE164_TICK_CORE_FOCUS.md)。

非空两任务encoded bytes联合构造新入口，不调用旧入口定理；同一core和物理堆只改lookup优先级6→7后拒绝。独立pend7堆核对事件隐藏值和time补片来源；原到期／倒计时操作执行及同输出抽象更新中和负控明确复用旧证明，不冒充新RuleSem运行。

实测：构建与清理后重建退出0；26个新增根、334活动＋54探针模块独立检查通过，543份Coq输入检查期间不变，允许假设集合未扩大。新增7项回归通过；全套1979项仍为旧423失败／1错误，完整旧ID集合保持。14次编译快照含10次非零结果（含一次主动中断）全部保留；逐项确认后清理8项一次性文件687666字节，恢复两份既有缓存。29028份旧文件按基线核对；旧审计identity和六行whitespace问题保持。验收见[verification.json](audit/logs/stage164-tick-core-focus/verification.json)。

本步仅为IE=false的单个未挂起等待节点，需真实lookup及额外链字段；不是任意节点分类、IE=true借入或生产ISR／完整while／tick／API。当前fixture任务不在任务表，LocalInv仍为旧空见证，不声称初始化可达。生产Inv／LocalInv、CPU hook、初始化／WFIFun／GOOD_OS及同程序K1–K4仍开放；六门94/1/1/1/1/0，无新增整函数信用。下一步把整链分类和共享core取还组合，而非继续假设caller持有全链raw字段。第一阶段未完成，uCOS3未开始；总目标active，不提交／推送。下方历史原文不改写。
<!-- tick-core-focus-checkpoint-end -->

<!-- tick-ready-update-checkpoint-start -->
## 局部检查点：原 tick 等待节点更新后归还同一共享 core

第163步连接原 `encrit ; (delay ; (advance ; excrit))` 单次迭代的真实TCB／bitmap／scan写入、既有合法抽象任务步和无损归还：同一组task/event/current/time槽绑定更新后的TCB／ready／table与原clock，显式保留Next、到期后delay／pend／event残余及完整caller frame。主InfRules不预设执行或求值成功，RuleSem只由RuleSound导出。详见[第163步中文说明](audit/STAGE163_TICK_READY_UPDATE.md)。

两任务独立encoded bytes联合构造合法栈顶1、readonly current、clock37与canary99，排除局部契约空真。原独立操作语义检查d=1到期bitmap80／group1；同一实际Mf、END及控制状态仅中和抽象任务更新，由priority6的task／ready不一致拒绝，而非非空bitmap早拒。d=0／3不误唤醒，残余字段精确归还；不把旧操作执行冒充新RuleSem运行。

实测：构建与清理后重建退出0；40个新增根、333活动＋53探针模块独立检查通过，541份Coq输入检查期间不变，允许假设集合未扩大。新增7项回归通过；三轮全套均1972项、423失败／1错误，完整旧ID集合保持。53次编译快照含45次失败保留；逐项确认后清理8项一次性文件680190字节，恢复两份既有缓存。28815份旧文件仅说明、项目入口与生成依赖有预期差异。旧审计identity和六行whitespace问题保持；验收见[verification.json](audit/logs/stage163-tick-ready-update/verification.json)。

本步仅为IE=false、caller显式持有focused资源的单个未挂起等待节点，尚未证明任意core可打开；不是IE=true借入、生产ISR安装或完整while／tick／API。当前任务不在fixture任务表、LocalInv仍为旧空见证，不声称初始化可达。生产Inv／LocalInv、CPU hook、初始化／WFIFun／GOOD_OS及同程序K1–K4仍开放，六门94/1/1/1/1/0，无新增整函数信用。第一阶段未完成，uCOS3未开始；总目标active，不提交／推送。下方历史原文不改写。
<!-- tick-ready-update-checkpoint-end -->

<!-- time-ready-shared-checkpoint-start -->
## 局部检查点：同一共享不变量的时钟借还

第162步把物理 clock 与已有 TCB／ready／table 资源绑定到同一组 abstract task/time witnesses，避免重复拥有抽象槽。闭合 `V293_tick_ready_clock_prefix` 通过真实 encrit／clock++／excrit 借出、同步和归还，不要求 caller 另持 clock；右结合 `with_tail` 仍显式要求 continuation 的独立证明。详见[第162步中文说明](audit/STAGE162_TIME_READY_SHARED.md)。

两个非空任务及分离编码字节给出新SWINVt实例；只改clock且保留abstract time被拒绝。ready单字节16→32负控保持其他地址和clock，前后均非空且group=1，由实际task4 membership矛盾拒绝，而非早期空bitmap检查。

实测：构建与清理后重建退出0；41个新增根及332活动＋52探针模块独立检查通过，539份Coq输入检查期间不变，假设集合未扩大。新增7项回归通过；三轮全套均1965项、423失败／1错误，完整旧ID集合保持。24次编译快照含17次失败保留；逐一确认后清理8项一次性文件673392字节、恢复两份既有缓存；26766份旧文件仅说明、项目入口和生成依赖有预期差异。旧审计identity和六行whitespace问题保持；验收见[verification.json](audit/logs/stage162-time-ready-shared/verification.json)。

本步仅为allISR=false、IE=true的clockprefix，不是实际ISR或完整tick。GoodI仍用旧见证LocalInv，未完成生产LocalInv／Inv安装、初始化／WFIFun／GOOD_OS和同程序K1–K4；六门94/1/1/1/1/0，无新整函数信用。第一阶段未完成，uCOS3未开始；总目标active，不提交／推送。下方历史原文不改写。
<!-- time-ready-shared-checkpoint-end -->

<!-- tick-post-hook-hoare-checkpoint-start -->
## 已独立验证的局部检查点：原 tick 后 hook 后缀 Hoare

第161步已把第160步原while连接到CPU tick hook返回后的完整原后缀：进入临界区、真实时钟加一、退出临界区、真实OSRunning==1分支、head赋值和原while。主接口 `V293_tick_post_hook_hoare` 直接使用既有AST，组合原InfRules，不预设执行成功或guard值；`RuleSem` 只经既有RuleSound正向导出。详见[第161步中文说明](audit/STAGE161_TICK_POST_HOOK_HOARE.md)，验收见[verification.json](audit/logs/stage161-tick-post-hook-hoare/verification.json)。

六任务入口由encoded bytes独立构造，scan初值为idle而非非空head，含readonly current、canary和合法栈顶1。对两种初始IE，独立旧操作路径检查run=1更新链和bitmap、run=0/255保持链和bitmap；三者时钟均可从0xffffffff回绕为0。真实入口guard的head效果中和检查，以及同一实际输出的错时钟／跳过循环字段负控分别核对关键观测；不冒充删除版AST执行或新RuleSem运行。

实测：构建与清理后重建退出0；28个新增根及331活动＋51探针模块独立检查通过，537份Coq输入检查期间不变，允许假设集合未扩大。新增7项回归通过；三轮全套均1958项、423失败／1错误，完整旧ID集合保留。15次编译快照含12次失败保留；确认后清理8项一次性文件676050字节并恢复两份既有缓存；26677份旧文件仅说明、项目入口和生成依赖有预期差异。

caller仍在进入后缀前拥有raw字段，任意IRQ invariant原样借还不等于生产Inv资源转移。完整tick函数/API/ISR、CPU hook、生产LocalInv／Inv、初始化／WFIFun、GOOD_OS及同程序K1–K4仍开放；六门94/1/1/1/1/0、旧审计identity及旧六行whitespace问题不变，无新增函数覆盖信用。下一步连接生产共享资源借还与完整函数，不能把后缀当整核。第一阶段未完成，uCOS3未开始；总目标active，不提交／推送。下方历史原文不改写。
<!-- tick-post-hook-hoare-checkpoint-end -->

<!-- tick-while-hoare-checkpoint-start -->
## 已独立验证的局部检查点：原 tick while Hoare

第160步将原单次循环体连接为原while的正式InfRules：真实guard由拥有的指针／优先级字节推出，循环不变量精确连接已处理字段、剩余合法链和最终ready位图，复用既有after／fold而非新增执行oracle。RuleSem仅经既有RuleSound正向导出，覆盖任意合法有限链和两种初始IE。详见[第160步中文说明](audit/STAGE160_TICK_WHILE_HOARE.md)，验收见[verification.json](audit/logs/stage160-tick-while-hoare/verification.json)。

六任务混合字节堆联合构造readonly current及canary；合法栈顶1满足INUM=2。实际退出为idle、group3、两行4／4，原guard为假；同一实际Mf上分别拒绝错误指针和错误row，另一正确观测及canary保持。这是独立旧操作路径的对照，不是新RuleSem的运行测试。caller仍须另行持有raw字段；任意IRQ不变量原样借还不等于生产Inv资源转移或初始化可达。

实测：构建与清理后重建退出0；20个新增根及330活动＋50探针模块独立检查通过，535份Coq输入检查期间不变，允许假设集合未扩大。新增7项回归通过；三轮全套均1951项、423失败／1错误，完整旧ID集合保留。20次编译快照含16次失败保留；确认后清理8项一次性文件674316字节并恢复两份既有缓存；26571份旧文件仅说明、项目入口和生成依赖有预期差异。

本步是框架部分正确性／simulation意义下的while，不是一般调度终止性证明或完整tick函数/API/ISR。生产LocalInv／Inv转移、CPU hook、初始化／WFIFun、GOOD_OS和同程序K1–K4仍开放；六门94/1/1/1/1/0及旧审计identity问题不变，无新增函数覆盖信用。下一步把循环规则接入clock／OSRunning／head赋值的正式后hook路径，再连接生产共享资源和完整函数；不能以已有操作端点替代这些Hoare义务。第一阶段未完成，uCOS3未开始；总目标active，不提交／推送。下方历史原文不改写。
<!-- tick-while-hoare-checkpoint-end -->

<!-- tick-iteration-hoare-checkpoint-start -->
## 已独立验证的局部检查点：原 tick 单次循环体 Hoare

第159步连接真实 next 字段读取、原指针赋值及临界区退出：保持 `encrit ; (delay ; (advance ; excrit))` 原 AST 的右结合和顺序，两种初始IE均恢复原ISR／IE／中断栈／临界栈。全部unsigned delay和物理status字节由正式InfRules覆盖，再经既有RuleSound正向导出RuleSem；没有执行／求值oracle前提。详见[第159步中文说明](audit/STAGE159_TICK_ITERATION_HOARE.md)，验收见[verification.json](audit/logs/stage159-tick-iteration-hoare/verification.json)。

IE=true时获取的ISR不变量作为任意原样frame穿过delay／next再归还，未换成空I；raw字段仍须由caller另行持有，未完成生产Inv转移。具体入口使用真实编码字节、readonly current和canary；旧栈顶3不能满足INUM=2的失败保留，新入口和独立操作负控均用合法栈顶1，未改上界。88种分支入口／规则实例排除空真；指针和IE负控分别改变同一实际终态的单一期望，同时保留next／栈和canary，不把独立操作执行冒充新RuleSem运行测试。

实测：构建与清理后重建退出0；12个新增根及329活动＋48探针模块独立检查通过，533份Coq输入在检查期间不变，既有允许假设集合未扩大。新增7项回归通过；全套1944项的423失败／1错误及完整旧ID集合保留。逐项确认后清理9个一次性文件673240字节、恢复两份既有缓存；旧26485份文件仅说明、项目入口和生成依赖有预期差异。15次编译快照含11次失败均保留。

本步仍不是完整while、tick函数/API/ISR或生产Inv；CPU hook、初始化／WFIFun、GOOD_OS和同程序K1–K4仍开放。六门94/1/1/1/1/0及旧审计identity问题不变，无新增函数覆盖信用。下一步连接原while循环不变量与已有链／ready关系，并明确生产IRQ资源转移。第一阶段未完成，uCOS3未开始；总目标active，不提交／推送。下方历史原文不改写。
<!-- tick-iteration-hoare-checkpoint-end -->

<!-- tick-delay-hoare-checkpoint-start -->
## 已独立验证的局部检查点：原tick延时片段的正式Hoare规则

第158步把已有逐步执行向正式规则纵向连接：从原始字段所有权推出真实表达式求值，应用原assign／if／seq规则，得到原`V293_tick_delay`的InfRules，再经既有RuleSound导出RuleSem。不从执行端点倒推Hoare，也不把执行或求值作为主接口前提。详见[第158步中文说明](audit/STAGE158_TICK_DELAY_HOARE.md)，冻结验收见[verification.json](audit/logs/stage158-tick-delay-hoare/verification.json)。

主接口覆盖全部unsigned delay和全部物理status字节：delay0不变、delay1到期、delay≥2递减；到期分支处理pending mask、pend及挂起／ready位，保留同一frame和next字段。独立字节入口还构造真实只读current指针与空见证LocalInv；44种分支实例排除空真。两项负控在旧独立操作语义的同一实际Mf上只替换一个bitmap／pend期望，另一个字段和canary保持；不是新RuleSem的运行测试。

实测：构建与清理后重建退出0；21个新增根及328活动＋47探针模块的独立coqchk通过，531个Coq输入在信任检查期间不变。实际假设为既有classic／funext_dep／Eqdep，允许集合未扩大。新增7项回归通过；三轮全套均1937项、423失败／1错误，完整失败及错误ID集合与第157步一致。逐项核对后删除9个一次性目标共677583字节并恢复两份既有缓存；26311份旧文件仅本说明、状态、项目入口和生成依赖有预期差异。

这只是原延时片段，不含next前移、循环、临界区或CPU hook；生产LocalInv／Inv、完整函数／ISR、初始化／WFIFun、GOOD_OS和同程序K1–K4仍开放。六门94/1/1/1/1/0和旧审计身份问题保留，无新函数覆盖计分。下一步连接原next赋值与循环接口，而不是把尾段执行改名为完整API。第一阶段未完成，uCOS3未开始；总目标active，不提交／推送。下方历史原文不改写。
<!-- tick-delay-hoare-checkpoint-end -->

<!-- tick-reentry-checkpoint-start -->
## 已独立验证的局部检查点：真实 tick 返回资源可用于下一轮原尾段

第157步从真实执行保留的原始字段确定性构造下一轮 binding，保留到期后不再被 ready 布局使用的事件指针；不从隐藏实际取值的存在量化任务记录猜回字段，不重复持有 raw／规范记录权限。详见[第157步中文说明](audit/STAGE157_TICK_REENTRY.md)，冻结验收见[verification.json](audit/logs/stage157-tick-reentry/verification.json)。

非空三任务＋idle实例中，由第一次真实返回堆证明两个局部 block 的全部偏移均可重新分配，再实际执行第二轮分配前缀和原 post-hook 尾段。两次返回实际读取 clock37→38→39、第二任务 delay3→2→1；到期事件指针、已 ready 任务的 pend 和 caller canary 保留。五类已表示等待原因检查 delay0／1／3。单因素对照只从正确第一轮 Mf 分出首个 next 权限，补片保留其余资源及完整抽象状态，而完整再入口 payload 被拒绝。

实测：构建／清理后重建退出0；27个新根的假设检查及独立 coqchk 的327个活动模块＋46个探针模块通过。新增7项测试通过；两轮全套均1930项、423失败／1错误，失败与错误ID逐项保持原样。逐项核对后清理8个一次性文件共673931字节并恢复两份既有缓存；28000份旧文件仅本说明、状态说明、项目入口和生成依赖有预期差异，旧C／Coq源码、测试及冻结证据不改写。

CPU hook仍启用且开放，两轮各自的分配前缀与post-hook尾段未拼成连续完整调用。完整函数Hoare／ISR、生产Inv／初始化／WFIFun、GOOD_OS和同程序K1–K4仍开放；六门94/1/1/1/1/0与旧审计身份问题保留。第一阶段未完成，uCOS3未开始；总目标active，不提交／推送。下一步连接既有ready组件并补齐hook／临界区与生产不变量义务。下方历史原文不改写。
<!-- tick-reentry-checkpoint-end -->

<!-- tick-lossless-fields-checkpoint-start -->
## 已独立验证的局部检查点：tick无损字段与真实返回资源

第156步显式保留next、剩余delay／pend及到期事件指针，证明任意合法有限链的精确字段布局与原始字段资源双向等价；同一返回堆联合拥有规范任务记录和剩余字段，经过原尾段、两次真实free及caller恢复。详见[第156步](audit/STAGE156_TICK_LOSSLESS_FIELDS.md)，冻结验收见[audit/logs/stage156-tick-lossless-fields/verification.json](audit/logs/stage156-tick-lossless-fields/verification.json)。

非空实例检查31个字段单元分成22个规范单元与9个剩余单元，逐项读取实际Mf；仅移走首个next的所有权后，其余资源和抽象状态仍保持，但完整出口约定不成立。实际current指针与四个共享抽象槽均只持有一次，caller9999指向确实拥有的canary90。现有ready_core已封装，但生产LocalInv／Inv和下一次tick整入口尚未闭合；精确布局的逆变换不是任意存在量化record的逆变换，也不是完整TCB。

本步实测：构建与清理后重建退出0；28个新根的假设检查通过，未增加既有允许集合以外的假设；独立coqchk检查325个活动模块＋45个探针模块通过。新增7项测试通过，两轮全套均为1923项、423失败／1错误，旧失败及错误ID完全相同。逐项核对后清理9项一次性产物、恢复两份既有缓存；27880份旧文件仅本说明、状态说明、项目入口和生成依赖有预期差异，旧C／Coq源码、测试及冻结证据不变。

固定CPU hook仍开放：分配前缀与hook返回后尾段未拼成完整调用。完整Hoare／ISR、初始化、WFIFun、GOOD_OS和同程序K1–K4仍开放；六门94/1/1/1/1/0与旧审计身份问题保留。第一阶段未完成，uCOS3未开始；总目标active，不提交／推送。下方历史原文不改写。
<!-- tick-lossless-fields-checkpoint-end -->

<!-- tick-raw-ready-return-checkpoint-start -->
## 已独立验证的局部检查点：真实Vundef入口与tick返回后的联合资源

第155步构造真实两次allocb／saved=0／未初始化ptcb入口，证明原post-hook运行尾段及两局部真实free；恢复非空caller环境，同一返回内存拥有选定任务记录、ready／优先级表、时钟及共享字段。详见[第155步](audit/STAGE155_TICK_RAW_READY_RETURN.md)，验收见本步verification.json。

固定CPUhook保持开放；分配前缀与hook返回后的尾段是两个检查点，未拼成完整调用。出口选定record未命名保留next等额外链字段，尚不能直接重复调用tick或重封闭生产Inv；非空caller未证生产LocalInv。完整Hoare／ISR、初始化、WFIFun、GOOD_OS和同程序K1–K4仍开放。六门94/1/1/1/1/0、旧423失败／1错误及旧审计身份问题保留；uCOS3未开始，总目标active，不提交／推送。下方历史原文不改写。

本步实测：构建与清理后重建退出0；15个新根未增加既有允许集合以外的假设；独立coqchk检查323个活动模块＋44个探针模块通过。新增7项测试通过，两轮全套均为1916项、423失败／1错误，旧失败及错误ID完全相同。逐项核对后清理11项一次性文件／目录并恢复两份既有缓存；27787份旧文件仅说明、项目入口和生成依赖有预期差异，旧C／Coq源码及证据未改写。
<!-- tick-raw-ready-return-checkpoint-end -->

<!-- tick-post-hook-ready-checkpoint-start -->
## 已独立验证的局部检查点：原 tick post-hook 运行路径联合时钟／ready关系

第154步复用原完整后缀执行，把时钟递增、OSRunning=1判断、实际ptcb=head和完整while连接到同一Mf的新任务记录、ready_payload及实际优先级表。非空入口初始ptcb指向idle而不是head；检查时钟37→38、到期与递减，以及只遗漏抽象时钟更新的单因素关系对照。详见[第154步](audit/STAGE154_TICK_POST_HOOK_READY.md)，最终验收以本步 verification.json 为准。

这仍是无交错post-hook运行分支端点，不是整函数Hoare／ISR：保存寄存器初始化、CPU hook、函数分配／返回、生产Inv／初始化／WFIFun、挂起flags及event／pend关系、GOOD_OS和同程序K1–K4仍开放。六门94/1/1/1/1/0、旧423失败／1错误与旧审计身份问题保留。uCOS3未开始，总目标active；不提交／推送。下方历史原文不改写。

本步实测：构建与清理后重建退出0；9个新根的假设检查未增加旧允许集合以外的假设；独立coqchk检查322个活动模块＋43个探针模块通过。新增7项测试通过，两轮全套均为1909项、423失败／1错误，旧失败及错误ID完全相同。已核对后清理8项一次性产物并恢复两份既有缓存；旧源码与证据不变。
<!-- tick-post-hook-ready-checkpoint-end -->

<!-- tick-ready-chain-checkpoint-start -->
## 进行中的检查点：完整 tick while 维护既有 ready／任务／优先级表关系

第153步复用现有 ready_rel／ready_payload，将单节点保持提升到原完整 while：同一实际 Mf 中联合封闭新任务表记录、ready bitmap及实际优先级表。非空四任务共用同一block的不重叠偏移，另构造13项实际指针；漏置优先级10这一位的单因素关系对照被拒绝，旧高行解释也由实际读数20拒绝。其他共享槽位、ready／idle、指针表和canary保持。详见[第153步](audit/STAGE153_TICK_READY_CHAIN.md)，最终结果以本步 verification.json 为准。

这是未挂起有限链的无交错端点连接，不是完整tick Hoare/API、ISR或生产Inv。挂起／flags及event／pend结果关系、初始化、WFIFun、GOOD_OS和同程序K1–K4仍开放；六门94/1/1/1/1/0与旧423失败／1错误及审计身份问题保留。uCOS3未开始，总目标active，未提交／推送。下方历史原文不改写。
<!-- tick-ready-chain-checkpoint-end -->

<!-- tick-while-shared-checkpoint-start -->
## 进行中的检查点：完整 tick while 的共享任务表有序更新

第152步在原完整 while 的同一实际输出内存中，把联合任务记录、指针、bitmap及共享状态重新连接；等待节点按链顺序执行原抽象原语，ready跳过、idle不遍历，旧物理记录由同一入口资源推导。非空探针检查第一个中间抽象状态，并实际执行“仅遗漏第二等待任务”的对照：同一物理输出读到delay2，拒绝只缺这一项更新的delay3任务表。其他共享槽位、ready／idle和canary保持。详见[第152步](audit/STAGE152_TICK_WHILE_SHARED.md)，实际结果以本步 `verification.json` 为准。

这是无交错片段端点连接，不是逐物理小步模拟、完整tick API／ISR或生产Inv。挂起／flags、事件与生产bitmap关系、初始化、WFIFun、GOOD_OS及同程序K1–K4仍开放；六门94/1/1/1/1/0、旧423失败／1错误及旧审计身份失败保留。uCOS3未开始，总目标active；未提交／推送。下方历史原文不改写。
<!-- tick-while-shared-checkpoint-end -->

<!-- tick-while-records-checkpoint-start -->
## 进行中的检查点：原完整 tick while 输出联合任务记录

第151步复用原完整 while 执行，从同一实际输出内存重建任意有限合法 ready／未挂起等待链及 idle 的规范任务记录所有权；idle 优先级只拥有一次。非空探针让两个等待任务、一个 ready 与 idle 共用同一物理 block 的不重叠区间，实际检查到期、第二任务递减、最终 idle 指针和 canary；仅遗漏第二任务抽象记录更新的对照在同一实际输出被拒绝。详见[第151步](audit/STAGE151_TICK_WHILE_RECORDS.md)，最终结果以本步 `verification.json` 为准。

这是完整 while 的物理执行／所有权连接，不是完整抽象 tick 精化；共享任务表批量抽象步、挂起／flags、事件关系、初始化、ISR、生产 Inv／WFIFun、GOOD_OS及同程序K1–K4仍开放。六门94/1/1/1/1/0与旧423失败／1错误及审计身份失败保留；uCOS3未开始，总目标active，未提交／推送。下方历史原文不改写。
<!-- tick-while-records-checkpoint-end -->

<!-- tick-record-reassembly-checkpoint-start -->
## 进行中的检查点：tick 输出重组完整任务记录所有权

第150步把单节点 tick 的输出资源在同一实际内存中重组成规范任务表所有权，并可重新聚焦任意现存任务。两项非空任务共用一个物理block但字节不重叠；实际执行保留另一任务、下一指针和canary。删除另一任务一个字节的执行后关系对照与同字节双占反例均由Coq检查。详见[第150步](audit/STAGE150_TICK_RECORD_REASSEMBLY.md)，最终结果以本步 `verification.json` 为准。

完整任务记录不等于整个TCB；本步未执行下一节点或闭合完整while。挂起／flags、事件关系、初始化、ISR、生产Inv／WFIFun、GOOD_OS及同程序K1–K4仍开放；uCOS3未开始。六门94/1/1/1/1/0与旧423失败／1错误及审计身份失败保留；未提交／推送，总目标active。下方历史原文不改写。
<!-- tick-record-reassembly-checkpoint-end -->

<!-- tick-task-bridge-checkpoint-start -->
## 进行中的检查点：tick 单次循环接入共享任务表

第149步从真实可写资源构造原 tick 单次循环，使用同一个执行后内存连接等待任务记录、任务表、优先级表及 ready bitmap；原抽象步只改任务表槽位。覆盖 time／sem／mbox／q／mutex 的未挂起等待及任意 uint32 倒计时。非空入口、旧 delay、漏设 ready 位、漏改任务表和实际挂起分支均有独立对照。详见[第149步](audit/STAGE149_TICK_TASK_BRIDGE.md)，最终核对以本步 `verification.json` 为准。

这是单节点局部执行连接，不是完整 while／tick／ISR／生产 Inv／WFIFun。挂起与 flags 表示、事件关系、初始化、GOOD_OS 和同程序 K1–K4 仍开放；uCOS3未开始。六门94/1/1/1/1/0和旧失败状态不改写；未提交／推送。下方历史原文保留。
<!-- tick-task-bridge-checkpoint-end -->

<!-- tick-shared-clock-checkpoint-start -->
## 进行中的检查点：OSTimeTick 共享时钟递增

第148步把原 `OSTime++` 接入 getter/setter 共用的时钟 Inv，经原抽象步更新 `ostmid`；证明 `OSRunning != 1` 时原完整 post-hook 尾段，保留未执行的原 while。单因素对照使用同一物理执行后内存：省略抽象更新时不能重新封闭 core，正确更新时可以；另查错误增量和32位回绕。详见[第148步](audit/STAGE148_TICK_SHARED_CLOCK.md)，最终独立检查以本步 `verification.json` 为准。

这是时钟组件，不是整个 OSTimeTick／ISR／生产 Inv／WFIFun。运行中任务唤醒、初始化、GOOD_OS 与同程序 K1–K4 仍开放；六门94/1/1/1/1/0及旧423失败／1错误、审计身份问题不改写。uCOS3未开始，总目标active；未提交／推送。下方历史原文保留。
<!-- tick-shared-clock-checkpoint-end -->

<!-- time-get-api-checkpoint-start -->
## 进行中的检查点：OSTimeGet 读取线性化与共同 API 接入

第147步在原 getter 赋值处用原 spec_prim_step 确定抽象返回值，整个 O 保持不变，再连接原 API builders；共同组件扩展为 OSVersion／OSTimeSet／OSTimeGet 三 API＋OS_SchedNew 内部函数。同一 LocalInv 的非空共享 core／caller 入口可满足；只把读数37改成返回38的对照在原抽象步被拒绝，不依赖入口拒绝。详见[第147步](audit/STAGE147_TIME_GET_API.md)，最终独立检查结果以本步 verification.json 为准。

这是共享时钟组件，不是完整生产 Inv／初始化／ISR／整核 WFIFun；不增加源码函数覆盖信用，不声称退出临界区后时钟不变。GOOD_OS／同程序K1–K4仍开放，六门94/1/1/1/1/0与旧423失败／1错误及审计身份问题保留。uCOS3未开始，总目标active；未提交／推送。下方历史原文不改写。
<!-- time-get-api-checkpoint-end -->

<!-- component-link-checkpoint-start -->
## 进行中的检查点：三函数组件接入原顶层接口

第146步将 OSVersion／OSTimeSet 合入同一 API 表，再与 OS_SchedNew 共用 Spec、scheduler、时钟 Inv 和 name-only LocalInv，建立组件级 WFAPI／WFIFun／GoodI／符号隔离。探针构造同一 LinkLI 的可满足内部入口，消融检查原 pumerge 的实际符号遮蔽。详见[第146步](audit/STAGE146_COMPONENT_LINK.md)，实际独立检查结果以本步 verification.json 为准。

这是两 API＋一个内部函数的组件，不是完整生产程序 WFIFun；完整 Inv、初始化 side_condition、ISR／任务生命周期、源码级 GOOD_OS 和同程序 K1–K4仍未完成。六门94/1/1/1/1/0、旧423失败／1错误及审计身份失败不改写。uCOS3未开始，总目标active；未提交／推送。下方历史原文保留。
<!-- component-link-checkpoint-end -->

<!-- ready-resumption-checkpoint-start -->
## 进行中的检查点：实际切回后的退出、释放与 caller 恢复

第145步由挂起局部的完整所有权构造实际 free，并将原 switch 切回、excrit、return 连成全局轨迹；非空实例从真实 sfexec 经首次切换、初始安装的环境读表／切回 fixture，回到旧 caller。单因素删除保存栈顶的两侧均实际返回，堆相同而 IE 相反。详见[第145步](audit/STAGE145_READY_RESUMPTION.md)，9根及8项新检查的实际结果以本步 checkpoint-report.json／verification.json 为准。

这是条件资源恢复，不是任意干扰保证；Waiting 仍 abstract blocked，环境切回不是生产调度器选择／唤醒。cache 同步、client scall、初始化、所有交错、生产 Inv／WFIFun／GOOD_OS／同程序K1–K4仍开放；uCOS3未开始，总目标active。六门94/1/1/1/1/0、旧423失败／1错误及审计身份问题保留。未提交／推送；下方历史原文不改写。
<!-- ready-resumption-checkpoint-end -->

<!-- ready-cache-contract-checkpoint-start -->
## 进行中的检查点：原切换缓存契约与同步缺口

第144步给出任意合法状态的 cache/current 充要契约，由所有权构造实际 cache store，原 lpstep 保留缓存并绑定同一实际任务表。只省略 cache 写入的对照两侧都实际切换，最终堆只差一个缓存地址；旧完整 sfexec 全局轨迹接到不一致反例。详见[第144步](audit/STAGE144_READY_CACHE_CONTRACT.md)，7根与8项新检查的实际结果以本步 checkpoint-report.json／verification.json 为准。

这是诊断／资源契约，不是已实现端口：未把 store 安装到冻结 C／AST，不能声称 OSPrioCur 同步已修复。初始化、所有交错、旧任务恢复、生产全局 Inv／WFIFun／GOOD_OS／同程序K1–K4仍开放；uCOS3未开始，总目标active。六门94/1/1/1/1/0、旧423失败／1错误与审计身份问题保留；未提交／推送。下方历史原文不改写。
<!-- ready-cache-contract-checkpoint-end -->

<!-- ready-call-global-checkpoint-start -->
## 进行中的检查点：真实调度调用的原全局连续执行

第143步从实际 sfexec OS 边界经原分配／初始化连续全局返回，不再加虚构外层调用；不切换和合法非零 guard 路径恢复 caller／aux、释放四字节。切换路径也接为同一原全局闭包，旧任务保留局部对象／待执行出口，新任务 aux 不变。仅改变最终调用帧保存环境的对照两侧均实际返回、堆／aux 相同，但负例恢复错误环境。详见[第143步](audit/STAGE143_READY_CALL_GLOBAL.md)，13根证明及8项新检查的实际结果以 checkpoint-report.json／verification.json 为准。

这是有限实例无交错存在性，不是 client scall 同内存连接、初始化、所有交错、活动ISR或生产全局 Inv／WFIFun。OSPrioCur 同步与旧任务恢复仍开放；GOOD_OS／同程序K1–K4未完成，uCOS3未开始，总目标active。六门94/1/1/1/1/0、旧423失败／1错误及审计身份问题保留。未提交／推送；下方历史原文不改写。
<!-- ready-call-global-checkpoint-end -->

<!-- ready-full-call-checkpoint-start -->
## 进行中的检查点：调度器真实入口、局部分配与返回释放

第142步从真实 scall／sfexec 调用开始，执行 cpu_sr 的原分配与初始化；同一非空 ready＋waiting 内存上，不切换／guard 阻止路径连续返回、恢复调用者环境并释放四字节。切换路径只接到原 switch：旧任务保留局部对象与待执行出口，不声称已经恢复返回。仅跳过最后一次行政性释放的对照也实际返回，但留下可读取局部对象；其他 block 不变。详见[第142步](audit/STAGE142_READY_FULL_CALL.md)，18根证明及7项新检查的实际结果以 checkpoint-report.json／verification.json 为准。

这是有限实例的无交错存在性；切换分支是局部前缀＋单次原全局步，不是完整全局调用闭包。初始化、所有交错、活动ISR可达性、OSPrioCur 同步、生产全局 Inv／WFIFun／GOOD_OS／同程序K1–K4仍开放。uCOS3未开始，总目标active；六门94/1/1/1/1/0、旧423失败／1错误及审计身份问题保留。未提交／推送；下方历史原文不改写。
<!-- ready-full-call-checkpoint-end -->

<!-- ready-critical-global-checkpoint-start -->
## 进行中的检查点：临界区与两道限制接入原全局调度轨迹

第141步复用原 loststep 闭包，逐步同步真实 ir／aux 到原 lpstep；两种 IE 与任意 critical stack 下，实际 encrit 压栈、excrit 弹栈恢复。两个独立 guard 字节分别控制跳过尾段；零值路径连接真实调用／返回、目标赋值、原分支、计数器及 switch。切换后旧任务保留待执行 excrit；仅删 encrit 的同内存对照实际错误恢复 IE／弹掉外层栈。详见[第141步](audit/STAGE141_READY_CRITICAL_GLOBAL.md)，实际验证以本步 checkpoint-report.json／verification.json 为准。

入口是 cpu_sr 初始化后的规范化片段，不是完整函数调用、初始化可达性、所有交错或生产全局 Inv。current 切至 Ready4 后 cache 仍6；旧任务恢复与端口同步、CurLINV、WFIFun、GOOD_OS／同程序K1–K4仍开放。uCOS3未开始，总目标active；六门94/1/1/1/1/0、旧423失败／1错误及审计身份问题保留。未提交／推送；下方历史原文不改写。
<!-- ready-critical-global-checkpoint-end -->

<!-- ready-global-trace-checkpoint-start -->
## 进行中的检查点：源码片段接入原全局任务执行

第140步将原调用／返回／目标赋值／字节分支／计数器和实际切换接为原 lpstep 的连续闭包；标准传递闭包不增加执行规则。合法外层 OS kcall 与 goodks 推导逐步 InOS，clientst 不变；仅删除外层函数绑定的单因素对照保留源片段执行但拒绝同一入口的 OS 分类。详见[第140步](audit/STAGE140_READY_GLOBAL_TRACE.md)，实际验证以本步 checkpoint-report.json／verification.json 为准。

外层112绑定明确是 enclosing fragment fixture，不是完整 OS_Sched 或初始化可达入口。实际 current 切到 Ready4 后 cache 仍6，源码级同步义务未闭合；切换后空间断言仍使用原调用者环境，不能冒充完整 CurLINV。存在性无交错轨迹不等于所有交错、生产全局 Inv、WFIFun 或 GOOD_OS／同程序K1–K4。uCOS3未开始，总目标active；六门94/1/1/1/1/0、旧423失败／1错误及审计身份问题保留。未提交／推送；下方历史原文不改写。
<!-- ready-global-trace-checkpoint-end -->

<!-- ready-source-tail-checkpoint-start -->
## 进行中的检查点：原优先级分支、计数器与真实切换连接

第139步保留原优先级字节比较，由完整所有权构造实际计数器写入，把原调用／返回／目标赋值和分支／计数器接成连续 cstepstar，终点的确切 switch 代码与同一内存用于原 pswitch_step。联合实例覆盖两分支、UINT32_MAX 回绕、仅改变 cache 一字节的对照；同时证明 Waiting6→Ready4 切换后 cache 仍为6，端口同步义务未闭合。详见[第139步](audit/STAGE139_READY_SOURCE_TAIL.md)，实际验证以本步 checkpoint-report.json／verification.json 为准。

这仍是 unlocked 片段和单次切换的混合执行，不是全局 lpstep 闭包或完整 OS_Sched。有限 Inv 保留不代表缓存一致性或生产全局 Inv 已建立；初始化、API／ISR、Hook／栈、WFIFun、GOOD_OS／同程序K1–K4仍开放。uCOS3未开始，总目标active；六门94/1/1/1/1/0、旧423失败／1错误及审计身份问题保留。未提交／推送；下方历史原文不改写。
<!-- ready-source-tail-checkpoint-end -->

<!-- ready-switch-step-checkpoint-start -->
## 进行中的检查点：真实 current 写入与框架任务切换

第138步由同一 ready Inv 的实际 current 所有权构造成功 store，并直接执行原 pswitch_step；与第137步原调用返回／目标赋值通过同一 Mtarget 连接。非空 ready＋waiting 实例覆盖两种 current、selected 自身局部投影、任务记录与 canary 保留；仅更新 ghost 而省略实际 current 写入时 Inv 拒绝。旧类型绑定保留为共同 pointee type 不可满足的反例，正例只改 current 绑定类型、不改内存字节。详见[第138步](audit/STAGE138_READY_SWITCH_STEP.md)，实测以本步 checkpoint-report.json／verification.json 为准。

这是源片段 cstepstar 与单个真实 lpstep 的共同内存连接，不是完整 OS_Sched 连续控制轨迹。即时 frame 不等于跨恢复的私有资源稳定性。生产全局语义 Inv、初始化、API／ISR、Hook／栈、WFIFun、GOOD_OS／同程序K1–K4仍开放，uCOS3未开始，总目标active；六门94/1/1/1/1/0、旧423失败／1错误及审计身份问题保留。未提交／推送；下方历史原文不改写。
<!-- ready-switch-step-checkpoint-end -->

<!-- ready-call-return-checkpoint-start -->
## 进行中的检查点：真实调度调用、局部变量释放与目标交接

第137步把同一 ready Inv 接到原 OS_SchedNew 的 scall／分配／两赋值／返回／释放，局部地址由证明构造，不由调用者提供；原首次赋值直接写入分配所得 Vundef。返回调用者环境后执行原目标指针写入并建立 SWPRE。联合非空实例覆盖两种 current、调用者旧局部 canary 保留，以及同一完整调用返回后仅省略目标写入的拒绝。详见[第137步](audit/STAGE137_READY_CALL_RETURN.md)，实测以本步 checkpoint-report.json／verification.json 为准。

这是无交错存在性执行；frame 限 GoodInvAsrt，不包含实际 switch、完整 OS_Sched 或 WFIFun。目标不作为私有 frame 跨切换保存。生产全局语义 Inv、初始化、API／ISR、Hook／栈、GOOD_OS／同程序K1–K4仍开放，uCOS3未开始，总目标active。六门94/1/1/1/1/0、旧423失败／1错误及审计身份问题保留；未提交／推送。下方历史原文不改写。
<!-- ready-call-return-checkpoint-end -->

<!-- ready-target-handoff-checkpoint-start -->
## 进行中的检查点：就绪选择接到真实目标指针写入

第136步从同一 ready Inv 导出最高任务，在原两条选择赋值后执行原目标指针赋值，返回实际 typed store、SWPRE 及 current 成员／非成员分支。联合非空实例从指向 waiting 的旧目标出发；仅省略最后写入时，选择结果与 Inv 仍成立，但 SWPRE 被拒绝，正反内存在目标四字节外完全相同。详见[第136步](audit/STAGE136_READY_TARGET_HANDOFF.md)，最终实测以本步 checkpoint-report.json／verification.json 为准。

这是无交错三赋值片段，不含真实调用返回或 switch；目标不作为私有 frame 跨切换保存。生产全局语义 Inv、初始化、API／ISR、Hook／栈、WFIFun、GOOD_OS／同程序K1–K4仍开放；uCOS3未开始，总目标active。六门94/1/1/1/1/0、旧423失败／1错误及审计身份问题保留；未提交／推送。下方历史原文不改写。
<!-- ready-target-handoff-checkpoint-end -->

<!-- ready-task-invariant-checkpoint-start -->
## 进行中的检查点：同一任务表连接真实位图、优先级表与调度赋值

第135步增强有限运行期 Inv：同一 tasks 的真实 TCB 已选字段、三个就绪字节与13个优先级指针共同拥有，闭合 GoodI；从完整内存推出最高 ready 任务及实际表指针，并执行原 OS_SchedNew 两条赋值。独立非空 ready＋waiting 联合实例覆盖两种 current；分别仅破坏 low 位图字节、槽4指针的单因素对照证明旧记录 Inv 存活而新 Inv 拒绝。详见[第135步](audit/STAGE135_READY_TASK_INVARIANT.md)，最终实测以本步 checkpoint-report.json／verification.json 为准。

这不是生产全局语义 Inv、完整函数或初始化可达性证明。未使用槽及位13..15未约束；空 LocalInv 不含完整私有资源，实际变量绑定／只读 lookup 是执行接口义务。创建／阻塞／唤醒等 API、活动 ISR、Hook／栈与 WFIFun 仍待接通；GOOD_OS／同程序K1–K4未完成，uCOS3未开始，总目标active。六门94/1/1/1/1/0、旧423失败／1错误及审计身份问题保留，未提交／推送；下方历史原文不改写。
<!-- ready-task-invariant-checkpoint-end -->

<!-- task-record-invariant-checkpoint-start -->
## 进行中的检查点：同一抽象任务表拥有真实TCB记录

第134步闭合有限任务记录Inv的GoodI：四槽抽象所有权与同一tasks的实际已选TCB字段耦合，current真实store保留记录；非空ready＋waiting实例覆盖等待current成员及非成员两分支。只改实际优先级一字节4→5、任务表和其他字节不变时，旧共享Inv仍成立、新记录Inv拒绝。详见[第134步](audit/STAGE134_TASK_RECORD_INVARIANT.md)，最终实测以本步checkpoint-report.json／verification.json为准。

这不是最终生产全局语义Inv：ready bitmap／优先级表、完整池与链、初始化建立、API／ISR保持、真实Hook与栈初始化、WFIFun尚未连接。下一步让同一tasks的表与bitmap关系接入该可实例化接口并与已有真实字节入口会合；不把独立fixture当可达运行态。GOOD_OS／同程序K1–K4仍未完成；六门94/1/1/1/1/0不变，旧423失败／1错误及审计身份问题保留，uCOS3未开始，总目标active；未提交／推送。下方历史原文不改写。
<!-- task-record-invariant-checkpoint-end -->

<!-- boot-tcb-entry-checkpoint-start -->
## 进行中的检查点：真实初始化字节接到首个TCB调用

第133步从同一三次初始化返回内存，提取首TCB的18个精确待写字段，保留4个备用字段、其余12节点和优先级表；直接执行原七参数OS_TCBInit到首个真实Hook，无CurLINV或Hook返回前提。仅把同一内存的空闲链头实际store为NULL，原函数返回66且节点字节保留。详见[第133步](audit/STAGE133_BOOT_TCB_ENTRY.md)，最终实测以本步checkpoint-report.json／verification.json为准。

这不是完整OSTaskCreateExt、完整OSInit或已创建的idle任务；栈参数只是typed fixture，Hook206在探针中确实未实现，未用空函数补洞。存在性轨迹不等于所有运行轨迹定理。下一步连接真实Hook／栈初始化与创建者后缀。生产语义Inv／GoodI、initst／WFIFun、ISR、GOOD_OS／同程序K1–K4仍开放；六门94/1/1/1/1/0不变，旧423失败／1错误和审计证据身份问题保留。uCOS3未开始，总目标active；未提交／推送。下方历史原文不改写。
<!-- boot-tcb-entry-checkpoint-end -->

<!-- boot-running-boundary-checkpoint-start -->
## 进行中的检查点：启动初始化与运行期契约分开验证

第132步从原三次初始化的实际字节入口与同一返回内存，证明 OSTCBCur=NULL、OSRunning=0，排除任意 li 的 CurLINV 和全部构造器的 initst；真实框架标识符60已绑定到实际 current 字节，不靠缺失绑定制造反例。单次真实 current 写入的正／省略对照与四槽抽象所有权检查已通过 Coq，但首空闲TCB指针不是已创建任务，ghost placeholder 也不是生产语义Inv。详见[第132步](audit/STAGE132_BOOT_RUNNING_BOUNDARY.md)，完整实测以本步 checkpoint-report.json／verification.json 为准。

下一步复用已有无 CurLINV 的操作语义创建调用，从该可达内存建立启动任务、实例化 Hook，再连接真实 OSStart 与运行期 initst；不改 C 或框架门槛，不以补齐抽象槽冒充完整 GoodI。生产语义Inv、启动／运行衔接、Hook／WFIFun、ISR、GOOD_OS／同程序K1–K4仍开放；六门94/1/1/1/1/0不变。旧423失败／1错误与审计证据身份问题保留，uCOS3未开始，总目标active。未提交／推送；下方历史原文不改写。
<!-- boot-running-boundary-checkpoint-end -->

<!-- tcb-site-freshness-checkpoint-start -->
## 进行中的检查点：真实分配点新鲜性与 GoodI 不可实例化发现

第131步用真实allocator的NodeMember与固定13个记录起点的静态排除条件推出不别名，原字段／Hook／发布体、标准BuildPreI／BuildRetI与fpre／fpost不变；不再收通用状态Fresh。独立原token正例、仅换成首节点的单因素拒绝及同块偏移1接受均经Coq检查。详见[第131步](audit/STAGE131_TCB_SITE_FRESHNESS.md)，终态以本步checkpoint-report.json／verification.json实测为准。

更关键的是，本步机器证明具体SFPhysicalInv无法满足GoodI：原三次初始化建立的物理核心拥有空抽象状态，可再兼容非空curtid扩展，违反GoodI第一条件。因此第128～131步相关物理借还／条件完整体不能据此授予实际完整函数可调用信用；不能仅继续补Hook或堆条件定理。下一步先建立带抽象所有权和物理语义关系的可实例化Inv，证明GoodI；不削弱框架门槛。全部前提联合可满足未证明，生产全局Inv、Hook／WFIFun、完整创建者、活动ISR、GOOD_OS／同程序K1–K4仍未完成。六门94/1/1/1/1/0不变，旧423失败／1错误与审计旧证据身份问题保留。uCOS3未开始，总目标active；未提交／推送。下方历史原文不改写，旧“GoodI尚未证明”的具体实例限制以上述反例纠正。
<!-- tcb-site-freshness-checkpoint-end -->

<!-- tcb-shared-contract-checkpoint-start -->
## 进行中的检查点：共享池 TCB 标准契约与真实 err 接收调用

第130步把原 OS_TCBInit 七参数、两局部函数体接入 BuildPreI／BuildRetI，再以同一 fpre／fpost 推导创建者原七表达式和 err 接收变量的 call rule。局部 domain 留在内部 frame，返回66保留 owner＋R，返回0只交还R。独立构造器、分支及仅改变top类型的单因素检查通过。21个证明根、全296活动模块＋16探针的coqchk通过，新增8项回归通过；详见[第130步](audit/STAGE130_TCB_SHARED_CONTRACT.md)及本步checkpoint-report.json。

这是有条件的函数体和调用规则推导，不是完整program执行。GoodI、Fresh、两Hook实现／WFIFun及全部前提联合可满足性仍开放；尤其Fresh尚未利用真实表成员信息，可能比实际路径要求更强，未证明具体探针满足它。下一步先保留真实分配点的NodeMember来推导标记不别名，再做联合实例。生产语义Inv、活动ISR、完整创建者成功、GOOD_OS／同程序K1–K4仍未完成；六门94/1/1/1/1/0不变，旧423失败／1错误与make audit证据身份过期失败均保留。uCOS3未开始，总目标active。未提交／推送，下方历史原文不变。
<!-- tcb-shared-contract-checkpoint-end -->

<!-- tcb-hook-frame-checkpoint-start -->
## 进行中的检查点：纠正 TCB Hook 不可实例化的前提

第129步确认第122～128步相关完整TCB条件接口的 GoodFunAsrt 前提无法实例化：publication_globals 含调用者局部环境约束。旧条件推导仍有效，但不能授予实际可调用整函数信用。现将这些约束保留在调用者 frame，首Hook只传 owner＋R，次Hook只传R；从原allocator开始重新连接原完整 OS_TCBInit 体，并从同一 joint Inv 推导六项借还。具体非空R的good构造、两个typed Hook调用及同内存局部遮蔽单因素对照通过。22个根、全295活动模块＋15探针的coqchk通过；新增8项回归通过。详见[第129步](audit/STAGE129_TCB_HOOK_FRAME.md)，终态以本步checkpoint-report.json为准。

这只修正了明确不可能的子前提，未证明全部完整体假设联合可满足；标准非空 BuildPreI／BuildRetI、真正创建者接收变量调用、Hook实现／WFIFun、token freshness、生产全局语义Inv、活动ISR及GOOD_OS／同程序K1–K4仍开放。六门94/1/1/1/1/0不变，全量1725项中的旧423失败／1错误及覆盖审计证据身份问题保留；uCOS3未开始，总目标active。未提交／推送，下方历史原文不变，涉及旧Hook接口的历史结论以上述纠正为准。
<!-- tcb-hook-frame-checkpoint-end -->

<!-- create-joint-shared-checkpoint-start -->
## 进行中的检查点：同一共享状态连接任务创建预留、回滚与完整TCB初始化体

第128步从真实OS_InitMisc→OS_InitRdyList→OS_InitTCBList三次调用的同一份返回内存，建立包含独立OSIntNesting零字节的联合物理核心。一个固定Inv同时支持原创建者的encrit、RESERVED预留、失败回滚、栈初始化调用片段，以及原完整OS_TCBInit函数体的六项借还。独立实际字节入口和仅省略一次NULL写入的单因素对照已检查。29个新证明根、全294活动模块＋14探针的coqchk及新增8项回归通过。详见[第128步](audit/STAGE128_CREATE_JOINT_SHARED.md)，终态以本步checkpoint-report.json为准。

这不是生产全局Inv或完整任务创建成功契约；非空TCB调用的标准fpre／fpost与call_rule尚未接通，独立初始化与完整创建者也尚未在同一完整program中连续组合。活动ISR、精确资源分区／删除保持、任务映射与ready语义、Hook／WFIFun、token freshness及GOOD_OS／同程序K1–K4仍开放。六门94/1/1/1/1/0不变，全量1717项中的旧423失败／1错误及覆盖审计身份问题保留，uCOS3未开始，总目标active。未提交／推送，下方历史原文不变。
<!-- create-joint-shared-checkpoint-end -->

<!-- tcb-joint-shared-checkpoint-start -->
## 进行中的检查点：同一共享状态连接真实初始化与完整TCB初始化体

第127步从真实OS_InitMisc→OS_InitRdyList→OS_InitTCBList三次调用的同一份返回内存建立联合物理资源核心，并以一个固定Inv推导空闲池、任意合法优先级槽和有限活动发布链的六项借还，接回原完整OS_TCBInit函数体。独立实际字节入口及仅改变RESERVED槽权限的单因素对照已检查。47个证明根、全293活动模块＋13探针的coqchk和新增8项回归通过。详见[第127步](audit/STAGE127_TCB_JOINT_SHARED.md)，终态以本步checkpoint-report.json为准。

这不是生产全局Inv或完整OSInit交错证明；入口限制无活动ISR，完整TCB初始化仍带Hook、token freshness等明确前提。精确资源分区／删除保持、任务映射与ready语义、Hook／WFIFun及GOOD_OS／同程序K1–K4仍开放。六门94/1/1/1/1/0不变，全量1709项中的旧423失败／1错误及覆盖审计身份问题保留，uCOS3未开始，总目标active。未提交／推送，下方历史原文不变。
<!-- tcb-joint-shared-checkpoint-end -->

<!-- init-tcb-finite-pool-checkpoint-start -->
## 进行中的检查点：真实初始化返回建立增强空闲池

第126步从原OS_InitTCBList调用的同一份返回内存建立固定13槽增强空闲池：20＋32字节原payload、实际Next、表成员性均保留；空活动头、13个null优先级槽和caller frame继续分离拥有。独立实际字节入口、13节点load遍历及只把首Next真实store为null的单因素对照均通过。20个证明根和全292活动模块＋11探针的coqchk通过，新增8项回归通过。详见[第126步](audit/STAGE126_INIT_TCB_FINITE_POOL.md)，终态以本步checkpoint-report.json为准。

这只是原初始化调用的局部结果，不是生产全局Inv或完整OSInit交错证明。三池联合开合、运行中资源分区／删除保持、token freshness、Hook／WFIFun及GOOD_OS／同程序K1–K4仍开放。fuel是递归上界，不将截断后池必假作为结论。六门94/1/1/1/1/0不变，旧423失败／1错误未修复，uCOS3未开始，总目标active。未提交／推送，下方历史原文不变。
<!-- init-tcb-finite-pool-checkpoint-end -->

<!-- tcb-finite-allocator-checkpoint-start -->
## 进行中的检查点：真实空闲链提供固定表成员性

第125步让当前真实空闲链在弹出节点时提供固定TCB表成员性，并将其贯穿原18字段、两个Hook、优先级槽与有限发布，接回完整OS_TCBInit函数体；新接口不再要求原来的forall post-Hook Member前提。41个证明根及全291活动模块＋10探针的coqchk通过，新增8项回归通过。详见[第125步](audit/STAGE125_TCB_FINITE_ALLOCATOR.md)，终态以本步checkpoint-report.json为准。

这不是生产全局Inv或初始化可达性证明；所有共享池借还的联合实例、初始化建立增强空闲池、分配／删除保持性、token freshness、Hook／WFIFun及GOOD_OS／K1–K4仍开放。六门94/1/1/1/1/0不变，uCOS3未开始，总目标active。旧证据与失败不改写，未提交／推送，下方历史原文不变。
<!-- tcb-finite-allocator-checkpoint-end -->

<!-- tcb-finite-enabled-checkpoint-start -->
## 进行中的检查点：有限链接开启中断的发布后缀

第124步已检查同Inv借出当前有限地址索引链、执行原发布体、归还并返回0的完整后缀，并接回条件式完整OS_TCBInit函数体；新接口不再接收独立Capacity。22个证明根及全290活动模块＋9探针的coqchk通过，新增8项回归通过。分配后表成员性等生产义务仍保留。详见[第124步](audit/STAGE124_TCB_FINITE_ENABLED.md)，终态以本步checkpoint-report.json为准。

这不是生产全局Inv或初始化可达性证明；Hook／WFIFun、分配／删除保持性、token freshness、GOOD_OS／K1–K4仍开放。旧第122步不改写，六门94/1/1/1/1/0不变，uCOS3未开始，总目标active。未提交／推送，下方历史原文不变。
<!-- tcb-finite-enabled-checkpoint-end -->

<!-- tcb-finite-sites-checkpoint-start -->
## 进行中的检查点：真实发布链的有限地址约束

第123步给同一份完整56字节TCB链增加实际地址索引：从固定13槽表的包含关系与不重复性推出当前计数上界，原发布体插入新节点后保持约束；物理地址新鲜性来自实际Next完整写权限冲突。详见[第123步](audit/STAGE123_TCB_FINITE_SITES.md)，终态以本步checkpoint-report.json为准。

本步入口仍已关闭中断，新refinement不是生产Inv；第122步完整函数定理的Capacity尚未消去。初始化／分配与删除保持性、生产同Inv借还、allocator-token freshness、Hook／WFIFun／GOOD_OS／K1–K4仍开放。六门94/1/1/1/1/0不变，uCOS3未开始，总目标active。未提交／推送，下方历史原文不变。
<!-- tcb-finite-sites-checkpoint-end -->

<!-- tcb-enabled-publication-checkpoint-start -->
## 进行中的检查点：开启中断发布接原完整函数体

第122步在同一个Inv接口下连接encrit1／完整字节发布／excrit1／return0，并接回原OS_TCBInit完整函数体，消除最后的后缀Hoare continuation。七参数／两局部和调用者资源保留，发布节点归还共享池。详见[第122步](audit/STAGE122_TCB_ENABLED_PUBLICATION.md)。

这是显式带Capacity、生产借还、freshness和Hook契约的条件定理；物理池允许count255，四个字面入口不能代替所有交错状态的容量证明。同一物理Inv的实际enter与已关闭中断body／exit／return分别检查，未得到无条件enabled成功。生产Inv／WFIFun／初始化、标准整函数契约及GOOD_OS／K1–K4仍开放；六门94/1/1/1/1/0不变，uCOS3未开始，总目标active。旧失败保留，终态以checkpoint-report.json为准；未提交／推送，下方历史原文不变。
<!-- tcb-enabled-publication-checkpoint-end -->

<!-- tcb-publication-pool-checkpoint-start -->
## 进行中的检查点：发布体接完整字节与计数双向链

第121步把实际发布体接到完整56字节节点及精确计数的双向物理链：空／非空旧头、两行ready、计数递增和旧尾链保留；真实初始化节点可提供同一组字节。四种具体入口及省略旧头Prev实际store的单因素链关系对照独立检查。详见[第121步](audit/STAGE121_TCB_PUBLICATION_POOL.md)。

本步入口仍已关闭中断；尚未连接共享池encrit1／excrit1、完整函数体和return0。物理链不等于任务映射／ready语义Inv，初始化视图忘却部分字段精确值。生产Inv／WFIFun／初始化、Freshness、Hook函数体及GOOD_OS／K1–K4开放；六门94/1/1/1/1/0不变，uCOS3未开始，总目标active。旧失败保留，终态以checkpoint-report.json为准；未提交／推送，下方历史原文不变。
<!-- tcb-publication-pool-checkpoint-end -->

<!-- tcb-second-hook-checkpoint-start -->
## 进行中的检查点：完整函数体接真实第二个 Hook

第120步把原第二个CPU Hook接回完整OS_TCBInit函数体，实际读取ptcb，保留七参数／两局部和初始化节点；优先级槽归还共享池后，不再要求把已消费的owner半权限交给第二个Hook。同一个有限Spec容纳两种资源契约。详见[第120步](audit/STAGE120_TCB_SECOND_HOOK.md)。

完整函数体唯一剩余Hoare continuation已缩小到原发布／就绪位／计数与return0路径；但Freshness仍是显式前提。本步机器检查了满足完整物理资源却token与节点别名的反例，不能从地址分离直接消去这一生产义务。Hook函数体、生产Inv／WFIFun／初始化、标准整函数契约及GOOD_OS／K1–K4开放；六门94/1/1/1/1/0不变，uCOS3未开始，总目标active。旧失败保留，终态以checkpoint-report.json为准；未提交／推送，下方历史原文不变。
<!-- tcb-second-hook-checkpoint-end -->

<!-- tcb-full-priority-checkpoint-start -->
## 进行中的检查点：完整函数体接真实优先级槽写入

第119步用可还原的资源视图，把第118步首Hook／真实优先级槽写入接回原完整OS_TCBInit函数体；七参数、两局部、初始化节点和调用者资源不丢失。带owner半权限的非空字节实例与仅改变local92遮蔽的地址对照已检查。详见[第119步](audit/STAGE119_TCB_FULL_PRIORITY.md)。

完整函数体定理的唯一剩余Hoare continuation从第二个Hook／发布开始；但生产freshness、同Inv开合和Hook契约仍为显式前提，不是无条件成功返回0。标准整函数契约、Hook函数体、生产Inv／WFIFun／初始化及GOOD_OS／K1–K4开放；六门94/1/1/1/1/0不变，uCOS3未开始，总目标active。旧失败保留，终态以本步checkpoint-report.json为准。未提交／推送，下方历史原文不变。
<!-- tcb-full-priority-checkpoint-end -->

<!-- tcb-owned-priority-checkpoint-start -->
## 进行中的检查点：预留半权限接真实优先级槽写入

第118步连接首个真实Hook调用及其后的原encrit／优先级槽写入／excrit：创建者与共享池的半权限重拼完整写权限，真实prio／ptcb单元决定地址和值，归还同一个Inv。字面非空片段和省略一次物理写入的单因素对照独立检查。详见[第118步](audit/STAGE118_TCB_OWNED_PRIORITY.md)。

成功后缀接口的剩余Hoare前提从第二个Hook／发布开始；但与第117步完整函数体的参数视图及生产freshness尚未整合，不能冒充整函数成功。Hook函数体／WFIFun、生产Inv／初始化及GOOD_OS／K1–K4开放，六门94/1/1/1/1/0不变，uCOS3未开始，总目标active。旧失败保留；终态以本步checkpoint-report.json为准。未提交／推送，下方历史原文不变。
<!-- tcb-owned-priority-checkpoint-end -->

<!-- tcb-enabled-hook-checkpoint-start -->
## 进行中的检查点：开启中断的私有TCB接真实首个Hook调用

第117步在IE=true、共享head已归还的真实路径上，用call_rule连接原首个Hook调用；私有完整节点与调用者局部frame分离，一个有限Spec通过逻辑参数支持不同取出节点。真实字节输入与同Inv共享尾链共存，指针／任务／结果的三个单因素契约判别已检查。详见[第117步](audit/STAGE117_TCB_ENABLED_HOOK.md)。

原完整函数体的剩余Hoare前提已推进到首个Hook之后；Hook函数体／WFIFun、优先级槽与发布／返回0、生产Inv／初始化及GOOD_OS／K1–K4仍开放。六门94/1/1/1/1/0不变，uCOS3未开始，总目标active。旧失败保留，终态以本步checkpoint-report.json为准；未提交／推送，下方历史原文不变。
<!-- tcb-enabled-hook-checkpoint-end -->

<!-- tcb-allocated-fields-checkpoint-start -->
## 进行中的检查点：真实私有 TCB 接原18个字段写入

第116步从实际取出节点的 payload 导出旧值，闭合同Inv的原右结合 pop／excrit1／18字段写入；Next、Prev、flags-ready、填充及调用者 frame 保留，字段段不再私有持有共享head。真实字面入口与单次priority物理写入／省略写入对照独立检查。详见[第116步](audit/STAGE116_TCB_ALLOCATED_FIELDS.md)。

原完整函数体接口的剩余证明前提已推进到字段之后的Hook／成功后缀，但这仍不是非空成功返回0或标准整函数契约。生产Inv／WFIFun／初始化及GOOD_OS／K1–K4开放，六门94/1/1/1/1/0不变，uCOS3未开始，总目标active。旧失败保留，最终实测以本步checkpoint-report.json为准；未提交／推送，下方历史原文不变。
<!-- tcb-allocated-fields-checkpoint-end -->

<!-- tcb-free-pool-checkpoint-start -->
## 进行中的检查点：真实 TCB 空闲链表弹出与私有节点移交

第115步从同一共享 Inv 动态借出有限类型化链表，在原 AST 上连接读头、空／非空判断、实际 head=ptcb->Next 和 excrit1；归还变化后的尾链，取出节点的完整56字节转为私有。空池、双节点和单节点尾链的字面实例及省略头写入的单因素对照已检查。详见[第115步](audit/STAGE115_TCB_FREE_POOL.md)。

闭合的是弹出／归还片段；原完整函数体的组合接口仍显式要求字段初始化与成功后缀证明，不是非空成功返回0或标准整函数契约。生产Inv／WFIFun／初始化及GOOD_OS／K1–K4开放；六门94/1/1/1/1/0不变，uCOS3未开始，总目标active。旧失败保留，最终实测以本步checkpoint-report.json为准。未提交／推送，下方历史原文不变。
<!-- tcb-free-pool-checkpoint-end -->

<!-- enabled-owned-taskcreate-checkpoint-start -->
## 进行中的检查点：开启中断的真实任务创建入口接入预留所有权池

第114步在原完整 AST 上连接 CPU 初始化、优先级42、encrit1 后动态 NULL／非NULL 槽读取、占用40及空池预留回滚66；标准九参数／三局部 BuildPreI／BuildRetI 契约和同Inv／同有限Spec的完整TCB已检查。IE=true字面入口不持共享head／counter／slot字节，半权限RESERVED可读取。详见[第114步](audit/STAGE114_TASKCREATE_ENABLED_OWNED.md)。

这是counter0、TCB空池的受限整函数契约，公开后置为返回集合，不是所有运行情形；正ISR60、非空分配成功0、Hook函数体、生产Inv／WFIFun／初始化及GOOD_OS／K1–K4仍开放。六门94/1/1/1/1/0不变，uCOS3未开始，总目标active。全量测试仍有旧失败；终态以本步checkpoint-report.json为准。未提交／推送，下方历史原文不变。
<!-- enabled-owned-taskcreate-checkpoint-end -->

<!-- taskcreate-owned-null-branch-checkpoint-start -->
## 进行中的检查点：带预留所有权的 NULL 槽空池失败路径已连续接到返回66

第113步在原右结合 AST 上连接真实 RESERVED 写入、退出临界区、栈 Hook、七实参 TCB 调用、借池合并半权限、NULL 回滚及返回66；原中断／NULL判断和占用尾部保留。同一个字面 Inv／有限 Spec 检查连续tail和完整空头TCB，12个局部及槽／counter／head的实际字节给出非空入口实例。详见[第113步](audit/STAGE113_TASKCREATE_OWNED_NULL_BRANCH.md)。

仍从临界区内合法NULL入口开始，不是IE=true整函数契约；Hook函数体、生产全局Inv、非空分配、WFIFun、初始化及GOOD_OS／K1–K4开放。六门94/1/1/1/1/0不变，uCOS3未开始，总目标active。旧失败和冻结证据保留，终态以本步checkpoint-report.json为准；未提交／推送。下方历史原文不变。
<!-- taskcreate-owned-null-branch-checkpoint-end -->

<!-- reservation-ownership-checkpoint-start -->
## 进行中的检查点：预留半权限保护任务创建失败回滚

第112步复用既有 HalfPermMap：真实 RESERVED 写入后，创建者与共享池各持一半；半权限穿过原栈 Hook／TCB 调用的 caller frame，失败回滚再借池并重拼完整写权限，不能误清不同任务指针。值决定权限的池已证明 precise／GoodInvAsrt／ISR 稳定性。同一字面 Inv 检查调用者与共享池实际共存、真实调用后缀及完整空头 TCB callee；移除 owner 有兼容反例。详见[第112步](audit/STAGE112_RESERVATION_OWNERSHIP.md)。

仍非完整 NULL 分支／整函数；生产全局 Inv、非空分配、WFIFun、初始化及 GOOD_OS／K1–K4 未完成。六门94/1/1/1/1/0不变，uCOS3未开始，总目标active。旧失败和冻结证据保留，终态以本步 checkpoint-report.json 为准；未提交／推送。下方历史原文不变。
<!-- reservation-ownership-checkpoint-end -->

<!-- taskcreate-enabled-rollback-checkpoint-start -->
## 进行中的检查点：开启中断的真实TCB调用接回失败回滚

第111步接通实际七实参 `OS_TCBInit` 调用、err赋值与原完整失败后缀：重新进入临界区借出当前槽位，真实NULL写入，归还同一池后返回66。独立探针用同一有限Spec和Inv检查调用片段及完整TCB函数体。详见[第111步](audit/STAGE111_TASKCREATE_ENABLED_ROLLBACK.md)。

槽位不是跨中断保持不变的RESERVED快照；当前存在物理池尚未证明预留所有权，不能排除误清已建任务，故不授予生产safety或整函数覆盖信用。完整前缀／Hook交接、生产不变量、WFIFun、初始化及GOOD_OS／K1–K4仍开放。六门94/1/1/1/1/0不变，uCOS3未开始，总目标active。旧失败和冻结证据保留；最终实测以本步checkpoint-report.json为准；未提交／推送。下方历史原文不变。
<!-- taskcreate-enabled-rollback-checkpoint-end -->

<!-- tcb-empty-enabled-checkpoint-start -->
## 进行中的检查点：中断开启时从共享空池借还TCB头并返回66

第110步为原完整 `OS_TCBInit` 增加IE=true标准契约：真实encrit1借出NULL头的只读字节，实际load和guard决定空池路径，excrit1归还同一个不变量并恢复入口临界栈，原始return66及七参数／两局部的标准builder完整连接。详见[第110步](audit/STAGE110_TCB_EMPTY_ENABLED.md)。

独立字面实例证明调用者没有头字节；NULL-only池不是通用allocator，生产Open／Close仍开放。返回码对照与物理头字节消融的结论分别限定为规格身份、类型化load，不能代替整段执行。未完成任务创建全路径连接、全局不变量、WFIFun、初始化和GOOD_OS／K1–K4；六门94/1/1/1/1/0不变，uCOS3未开始，总目标active。旧失败保留，验收以本步checkpoint-report.json为准；未提交／推送。下方历史原文不变。
<!-- tcb-empty-enabled-checkpoint-end -->

<!-- taskcreate-enabled-slot-pool-checkpoint-start -->
## 进行中的检查点：NULL 槽预留后归还同一个共享池，再调用栈 Hook

第109步增加 nullable 物理资源池：真实 encrit1 打开见证，NULL 分支中的实际预留赋值、excrit1 归还与栈 Hook 调用片段已接通。不是完整函数契约；不删原占用分支，不用外部 Hook 改变 IE 来套用旧 TCB 前置。详见[第109步](audit/STAGE109_TASKCREATE_ENABLED_SLOT_POOL.md)。

完整前缀动态分支到后续 TCB／返回的连接仍在进行；全局不变量、WFIFun、初始化和 GOOD_OS／K1–K4仍开放。六门94/1/1/1/1/0不变，uCOS3未开始，总目标active。历史失败及第108步冻结证据保留，未提交／推送。下方历史原文不变。
<!-- taskcreate-enabled-slot-pool-checkpoint-end -->

<!-- taskcreate-dynamic-reject-checkpoint-start -->
## 最新检查点：临界区内打开同一个存在资源池并决定任务创建拒绝路径

第108步不再在入口固定拒绝类别／计数／指针：真实encrit1取得同一个存在物理池后，拥有的实际计数字节决定60或40；两条路径都归还资源并恢复IE=true及原临界栈。原完整AST、BuildPreI／BuildRetI、九参数／三局部和精确声明域不变。详见[第108步](audit/STAGE108_TASKCREATE_DYNAMIC_REJECT.md)。

同一个探针不变量和调用者支持计数0／1；单因素对照只检查类型化物理guard，不是整段执行。资源池仍限合法优先级及非NULL槽，不能冒充生产全局不变量；分配、Hook函数体、WFIFun和初始化仍开放。六门94/1/1/1/1/0不变，GOOD_OS及同程序K1–K4未完成，uCOS3未开始，总目标active。旧失败保留；验收以本步final-report.json为准；未提交／推送。下方历史原文保留。
<!-- taskcreate-dynamic-reject-checkpoint-end -->

<!-- taskcreate-enabled-reject-checkpoint-start -->
## 最新检查点：开启中断的任务创建提前返回借还真实共享资源

第107步为原完整 `OSTaskCreateExt` 的42／60／40三类提前返回接通IE=true标准契约：真实encrit1借出ISR不变量，拥有的真实字节决定guard，excrit1归还资源并恢复入口中断状态；九参数／三局部和精确声明域完整交接。详见[第107步](audit/STAGE107_TASKCREATE_ENABLED_REJECT.md)。

资源双向转换仍是生产全局不变量的开放义务；探针仅给出分类局部物理实例，ISR例不授予全局一致／可达信用。保存位对照只测临界退出原语，不是整段执行。开启中断的分配、Hook函数体、WFIFun、全局不变量及初始化仍开放。六门94/1/1/1/1/0不变，GOOD_OS与同程序K1–K4未完成，uCOS3未开始，总目标active。旧失败保留；验收以本步final-report.json为准；未提交／推送。下方历史原文保留。
<!-- taskcreate-enabled-reject-checkpoint-end -->

<!-- taskcreate-unified-internal-checkpoint-start -->
## 最新检查点：任务创建五类返回路径共用一个标准函数契约

第106步把42／60／40／66／0五类受限返回接入同一有限规格：栈Hook通过精确逻辑资源实例表达两个分配分支，TCB共用原snapshot契约；真实函数体、BuildPreI／BuildRetI及全部声明资源不变。详见[第106步](audit/STAGE106_TASKCREATE_UNIFIED_INTERNAL.md)。

两种分配分支的字面入口、链表头load及同规格完整TCB函数体均检查；对照只测量逻辑实例标签对应的断言身份，不声称整段执行。仍限入口IE=false、成功OSRunning=0；活动调度、WFIFun、全局不变量与初始化开放。六门94/1/1/1/1/0不变，GOOD_OS及同程序K1–K4未完成，uCOS3未开始，总目标active。旧失败保留；验收以本步final-report.json为准；未提交／推送。下方历史原文保留。
<!-- taskcreate-unified-internal-checkpoint-end -->

<!-- taskcreate-reject-internal-checkpoint-start -->
## 最新检查点：任务创建三类提前拒绝接通真实函数契约

第105步在原始完整 `OSTaskCreateExt` 上接通非法优先级42、ISR中创建60、优先级占用40三类提前返回，使用真实 `BuildPreI / BuildRetI`，交回九参数／三局部及精确声明域。guard由拥有的真实字节决定；未到达的Hook不增加规格查找前提。详见[第105步](audit/STAGE105_TASKCREATE_REJECT_INTERNAL.md)。

三类独立字面入口、标准builder和空规格下的公共契约均检查；对照只改变最后的期望返回码，测量类型化guard／返回表达式而非整段执行。仍限入口IE=false；活动调度、全路径统一规格／WFIFun、全局不变量和初始化开放。六门94/1/1/1/1/0不变，GOOD_OS与同程序K1–K4未完成，uCOS3未开始，总目标active。旧失败保留；验收状态以本步final-report.json为准；未提交／推送。下方历史原文保留。
<!-- taskcreate-reject-internal-checkpoint-end -->

<!-- taskcreate-success-internal-checkpoint-start -->
## 最新检查点：任务创建受限成功路径接通真实函数契约

第104步将第103步原始完整 `OSTaskCreateExt` 的受限成功路径接入真实 `BuildPreI / BuildRetI`：九个参数、三个局部变量和精确声明域完整交接；保留完整 snapshot callee 后置与调用者资源。详见[第104步](audit/STAGE104_TASKCREATE_SUCCESS_INTERNAL.md)。

独立探针检查真实字面入口、实际 builder 及同一有限规格下的 TCB 函数体。单因素对照只检查规范返回局部布局，不表示交换后的分离断言语义无效。仍限入口 IE=false、合法任务上下文／空槽／非空空闲TCB链表、OSRunning=0；三个外部 Hook、其余分支、活动调度、WFIFun、全局不变量和初始化开放。六门94/1/1/1/1/0不变；GOOD_OS与同程序K1–K4未完成，uCOS3未开始，总目标active；未提交／推送。旧失败保留，验收状态以本步 final-report.json 为准。下方历史原文保留。
<!-- taskcreate-success-internal-checkpoint-end -->

<!-- taskcreate-success-body-checkpoint-start -->
## 最新检查点：原完整任务创建函数体接通受限成功路径

第103步连接入口检查／预留、实际栈调用、同一完整snapshot TCB成功调用和原始返回0后缀。优先级槽只由入口持有，真实写入预留指针后再交给TCB前置；全部callee资源、调用者参数、prefix字节和frame保留。详见[第103步](audit/STAGE103_TASKCREATE_SUCCESS_BODY.md)。

独立字面入口、实际前缀执行及资源交接均检查；单因素对照只改期望槽值，两组先完成相同前缀和类型检查，错误NULL仅在最终load等式拒绝。不是整段调用执行轨迹。仍限IE=false、合法任务上下文／空槽／非空TCB链表、OSRunning=0；三个外部Hook、成功标准builder、活动调度、WFIFun和全局不变量开放。六门94/1/1/1/1/0不变，GOOD_OS与同程序K1–K4未完成，uCOS3未开始，总目标active；未提交／推送。旧失败完整保留，最终数据以本步final-report.json为准。下方历史原文保留。
<!-- taskcreate-success-body-checkpoint-end -->

<!-- taskcreate-stack-success-checkpoint-start -->
## 最新检查点：真实栈调用接通TCB成功调用与返回后缀

第102步将实际四实参栈调用及psp返回接入同一完整snapshot TCB成功调用，继而沿原始后缀在OSRunning=0时返回0；完整保留callee资源、全部调用者参数和frame。详见[第102步](audit/STAGE102_TASKCREATE_STACK_SUCCESS.md)。

栈和两个CPU Hook仍属外部契约；独立NULL返回仅是类型／连接见证，不是有效栈算法。成功侧完整入口、标准builder、活动调度、WFIFun与全局不变量仍开放。规格键单因素控制仅检验规格选择。六门94/1/1/1/1/0不变，GOOD_OS与同程序K1–K4未完成，uCOS3未开始，总目标active；未提交／推送。冻结结果以本步final-report.json为准。下方历史原文保留。
<!-- taskcreate-stack-success-checkpoint-end -->

<!-- taskcreate-success-hoare-checkpoint-start -->
## 最新检查点：创建任务成功调用接通原始返回后缀

第101步连接实际七实参TCB成功调用与原始创建后缀：真实err与只读OSRunning=0字节决定分支，返回0并保留完整callee后置、七实参及调用者frame。复用同一完整snapshot规格，不新增执行oracle。详见[第101步](audit/STAGE101_TASKCREATE_SUCCESS_HOARE.md)。

仅覆盖不运行调度器的call+suffix；成功侧完整入口／栈连接、标准builder、活动调度与WFIFun仍开放。单因素控制仅检验返回表达式求值，不代表整段执行。六门94/1/1/1/1/0不变，GOOD_OS与同程序K1–K4未完成，uCOS3未开始，目标active；未提交／推送。冻结结果以本步final-report.json为准。下方历史原文保留。
<!-- taskcreate-success-hoare-checkpoint-end -->

<!-- taskcreate-empty-internal-checkpoint-start -->
## 最新检查点：任务创建受限失败路径接通标准函数契约

第100步将原完整函数体的失败路径接入真实 BuildPreI／BuildRetI：九个参数和三个局部按实际声明顺序完整交接，精确声明域推导全局名不被遮蔽，返回时12个变量资源及声明域完整交回。详见[第100步](audit/STAGE100_TASKCREATE_EMPTY_INTERNAL.md)。

两个同类型指针实参交换控制均完成类型匹配和buildp，只在最终规范布局等式拒绝错误向量；仅验证builder映射，不是执行消融。仍是关闭中断、合法task上下文／空槽／空闲TCB链表NULL的受限契约；三个外部Hook、成功调度、WFIFun与全局不变量开放。六门94/1/1/1/1/0不变，GOOD_OS与同程序K1–K4未完成，uCOS3未开始，目标active；未提交／推送。冻结结果以本步final-report.json为准。下方历史原文保留。
<!-- taskcreate-empty-internal-checkpoint-end -->

<!-- taskcreate-body-failure-checkpoint-start -->
## 最新检查点：完整任务创建函数体接通受限失败路径

第99步将真实入口的CPU局部初始化、优先级／中断嵌套／空槽检查及预留写入，接到栈调用、同一完整snapshot TCB调用和清槽返回66。全部原始分支语法保留；真实字节决定guard，不新增执行oracle。详见[第99步](audit/STAGE99_TASKCREATE_BODY_FAILURE.md)。

仅覆盖合法优先级、任务上下文、空优先级槽／空闲TCB链表、入口中断已关闭的路径。栈Hook和两个TCB CPU Hook仍是外部规格；成功调度、WFIFun和全局不变量开放。预留符号控制在回滚前比较，不能由最终NULL槽区分。检查是否冻结以本步final-report.json为准。六门94/1/1/1/1/0不变，GOOD_OS与同程序K1–K4未完成，uCOS3未开始，目标active；未提交／推送。下方历史原文保留。
<!-- taskcreate-body-failure-checkpoint-end -->

<!-- taskcreate-stack-call-checkpoint-start -->
## 最新检查点：栈初始化调用接通任务创建失败链

第98步从真实局部内存读取栈函数四实参，将返回值写入 `psp`，再接同一完整 snapshot TCB 规格及失败清槽／返回66路径。返回后赋值的单因素控制只替换同类型接收变量：两条赋值均执行完成，错误变量在最终 `psp` 读回处被拒绝。详见[第98步](audit/STAGE98_TASKCREATE_STACK_CALL.md)。

栈初始化及两个TCB CPU Hook仍属外部契约；NULL返回探针只检查调用连接，不证明栈算法。完整入口前缀、成功路径、WFIFun及全局不变量仍开放。六门94/1/1/1/1/0不变，GOOD_OS与同程序K1–K4未完成，uCOS3未开始，目标active；未提交／推送。下方历史原文保留。
<!-- taskcreate-stack-call-checkpoint-end -->

<!-- taskcreate-failure-hoare-checkpoint-start -->
## 最新检查点：任务创建失败调用接通清槽与返回66

第97步连接七实参实际 TCB 调用与原始失败后缀：从 err 局部字节选择失败路径，在临界区清除实际持有的预留优先级槽，恢复原 cs 并返回66。失败预留值与完整规格成功侧旧值分开量化，保留原同一 snapshot 规格及全部 caller frame。详见[第97步](audit/STAGE97_TASKCREATE_FAILURE_HOARE.md)。

中断已关闭的局部接口不等于整函数 WFIFun；成功调度／全局不变量和两个外部 Hook 仍开放。六门94/1/1/1/1/0不变，GOOD_OS与同程序K1–K4未完成，uCOS3未开始，目标active，未提交／推送。下方历史原文保留。
<!-- taskcreate-failure-hoare-checkpoint-end -->

<!-- taskcreate-tcb-call-checkpoint-start -->
## 最新检查点：任务创建的七实参带返回值 TCB 调用

第96步从调用者真实局部内存读取七个实参，应用 `calle_rule_lvar` 把 TCB 初始化结果接入 `err : Tint8`，保留七参数及额外调用者 frame，并保留入口 head 到返回66／0的关联。被调用者契约与调用现场在同一有限规格表下检查。详见[第96步](audit/STAGE96_TASKCREATE_TCB_CALL.md)及本步最终报告。

两个 CPU Hook 仍是外部规格；任务创建前后的栈初始化／分支、完整 WFIFun 和全局不变量尚未闭合。六门94/1/1/1/1/0不变，GOOD_OS与同程序K1–K4未完成，uCOS3未开始，目标active，未提交／推送。下方历史原文保留。
<!-- taskcreate-tcb-call-checkpoint-end -->

<!-- tcb-snapshot-internal-checkpoint-start -->
## 最新检查点：OS_TCBInit 保存真实入口 head 的标准函数契约

第95步使用框架逻辑参数保存实际入口 head，指针相等 guard 与物理字节 load 相连；NULL快照对应返回66，合法指针快照对应返回0。真实 builder 的全部参数／局部返回资源及声明域保留。详见[第95步](audit/STAGE95_TCB_ENTRY_SNAPSHOT.md)。

两项真实CPU Hook规格、共同成功侧前提、全局Inv与WFIFun仍开放；尚未接入任务创建的实际调用。六门94/1/1/1/1/0不变，GOOD_OS与同程序K1–K4未完成，uCOS3未开始；目标active，未提交／推送。下方历史原文保留。
<!-- tcb-snapshot-internal-checkpoint-end -->

<!-- tcb-unified-internal-checkpoint-start -->
## 最新检查点：OS_TCBInit 两分支统一标准构造器契约

第94步把空／非空两支接入同一个 BuildPreI／BuildRetI 接口，逐点析取外部规格，保留全部参数／局部资源与精确声明域，直接使用既有两支定理。详见[第94步](audit/STAGE94_TCB_UNIFIED_INTERNAL.md)。

统一后置是两类结果／资源的析取，不自动保留入口分支到返回码的相关性；原有精确分支契约仍保留。两项CPU Hook规格、共同规格的成功侧前提、全局Inv与WFIFun仍开放。六门94/1/1/1/1/0不变，GOOD_OS与同程序K1–K4未完成，uCOS3未开始；目标active，未提交／推送。下方历史原文保留。
<!-- tcb-unified-internal-checkpoint-end -->

<!-- tcb-success-internal-checkpoint-start -->
## 最新检查点：OS_TCBInit 成功分支连接标准函数构造器

第93步继续将真实非空成功路径接到 BuildPreI／BuildRetI，七个实参按框架逆序／C顺序边界检查，九个参数及局部资源完整交回；六个全局名不被遮蔽从精确声明域推导，域保留在调用者侧。独立夹具及返回布局控制见[第93步](audit/STAGE93_TCB_SUCCESS_INTERNAL.md)与本步冻结报告。

仍需两项外部CPU Hook规格，尚非WFIFun或调用分配／释放执行证明。六门94/1/1/1/1/0不变，GOOD_OS与同程序K1–K4开放，uCOS3未开始，目标active；未提交／推送。下方历史原文保留。
<!-- tcb-success-internal-checkpoint-end -->

<!-- tcb-empty-internal-checkpoint-start -->
## 最新检查点：OS_TCBInit 空链表路径接通标准函数构造器

第92步把真实空链表失败路径接到 BuildPreI／BuildRetI：七个实参按真实顺序检查，两个局部的地址及任意旧值由框架断言取得，返回时完整交回全部九个变量资源与原局部定义域。外部规格不含局部绑定；全局91不被遮蔽从准确声明域推导。详见[第92步](audit/STAGE92_TCB_EMPTY_INTERNAL.md)。

这是NULL入口的受限函数契约，不是非空成功契约、WFIFun或新增alloc/free执行证明。六门94/1/1/1/1/0不变，GOOD_OS及同程序K1–K4仍开放，uCOS3未开始；未提交／推送。下方历史原文保留。
<!-- tcb-empty-internal-checkpoint-end -->

<!-- tcb-body-hoare-checkpoint-start -->
## 最新检查点：OS_TCBInit 空／非空入口统一函数体 Hoare

第91步把真实空链表失败路径和非空成功路径接到同一个完整函数体及析取入口，返回66／0分别精确保留各自完整资源，排除无值和其他码；无额外Boolean分支oracle。成功路径仍需两项外部Hook规格查找，失败路径的无Hook规格证明另行保留。详见[第91步](audit/STAGE91_TCB_BODY_HOARE.md)。

独立字面入口共享GE/LE及地址，但两支资源／权限并不相同，不宣称只改head就互换。统一body不是调用分配／回收、WFIFun或全局程序连接；具体验证与旧失败保留情况见本步final-report。六门94/1/1/1/1/0不变，GOOD_OS及同程序K1–K4开放，uCOS3未开始，目标active；未提交／推送。下方历史原文保留。
<!-- tcb-body-hoare-checkpoint-end -->

<!-- tcb-hook-call-checkpoint-start -->
## 最新检查点：两个真实 CPU Hook 调用现场接入 call_rule

第90步从真实ptcb局部load推导单参数／指针类型，分离26／27个Hook资源cell与调用者9个局部／参数cell及绑定，直接应用call_rule并接回完整非空函数体。接口不再接受两个Hook的InfRules前提，但仍需两项外部规格查找；新增GoodFunAsrt R限制，规格是调用现场特化，不是统一port实现或WFIFun。详见[第90步](audit/STAGE90_TCB_HOOK_CALL.md)。

独立两调用位置×NULL／非NULL联合入口、实际参数读取、错误指针／有值返回排除与有限规格表查找见本步证据。未将CPU Hook改成skip或伪造实现。六门94/1/1/1/1/0不变，GOOD_OS与同程序K1–K4未完成，uCOS3未开始；目标active，未提交／推送。下方历史原文保留。
<!-- tcb-hook-call-checkpoint-end -->

<!-- tcb-linked-hoare-checkpoint-start -->
## 最新检查点：完整非空函数体接通任务发布／返回

第89步用真实字节资源桥接，将第88步发布Hoare接入第87步完整函数体；原先三项开放Hoare缩为两个真实CPU Hook的契约，不再接受发布段／资源视图／求值轨迹oracle前提。25个剩余cell保留于return frame，含优先级槽、其余初始化字段、参数及free-head；原C和函数体语法不变。详见[第89步](audit/STAGE89_TCB_LINKED_HOARE.md)。

独立NULL／非NULL联合入口核心35／36cell、96／100字节，新18字段／两局部／槽全Vundef；同block不同offset，实际post读取与仅改free-head的单因素控制分别验证。完整body仍以两个真实Hook的Hoare为前提，非无条件WFIFun或调用分配／free证明。六门94/1/1/1/1/0不变，GOOD_OS和同程序K1–K4未完成，uCOS3未开始；目标active，未提交／推送。下方历史原文保留。
<!-- tcb-linked-hoare-checkpoint-end -->

<!-- tcb-publish-hoare-checkpoint-start -->
## 最新检查点：真实任务发布及返回段的直接 Hoare

第88步直接证明既有发布段的链表两分支、ready位OR、计数递增、临界区进入／退出和return0；接口没有执行轨迹或该段Hoare前提。独立NULL／非NULL联合内存、同block不同offset、实际链接／位图／计数读回及单因素错误post检查，见[第88步](audit/STAGE88_TCB_PUBLISH_HOARE.md)。

本步尚未桥接第87步完整函数体的资源视图，因此不能直接删除其中的发布前提。两个CPU Hook、WFIFun及全局Inv仍开放。六门94/1/1/1/1/0不变，GOOD_OS与同程序K1–K4未完成，uCOS3未开始，目标active；未提交／推送。下方历史原文保留。
<!-- tcb-publish-hoare-checkpoint-end -->

<!-- tcb-priority-hoare-checkpoint-start -->
## 最新检查点：两个真实 Hook 之间的优先级表写入 Hoare

第87步直接证明真实 `encrit; OSTCBPrioTbl[prio]=ptcb; excrit`，从实际参数读取计算数组地址，旧槽允许Vundef，关闭中断入口及任意临界区栈恢复。原函数体不变，整个suffix开放义务缩为两个独立真实Hook调用和发布／返回三项；没有把Hook实现或发布段算作完成。详见[第87步](audit/STAGE87_TCB_PRIORITY_HOARE.md)。

独立32cell/90字节联合入口包含字段、参数、两个局部、free-list、优先级槽、只读当前指针与哨兵；原入口18字段／两局部／槽全Vundef。无条件bracket及保留三义务的完整body实例、post槽实际load／排除NULL／free-head保持分别检查。控制与内核／回归／清理结果见本步final-report；六门94/1/1/1/1/0不变，GOOD_OS及同程序K1–K4仍开放，uCOS3未开始，目标active，未提交／推送。下方历史原文保留。
<!-- tcb-priority-hoare-checkpoint-end -->

<!-- tcb-success-hoare-checkpoint-start -->
## 最新检查点：非空空闲链表路径接入框架 Hoare

第86步直接证明cpu_sr置0、真实head load、非空guard、free-list pop、临界区退出并连接18字段段。无suffix前提的pop/excrit/字段Hoare已完成；既有完整函数体的条件Hoare及RuleSem显式保留真实success_suffix的InfRules义务，两个CPU Hook、优先级表、发布和return尚未兑现，不是整函数WFIFun。详见[第86步](audit/STAGE86_TCB_SUCCESS_HOARE.md)。

独立31cell/86字节联合入口包含全Vundef旧字段、两个可Vundef局部、真实参数、next、只读当前指针与哨兵。只改post head next→旧head的同证明体控制被拒绝，另有实际读回／排除与next保持定理。核心字节数77误写被内核拒绝并修正为81，初次全测的并发编写失败完整保留，固定最终源后重跑，不降低门槛。

252活动模块加1探针内核复核及33根假设检查；252源增量构建（非cold）、6项新检查通过。稳定全仓1412测试仍423失败、1错误，424旧诊断ID原序不变；默认audit身份过期和旧框架空白仍退出2。清理后结果见本步final-report。六门94/1/1/1/1/0不变，GOOD_OS及同程序K1–K4开放，uCOS3未开始；目标active，未提交／推送。下方历史原文保留。
<!-- tcb-success-hoare-checkpoint-end -->

<!-- tcb-fields-hoare-checkpoint-start -->
## 最新检查点：成功路径18字段初始化接入框架 Hoare

第85步直接用assign_rule和seq_rule证明既有18次真实写入，再由RuleSound得到RuleSem；输入不是存在性轨迹，旧字段可全Vundef，位图掩码从刚写的坐标字段真实读取计算。同一程序的资源后果保留全部旧任务记录，并建立新ready记录；任务map的set是规格参数，不冒充已执行的抽象状态更新。详见[第85步](audit/STAGE85_TCB_FIELDS_HOARE.md)。

独立28cell/74字节和35cell/84字节联合入口通过，包含旧任务、真实输入/绑定、局部不变量及哨兵。有效控制只将后置优先级11改10、证明体不变，被接口拒绝；初始两次缺导入失败如实保留，不计为有效负控。前瞻计划中的真实prefix连接尚未交付：本步仅18字段段，尚无free-list pop／Hook／发布／返回的成功路径Hoare或整函数WFIFun。

251活动源增量构建（非cold）及6项新结构检查通过；251活动模块加1探针coqchk通过，28根假设仅框架既有三项。全仓1406测试仍423失败、1错误，424个旧诊断ID与第84步原序相同；默认audit覆盖身份过期和旧框架行尾空白仍退出2。清理后构建和完整回归结果见本步final-report；六门94/1/1/1/1/0不变，GOOD_OS与同程序K1–K4仍开放，uCOS3未开始，目标active，未提交／推送。下方历史原文保留。
<!-- tcb-fields-hoare-checkpoint-end -->

<!-- tcb-empty-hoare-checkpoint-start -->
## 最新检查点：OS_TCBInit 空链表分支接入框架 Hoare

第84步不再仅给出存在性轨迹，而是直接用框架规则证明既有完整函数体在空闲链表头NULL、入口中断已关闭时返回66，随后由RuleSound得到RuleSem。实际完成cpu_sr置0、只读加载、守卫判定、临界区push/pop和return；成功分支及两个真实Hook调用仍在语法中，由真实NULL判定证明其不可达，不对成功路径授信用。详见[第84步](audit/STAGE84_TCB_EMPTY_HOARE.md)。

独立5cell/17字节实例同时满足GoodFrm与CurLINV条件，两局部初值Vundef，含只读当前任务指针和哨兵77，原临界区栈任意。无Hook条目的规格实例通过；同证明体仅将后置返回66改为0的控制被拒绝。函数体Hoare不包含调用分配/free，局部对象仍在返回断言中；启中断入口、成功路径Hoare与WFIFun仍开放。

250活动源增量构建（非cold）和6项新增结构检查通过；全仓1400测试仍423失败、1错误，与上步424项旧诊断逐项一致。默认audit覆盖身份过期及旧框架行尾空白仍退出2；250活动模块及1独立探针的coqchk通过，19定理根仅依赖框架既有三项假设；清理后构建通过，完整测试诊断未变，结果见本步final-report，不宣称全绿。六门94/1/1/1/1/0不变，整核GOOD_OS及同程序K1–K4仍开放，uCOS3未开始，目标active，未提交／推送。下方历史原文保留。
<!-- tcb-empty-hoare-checkpoint-end -->

<!-- call-records-checkpoint-start -->
## 最新检查点：真实调用分配到条件返回的任务记录连接

第83步从真正的sfexec调用者入口开始，实际分配7形参和2局部对象、初始化cpu_sr，接通已有初始化／两Hook契约／优先级表／发布／return/free链。同一Mf联合保留全部任务记录和幸存字段，恢复caller，释放9对象29字节；没有在入口预先摆放局部对象。详见[第83步](audit/STAGE83_CALL_RECORDS.md)。

独立35cell/85字节入口的新18字段均Vundef，9局部块的所有偏移均空。具体程序绑定900到当前函数，901/902缺失：无Hook前提实际分配并运行到首Hook，建立新旧记录；不给下游信用。完整条件链同Mf保留11项读取和全部释放事实。可逆原始单元视图保存原p/pend/type见证，通用旧记录状态不受ready限制，但独立实例只覆盖ready。两个CPU Hook仍无实现，应用hooks关闭不等于CPU Hook调用为空。

249活动源增量构建（非cold）、6项新增结构检查、249活动模块加2独立模块的coqchk、71根假设检查通过，仅框架既有三项假设。全仓1394测试仍423失败、1错误，424项旧诊断逐项相同；默认audit覆盖身份过期和旧framework行尾空白均仍退出2。清理后结果及清单见本步final-report，不宣称全绿。完整OSInit/startup/global Inv、GOOD_OS与同程序K1–K4仍开放；六门94/1/1/1/1/0不变，uCOS3未开始，目标active，未提交／推送。下方历史原文保留。
<!-- call-records-checkpoint-end -->

<!-- init-publish-records-checkpoint-start -->
## 最新检查点：初始化到发布返回的同一内存记录连接

第82步从已分配局部对象后的真实prefix开始，执行空闲链表pop和18次初始化写入，建立新记录并保留旧记录；在两个未兑现的真实Hook执行/资源契约下，接通优先级表、发布与return/free。同一Mf联合保留记录、初始化剩余字段、优先级表/空闲表及发布结果，恢复caller并释放29字节。详见[第82步](audit/STAGE82_INIT_PUBLISH_RECORDS.md)。

44cell/114字节独立字面入口的新18字段全Vundef，旧/新任务同block不同offset。无Hook前提的真实prefix建立两记录并排除错误优先级；缺失Hook负例只授prefix信用。完整条件链同Mf给出11项读取及29字节释放；两个Hook契约尚无具体实现，非无条件整函数调用。

248活动源增量构建及6项新结构检查通过（非cold）；全仓1388测试仍423失败、1错误，424项旧诊断一致。默认audit覆盖身份过期仍退出2；旧framework行尾空白仍使git diff --check退出2。内核、假设和清理后结果见本步final-report，不宣称全绿。完整OSInit/startup/global Inv、GOOD_OS及同程序K1–K4仍开放；六门94/1/1/1/1/0不变，uCOS3未开始，目标active，未提交/推送。下方历史原文保留。
<!-- init-publish-records-checkpoint-end -->

<!-- publish-return-records-checkpoint-start -->
## 最新检查点：真实返回与局部释放保留全部任务记录

第81步将第80步发布结果接到真实return/free：恢复caller、返回0、9局部对象29字节实际释放；同一Mf联合保留全部记录、发布结果和有限幸存frame。不运输任意依赖局部环境的断言，不复制写权限。详见[第81步](audit/STAGE81_PUBLISH_RETURN_RECORDS.md)。

独立31cell/72字节入口含同block不同offset的新旧任务、非空旧head及不同caller环境；同末态给出两记录、查询、8项读取和全部释放事实。语义反例排除局部ptcb权限在释放后仍存活；仅改新记录后置priority11→10的同证明体负控另检。247源增量构建及6项新结构检查通过（非cold）；247活动模块加2独立模块的coqchk及62根假设检查通过，仅框架既有三项假设。全仓1382测试仍423失败、1错误，424项旧诊断逐项一致；默认audit仍因覆盖身份过期退出2。清理实测见本步final-report，不宣称全绿。

只覆盖第二Hook返回后的真实后缀，不是Hook实现或完整函数入口可达性。完整初始化/启动/global Inv、GOOD_OS及同程序K1–K4仍开放；六门94/1/1/1/1/0不变，uCOS3未开始，目标active，未提交/推送。下方历史原文保留。
<!-- publish-return-records-checkpoint-end -->

<!-- publish-records-checkpoint-start -->
## 最新检查点：真实任务发布保留全部任务记录资源

从包含新任务的全记录所有权中借出y/by/bx三个字段供真实发布读取，再归还并重组同一记录集合，不额外索要重复权限。链表next/prev/head、非空旧head回链、位图和计数实际写入，任意frame保留。详见[第80步](audit/STAGE80_PUBLISH_RECORDS.md)。

独立23cell/47字节入口含同块不同偏移的旧、新任务和非空旧head；一次执行的同一Mf同时给出两记录、map查询及8项真实读取。实际末态排除旧head回链仍NULL；另有仅改新记录后置优先级11→10的同证明体控制，计划在控制编译前冻结。任务map仅为规格参数，O不变，不声称完整TCB/Hook/OSInit/启动组合/全局Inv完成。

246源增量构建（非cold）与6项新结构测试通过；全仓1376测试仍423失败、1错误，424项旧诊断逐项一致。246活动模块及2独立模块的coqchk、65根假设检查通过，假设并集仅为框架既有三项。清理22项本轮临时文件并恢复旧缓存；清理后实测见本步final-report。默认audit仍因覆盖身份过期失败，不宣称全绿。六门94/1/1/1/1/0，GOOD_OS及同程序K1–K4仍开放，uCOS3未开始，目标active，未提交/推送。下方历史原文保留。
<!-- publish-records-checkpoint-end -->

<!-- init-all-records-checkpoint-start -->
## 最新检查点：真实字段初始化扩展全任务记录资源

从新TCB原18字段及8输入的所有权，真实执行18次写入，在同一Mf保留所有旧任务记录并加入新记录；canonical map按任务ID插入，剩余11字段和任意frame保留，无写权限复制。详见[第79步](audit/STAGE79_INIT_ALL_RECORDS.md)。

独立34cell/83字节入口包含一个旧任务和一个新任务，两者共用block301不同偏移，实际覆盖递归插入。正例从同次执行给出全记录与哨兵；错误旧优先级目标映射在实际末态被排除，新记录优先级同证明体负控另检。任务映射只是规格参数，真实O不变，不声称发布已执行或完整TCB/OSInit/全局Inv已完成。

245源增量构建及6项新结构测试通过，非cold；全仓1370测试仍423失败、1错误，与上步424项旧诊断完全一致。245活动模块及2独立模块的coqchk、63根假设检查通过，清理22项本轮临时文件并恢复旧缓存；清理后结果见本步final-report；默认audit覆盖身份过期仍失败，不宣称全绿。44字节初始化字段不等于56字节完整TCB；完整启动组合、GOOD_OS及同程序K1–K4仍开放，六门94/1/1/1/1/0，uCOS3未开始，目标active，未提交/推送。下方历史原文保留。
<!-- init-all-records-checkpoint-end -->

<!-- start-record-checkpoint-start -->
## 最新检查点：真实启动保留所选初始化任务记录

不预设 CurTid 或任务记录，从18个实际初始化字段的原始所有权执行真实 OSStart 调用；同一 Mf 返回两个当前指针半份额、所选7字段记录和其余11字段，抽象任务表查询与最高就绪选择对应。字段只移交一次，不复制写权限。详见[第78步](audit/STAGE78_START_RECORD.md)。

字面入口实际包含TCB字段且无初始CurTid。只改入口物理优先级12→11，地址(90,50)以外的入口内存完全相同；两臂都运行到端口，负例最终不能建立优先级12记录。同证明体错误记录后置亦被拒绝。主接口消费初始化结果格式，尚未证明该启动入口由完整OSInit到达；44字节初始化字段不是56字节完整TCB。

244源增量构建及6项新结构回归通过，非cold；内核/假设检查与清理见本步final-report。全仓1364测试仍423失败、1错误，与上步424旧诊断完全一致；默认audit覆盖身份过期仍失败，不宣称全绿。完整全局Inv、抽象当前任务更新、端口执行、GOOD_OS和同程序K1–K4仍缺；六门94/1/1/1/1/0，uCOS3未开始，目标active，未提交/推送。下方历史原文保留。
<!-- start-record-checkpoint-end -->

<!-- start-current-checkpoint-start -->
## 最新检查点：启动写入建立框架真正的 CurTid

实际 OSStart 使用保留标识符 `OSTCBCur=60`，不预设当前任务；从 NULL 入口执行真实调用后，将同一当前指针完整所有权拆成两个 CurTid 半份额，保留其余单元。最高任务接口由实际位图／任务表／优先级表关系推出选择结果。详见[第77步](audit/STAGE77_START_CURRENT.md)。

独立字面实例证明入口不存在 CurTid，端口前同 Mf 保留半份额并读回指针、运行字节0和哨兵123。只改变保留绑定的对照两臂都实际执行到端口；缺绑定的一臂虽有正确指针，却不能建立 CurTid。仅改一个 CurTid 目标的同证明体负控被拒绝。

243源增量构建通过（非cold）；Coq内核、假设、全仓回归及清理实际结果见本步 final-report。仍未执行端口／修改抽象当前任务／建立完整全局 Inv，非 localHoare／WFIFun／GOOD_OS；旧回归失败及覆盖身份过期保留。六门94/1/1/1/1/0，同程序K1–K4未完成，uCOS3未开始；目标active，未提交／推送。下方历史原文保留。
<!-- start-current-checkpoint-end -->

<!-- start-port-checkpoint-start -->
## 最新检查点：OSStart 真实调用到达 CPU 启动端口

不假定启动前已有当前任务：从有界实际内存构造调度器局部块，执行真实调用／两次赋值／释放返回，接通 OSStart guard、三个字段写入和 OSStartHighRdy 的 sfexec 入口；运行字节为1时实际完整调用原样返回。最高就绪任务由位图与优先级表关系推出，而非作为结果前提。详见[第76步](audit/STAGE76_START.md)。

独立字面入口含空当前任务指针、仅任务12就绪，冷启动同 Mf 读回7项；实际实例化最高任务包装接口。端口在测试程序中明确缺实现；主结果停在入口，OSRunning仍为0，没有修改抽象当前任务或建立真实全局 Inv。错误当前指针后置负控与0／1运行字节对照通过，不授端口或所有交错执行信用。

242源增量构建（非cold）通过；新增5项结构回归通过。全仓回归、假设、coqchk及清理实际结果见本步final-report，不宣称旧回归全绿；默认审计的覆盖身份过期仍保留。C／配置／框架语义／旧证据未修改。六门仍94/1/1/1/1/0，GOOD_OS、同程序K1–K4、完整OSInit及运行态连接未完成，uCOS3未开始；目标active，未提交／推送。下方历史原文保留。
<!-- start-port-checkpoint-end -->

<!-- init-misc-hoare-checkpoint-start -->
## 最新检查点：OS_InitMisc 完整函数体接入框架 Hoare 证明

保留原函数模型及 C，增加真正经过语义证明的 `skip_rule`，并为十次清零、行政空尾及 void return 构造 `InfRules` 和 `RuleSem`。239源增量重建／最终构建检查通过（非cold），239活动模块加2独立验证模块的 `coqchk` 通过；58根假设检查仅含框架已有三项标准假设。独立可满足入口和两项同证明体错误后置负控通过。详见[第75步报告](audit/STAGE75_INIT_MISC_HOARE.md)及其 final-report。

全仓1348测试仍423失败、1错误，397旧诊断全部保留，新增27项是旧源／产物身份快照拒绝本次框架修改；不宣称回归全绿。`make audit` 退出2，函数覆盖证据身份过期未解决；旧测试及冻结证据未改写。

前提仍需保留 frame 蕴含真实 CurLINV；独立可满足 fixture 不是启动可达性，也没有实例化真实全局 Inv。下一步须处理初始化结果到真实运行态不变量的连接，再把适用函数接入内部规格构造器及统一程序，不能假装启动前已有当前任务。六门仍94/1/1/1/1/0，GOOD_OS与同程序K1–K4未完成，uCOS3未开始。更正历史文字：第57步已接通七调用同一内存，完整OSInit与启动到运行态连接仍缺。未提交／推送。
<!-- init-misc-hoare-checkpoint-end -->

<!-- task-create-fresh-checkpoint-start -->
## 最新检查点：实际调用自动构造12个新对象的块

`V293_create_fresh_call_prologue` 从任意有界实际内存构造12个互异fresh块，避开任意有限幸存cell集合，并真实执行9参数写入和3局部分配。`V293_OSTaskCreateExt_fresh_success_call_under_hooks` 将这一选择接到既有完整条件调用，不再输入块选择/互异/fresh/幸存分离假设。

**完整接口仍需要覆盖所有合法新布局的三个真实Hook契约家族，这是比固定布局契约更强的前提，并非无条件证明升级。** 五端口实现仍缺；无Hook的入口分配与有条件的完整成功严格分开。独立零大小cell反例表明fresh不等于避开逻辑cell；有限幸存上界不能省略。详见[第74步](audit/STAGE74_TASK_CREATE_FRESH.md)。

238源增量构建（非cold）复用1185旧产物；全量回归及信任/清理以本步final-report为准。第73步旧测试精确比较整个活动源列表，新增源会触发其过期断言；本步不修改旧测试或删除失败。非localHoare/全执行safety/GOOD_OS，六门仍94/1/1/1/1/0，同程序K1–K4及OSInit七调用同一内存仍开放。uCOS3未开始，目标active；未提交/推送。下方历史原文保留。
<!-- task-create-fresh-checkpoint-end -->

<!-- task-create-call-checkpoint-start -->
## 最新检查点：创建函数真实调用分配接通条件成功返回

`V293_OSTaskCreateExt_success_call_under_hooks` 从已求值实参的sfexec开始，真实分配/写入9参数与3局部对象，在同一实际内存接入已有body和return证明；创建12对象38字节与TCB调用9对象29字节最终释放，恢复原caller并保留31项结果。完整getaddr布局从实际新LE推出；互异fresh块选择与幸存块分离仍显式。详见[第73步](audit/STAGE73_TASK_CREATE_CALL.md)。

独立literal初始内存不含创建局部块；完整返回仍依赖三个未兑现Hook契约，缺五端口实现不变。仅改opt值的单因素锚点只验证call类型派发，不授下游信用。237源增量构建复用1175旧产物，非cold；信任/回归/清理实际结果见本步final-report。

不是上层C实参求值、localHoare、所有执行safety或GOOD_OS；六门仍94/1/1/1/1/0，同程序K1–K4、调度、OSInit七调用连续内存仍开放，uCOS3未启动，目标active，未提交/推送。下方历史原文保留。
<!-- task-create-call-checkpoint-end -->

<!-- task-create-return-checkpoint-start -->
## 最新检查点：创建函数真实释放局部对象并恢复上层调用者

`V293_OSTaskCreateExt_success_return_under_hooks` 从实际body入口，经三个真实Hook契约、TCB成功创建与err赋值、OSRunning=0的真实return err，继续执行sretv/sfree/sfreeend。创建自身12对象38字节释放，恢复caller，同一Mr保留31项发布/全局/frame数据及TCB调用9对象29字节已释放。详见[第72步](audit/STAGE72_TASK_CREATE_RETURN.md)。

getaddr完整布局、唯一块和幸存块分离仍为显式前提，创建入口的实际分配尚未证明；三个Hook契约未兑现，缺五端口实现事实不变。只改变return continuation是否含kcall的独立锚点消融仅授返回派发信用，不授完整body/Hook信用。

235活动源增量构建复用1170旧产物，非cold；信任、回归和清理见本步final-report。非localHoare/全执行safety/GOOD_OS；六门94/1/1/1/1/0不升级，同程序K1–K4及OSInit七调用实际内存仍开放，uCOS3未启动，目标active，未提交/推送。下方历史原文保留。
<!-- task-create-return-checkpoint-end -->

<!-- task-create-suffix-checkpoint-start -->
## 最新检查点：精确创建成功后缀连接运行态分支

`V293_OSTaskCreateExt_success_dispatch_under_hooks` 在第70步真实Mf继续执行源码后缀：OSRunning=0时实际求值return err得到0、停在kret；OSRunning=1时到真实OS_Sched的sfexec，保留return continuation。同一Mf和caller frame不变，TCB调用9对象29字节仍释放。详见[第71步](audit/STAGE71_TASK_CREATE_SUFFIX.md)。

三个真实Hook契约仍未兑现，未造调度noop。错误分支enter/slot=NULL/exit完整保留但本步未证明执行。p12/running0完整条件literal实例43项读回；running1只有生产泛化证明和独立suffix锚点，不称完整body literal。只改running字节的消融仅授后缀分支决策信用。

234活动源增量构建复用1160旧产物，非cold；信任/回归/清理以本步final-report为准。仍缺五端口实现，创建自身分配/释放返回、实际调度器和OSInit七调用连续内存未接。手工前端ADR4/5/7、非localHoare/全执行safety/GOOD_OS；六门94/1/1/1/1/0不升级，同程序K1–K4开放，uCOS3未启动，目标active，未提交/推送。下方历史原文保留。
<!-- task-create-suffix-checkpoint-end -->

<!-- task-create-result-checkpoint-start -->
## 最新检查点：TCB返回值真实写入caller的err

`V293_OSTaskCreateExt_result_assigned_under_hooks` 在第69步真实返回内存上执行caller地址求值和err字节store；同一最终Mf中err=0、42项结果及caller frame保留、TCB调用9对象29字节仍全部释放。err块与已释放块不别名从可写字节／释放事实推导，没有新增假设。详见[第70步](audit/STAGE70_TASK_CREATE_RESULT.md)。

三个真实Hook契约完全沿用，尚未兑现；固定缺Hook程序不因此成功。独立字面内存可满足，一个p12条件实例42项typed读回；四个同证明体负控及只改变err写权限的真实store决策消融见本步证据。权限实验仅授store决策信用，不授Hook／全路径信用。232源增量构建复用1155旧产物，非cold；信任／回归／清理数字见final-report。

精确创建后缀尚未建模，五端口实现、调用者分配及OSInit七调用实际内存仍开放。手工前端ADR0004/5/7；非localHoare、全执行safety或GOOD_OS。六门仍94/1/1/1/1/0，同程序K1–K4开放，uCOS3未启动，目标active；未提交／推送。下方历史原文保留。
<!-- task-create-result-checkpoint-end -->

<!-- task-create-tcb-return-checkpoint-start -->
## 最新检查点：任务创建入口接通TCB成功返回

`V293_OSTaskCreateExt_to_TCB_success_under_hooks` 将已有函数体前缀、栈返回及psp写入、七参数求值与第65步TCB完整成功调用接通，在同一实际Mbridge分配并最终释放9对象29字节，返回0、恢复caller并保留frame。优先级表槽仅移交一次，不重复拥有。**三个真实Hook返回义务仍开放**；固定缺Hook程序并没有成功运行。详见[第69步](audit/STAGE69_TASK_CREATE_TCB_RETURN.md)。

独立字面内存可满足；一个p12完整条件实例同Mf读回42项。主轨迹停在待写err的continuation，err仍9；只删除kassignr的独立真实执行消融验证err赋值锚点，不授全路径信用。231源增量构建复用1150旧产物；信任与回归见本步final-report。前五次生产证明失败及首probe失败均保留，最终以proof06/probe02身份为准。

非完整创建/OSInit、localHoare、全执行safety或GOOD_OS；五端口仍缺实现，err主轨迹赋值、创建后缀和七调用实际Mf未接。手工前端ADR0004/5/7边界不变。六门94/1/1/1/1/0、同程序K1–K4开放，uCOS3未开始，目标active；未提交/推送。下方历史原文保留。
<!-- task-create-tcb-return-checkpoint-end -->

<!-- task-create-tcb-entry-checkpoint-start -->
## 最新检查点：栈返回值写入psp，连接TCB七参数入口

`V293_OSTaskCreateExt_to_TCB_under_stack_return` 从body入口连接已有前缀、四参数栈调用、**显式真实Hook返回义务**、实际psp写入及OS_TCBInit七参数求值，停在TCB的sfexec。同一Mf中的psp就是第二个源参数；没有伪造Hook实现或要求全内存不变。详见[第68步](audit/STAGE68_TASK_CREATE_TCB_ENTRY.md)。

另有无条件“Hook已经返回”锚点定理；p0/p12 × NULL/nonnull四份返回锚点可满足，各17typed读取。它们不是固定程序已到达的返回点。两份body字面入口则真实到缺StackHook并停住，排除零步伪返回。三项同证明体终点负控与只删除kassignr wrapper的实际执行消融通过；消融仅授赋值锚点信用。

230源增量构建复用1140旧产物，非cold；信任/回归/清理数字见本步final-report。手工前端沿用ADR0004/5/7；5Hook缺实现、caller分配、TCB body/第65步完整连接、err赋值和创建后缀仍开放。非localHoare/全执行safety/GOOD_OS；六门仍94/1/1/1/1/0，同程序K1–K4开放，uCOS3未开始，目标active；未提交/推送。下方历史原文保留。
<!-- task-create-tcb-entry-checkpoint-end -->

<!-- task-create-stack-entry-checkpoint-start -->
## 最新检查点：任务创建四个实参求值，真实到达栈Hook入口

`V293_OSTaskCreateExt_to_stack_hook` 从函数体入口所有权连续执行第66步前缀、调用准备和四个实参实际求值，到达 `OSTaskStkInit` 的 `sfexec`，保留 `kassignr psp`。**没有查询、分配或执行Hook函数体，psp尚未更新。** 详见[第67步](audit/STAGE67_TASK_CREATE_STACK_ENTRY.md)。

复用框架uint32函数标识符表示task（新ADR0007），证明范围内解码准确且单射；非机器函数地址或ABI证明，源码任务到pc的统一映射仍开放。p0/p12 × selector700/701四份独立字面入口，各读回同一Mf的12字段，IE任意且恢复，si/ci不变；对P900=None实际到达缺Hook入口并证明无下一步，不再是未绑定task的早期拒绝。

三项同证明体终点负控分别拒绝参数换序、错误selector和frame值；表示实验仅授解码器决策信用，不授前缀/下游信用。228源增量构建复用1135旧产物，非冷构建；信任/回归/清理数字见本步final-report。

手工前端，沿用ADR0004/0005；函数调用分配、Hook实现、创建后缀及第65步TCB连接未完成。不是完整任务创建/OSInit、local Hoare、全执行safety或GOOD_OS；五端口仍缺实现，七调用实际Mf未接。六门仍94/1/1/1/1/0，同程序K1–K4开放，uCOS3未启动，目标active；未提交/推送。下方历史原文保留。
<!-- task-create-stack-entry-checkpoint-end -->

<!-- task-create-reservation-checkpoint-start -->
## 最新检查点：任务创建的优先级预留与栈调用准备

`V293_OSTaskCreateExt_to_stack_call_setup` 从函数体入口的环境和内存所有权出发，执行 CPU_SR 初值写入、三个条件检查、优先级槽真实预留写入、临界区退出，以及 `psp = OSTaskStkInit(...)` 的赋值调用准备。终点是带 `kassignr` 的 `scall`，**尚未求值四个实参、查询或执行栈初始化 Hook**。详见[第66步](audit/STAGE66_TASK_CREATE_RESERVATION.md)。

独立 p0／p12 两份字面入口可满足，各读回同一 Mf 的8项字段；IE任意且恢复，si／ci不变。三项同证明体终点负控，以及只改变预留赋值RHS的真实执行消融通过核对；消融不授整个前缀或下游信用。227源增量构建复用1125旧产物，非冷构建；信任与回归数字以本步 final-report 为准。

复用ADR0004符号保留地址与ADR0005临界宏归一化；手工前端、未分配的函数体入口、后缀未执行。不是完整任务创建／OSInit、local Hoare、全执行 safety 或 GOOD_OS；七调用实际内存未接，五个端口Hook缺实现。六门仍94/1/1/1/1/0，同程序K1–K4开放；uCOS3未开始，目标active，未提交／推送。下方历史原文保留。
<!-- task-create-reservation-checkpoint-end -->

<!-- tcb-call-success-checkpoint-start -->
## 最新检查点：OS_TCBInit 入口至成功返回的条件连接

`V293_OS_TCBInit_success_call_under_hooks` 连通实际分配/初始化、两个显式真实Hook返回义务、优先级表写入、发布、return 0和9对象29字节释放；自动构造fresh且避开所有存活块的9对象，同一Mf保有15个其它初始化字段、发布结果、free-head后继、优先级槽和caller frame。详见[第65步](audit/STAGE65_TCB_CALL_SUCCESS.md)。

独立四份literal入口可满足；完整成功输出是任意P下的**条件实例**，每例31/32项typed读取，并非固定缺Hook程序成功运行。同入口另证固定程序实际到达首Hook后无下一步。两个Hook契约未兑现，未造noop；P502一步查询消融不执行sentinel、不授下游信用。225源增量构建复用1120旧产物，非cold，最终信任/回归/清理见本步final-report。

仍是手工前端/宏映射、存在性无交错轨迹，非无条件完整OS_TCBInit、local Hoare、全执行safety或GOOD_OS；七调用实际Mf未接，五端口Hook缺实现。六门94/1/1/1/1/0不升，同程序K1–K4开放，uCOS3未开始，目标active；未提交/推送。下方历史原文保留。
<!-- tcb-call-success-checkpoint-end -->

<!-- tcb-success-return-checkpoint-start -->
## 最新检查点：第二Hook返回后的发布、return 0与释放

`V293_OS_TCBInit_success_suffix_return` 从**第二Hook已返回的精确锚点**连续执行任务链／ready位图／计数发布、return 0，释放9对象29字节并恢复caller；发布Ms直接连接到返回Mf，同一Mf保有存活字段与frame。显式要求NoDup及存活块Away，未自动推导入口freshness。详见[第64步](audit/STAGE64_TCB_SUCCESS_RETURN.md)。

独立p12／p11 × 旧链头NULL／非空四例，每例13／14项typed读回和29字节释放；初始IE任意，si／ci不变。最终同证明体四终点负控拒绝错误返回、计数、保护字及释放结果；原positive成员tactic失败保留。另行前瞻低层权限消融证明相同saved值可读不代表可释放，**不授publication／完整return消融信用**；原整片段权限实验未执行。224源增量构建复用1115旧产物，非cold；信任／回归／清理详见final-report。

缺失5个端口Hook未实现，锚点可达性未证明，未连接函数入口／七调用实际Mf。手工前端及宏映射擦除CPU_SR字节效应；存在性无交错轨迹，非完整OS_TCBInit／OSInit、local Hoare、全执行safety或GOOD_OS。六门仍94/1/1/1/1/0，同程序K1–K4开放；uCOS3未开始，目标active，未提交／推送。下方历史原文保留。
<!-- tcb-success-return-checkpoint-end -->

<!-- tcb-priority-hook-checkpoint-start -->
## 最新检查点：两个Hook之间的优先级表写入

`V293_OS_TCBInit_priority_to_second_hook` 从**第一个Hook已真实返回的锚点**开始，执行保留函数尾部的enter、`OSTCBPrioTbl[prio]=ptcb`、exit，再求值第二个Hook实参，停在`OSTaskCreateHook(ptcb)`的sfexec。同一Mf保有更新后的表槽及任意frame，IE／si／ci恢复；未执行第二Hook或发布／返回。详见[第63步](audit/STAGE63_TCB_PRIORITY_HOOK.md)。

另有从函数入口到第二Hook的**条件定理**，明确要求提供首Hook的真实返回轨迹和精确内存保护证明；允许未拥有内存变化，不要求输入输出M相等。固定源仍缺五Hook实现，条件尚未落实；独立probe的返回锚点不是已证明可达的入口。`V293_missing_hook_cannot_return`排除缺定义时凭零步返回；未造noop或新增公理。

独立有限入口p12／p11×旧槽pointer／Vundef四例，各10项读回、IE任意；两邻槽、ready group／row、计数及caller两保护字保持不变。三项同证明体终点负控分别拒绝错误Hook指针、表槽和保护字。单因素消融只将待执行表槽赋值变skip：旧指针保留，其余frame及同一第二Hook实参保持；仅授该写入的独立信用，不授Hook或下游发布信用。223源增量构建复用1110旧产物，非cold；50信任根及回归／清理以final-report为准。

手工前端与ADR0005宏归一化仍擦除CPU_SR token字节效应；仅存在性无交错轨迹，不是完整OS_TCBInit／OSInit、local Hoare、全执行安全或GOOD_OS。七调用实际Mf未接，六门仍94/1/1/1/1/0，同程序K1–K4开放，uCOS3未开始，目标active，未提交／推送。下方历史原文保留。
<!-- tcb-priority-hook-checkpoint-end -->

<!-- tcb-success-entry-checkpoint-start -->
## 最新检查点：成功分支从函数入口接到第一个真实Hook调用

`V293_OS_TCBInit_call_to_first_hook` 从七个实参已求值的sfexec开始，真实分配／写入七参数、分配两局部并初始化cpu_sr，取出空闲TCB、初始化18个字段，再实际求值Hook实参，停在`OSTCBInitHook(ptcb)`的sfexec。9个fresh块从任意入口内存的有界性自动构造，不再要求调用者预选。终点保留实际continuation、callee存储及caller frame；**尚未返回或释放**。详见[第62步](audit/STAGE62_TCB_SUCCESS_ENTRY.md)。

独立有限入口覆盖p12／p11和next非空／NULL四份内存；每例25项读回，IE任意。四项同证明体终点负控分别拒绝错误Hook指针、priority、空闲链头和保护字。前瞻单因素实验只改变P501查询：缺Hook无下一步，测试sentinel使查询可走一步，未执行其函数体，**不是真实Hook实现，不授下游机制独立消融信用**。222源增量构建复用1105旧产物，非cold；信任、回归及清理以本步final-report为准。

固定源码五个端口Hook只有声明、无实现。未执行Hook查询／函数体、优先级表写入、ready发布或成功return；未接七调用实际Mf。手工前端及ADR0005宏归一化仍擦除CPU_SR token字节效果；外层七实参表达式求值未证明。只证明存在性无交错轨迹，**不是完整OS_TCBInit／OSInit、local Hoare、全执行安全或GOOD_OS**。六门仍94/1/1/1/1/0，同程序K1–K4开放；uCOS3未开始，未提交／推送。下方历史原文不改写。
<!-- tcb-success-entry-checkpoint-end -->

<!-- tcb-empty-call-checkpoint-start -->
## 最新检查点：OS_TCBInit 空闲链为空时的完整调用生命周期

`V293_OS_TCBInit_empty_call_return` 从七个实参已求值的sfexec入口开始，真实分配／写入七参数、分配两局部、初始化cpu_sr=0，执行NULL分支、退出临界区、返回66并释放9对象共29字节；同一Mf保有链头与caller frame，恢复原caller及任意IE／si／ci。完整归一化函数语法保留成功分支两个真实Hook调用，并未假设它们为空操作。详见[第61步](audit/STAGE61_TCB_EMPTY_CALL.md)。

独立有限入口无TCB／stack存储，caller同名108绑定的88和保护字77均读回；p12／p11是两次独立实例，不是任务共存。只移除callee定义的前瞻消融证明同入口无loststep，**只授整call可用性，不授下游机制独立消融信用**。四最终接口负控在不同位置拒绝。221源增量构建复用1095旧产物，非cold；信任、完整回归、396条旧诊断逐ID保留和清理以本步final-report为准。

仍是手工前端／ADR0005宏映射，CPU_SR token字节效应擦除；入口要求9个已选fresh块，不证明任意M都能自动选块。不含实参表达式求值、成功Hook／优先级表执行、七调用Mf连接或空链可达性。**不是完整OS_TCBInit／OSInit、local Hoare、全执行safety或GOOD_OS**。成功路径Hook在固定配置只有声明、没有函数体，仍开放。六门不晋级，同程序K1–K4开放；uCOS3未开始，未提交／推送。下方历史检查点保留原文。
<!-- tcb-empty-call-checkpoint-end -->

<!-- tcb-publish-checkpoint-start -->
## 最新检查点：OS_TCBInit 的任务链、ready位图与计数发布片段

`V293_OS_TCBInit_publication_execution` 从`OSTaskCreateHook`之后、第三次归一化enter之前开始，连续执行任务链插入、真实NULL判断、group／所选row的OR、任务计数加一和exit，停在return0之前。同一Mf保有字段及任意frame的可写所有权，恢复任意初始IE和si／ci。详见[第60步](audit/STAGE60_TCB_PUBLISH.md)。

p12／p11 ×旧链头非空／NULL四个独立有限内存，分别13／12项读回；不是两任务共存。只删除ready行赋值的单因素消融：该行保留2，其他11／12项及IE／栈不变。四个最终接口负控在不同结论位置拒绝；三次消融harness失败保留，仅显式binder类型和证明tactic修正，冻结结论不改。219源增量构建复用1085旧产物（非cold）；52信任根与四模块coqchk通过；完整回归、396条旧诊断逐ID保留及清理以本步final-report为准。

入口只拥有指定字段，不证明完整TCB分配、链表无环或mask与priority字段关系；计数要求n<255，不含wrap。原protocol中live／allocated措辞不授额外信用。手工前端及ADR0005宏映射擦除CPU_SR字节，不是真端口执行。**未执行前置Hook／优先级表写入，未接第59步前缀或第57步七调用实际内存，未执行return。** 不是local Hoare／所有执行safety／完整OSInit或GOOD_OS。六门不晋级，同程序K1–K4开放，uCOS3未开始；未提交／推送。历史检查点保留原文。
<!-- tcb-publish-checkpoint-end -->

<!-- tcb-init-prefix-checkpoint-start -->
## 最新检查点：OS_TCBInit 的空闲链取出与字段写入已连续连接

`V293_OS_TCBInit_prefix_execution` 从局部初始化之后执行归一化enter、读取空闲链头、真实非空判断、pop、exit及18条字段赋值，在同一Mf停到调用者提供的Hook后缀之前；原失败分支仍保留在continuation。`V293_OS_TCBInit_empty_prefix_execution` 则只需ptcb与NULL链头，无需任何TCB字段，退出临界区到return66之前；**未执行return／释放**。两条轨迹均恢复任意初始IE及已有临界栈。详见[第59步](audit/STAGE59_TCB_INIT_PREFIX.md)。

四个独立入口组合p12／p11与非空／NULL next，各32项同内存读回；初始IE两值可实例化，不是两个任务共存。前瞻只删pop：链头保留旧指针，其余31项与IE／栈不变；四单结论负控在四个指定位置拒绝。旧依赖不一致的两次import失败不授信用，重冻结readiness后才运行有效实验；消融候选作用域错误只修证明tactic的%Z，不改冻结结论。217源增量构建（复用1075旧产物，非cold）；信任、完整回归、旧诊断和清理见本步final-report。

临界宏按ADR0005手工映射并擦除CPU_SR字节，**不是真端口调用仿真**；localalloc／init、Hook、优先级表／任务链／ready发布和成功返回仍开放，未接第57步实际七调用内存。typed next可指回自己，本步不证明链无环或独占分配；任意suffix须由上层填入真实源码。仅存在性无交错片段，非local Hoare／所有执行safety／完整OSInit或GOOD_OS。六门不晋级，同程序K1–K4未闭合，uCOS3未开始；未提交／推送。下方历史检查点保持原文。
<!-- tcb-init-prefix-checkpoint-end -->

<!-- tcb-init-fields-checkpoint-start -->
## 最新检查点：OS_TCBInit 的18条字段写入

`V293_OS_TCBInit_fields_execution` 证明成功分支中、free-list pop及退出临界区之后，到`OSTCBInitHook`之前的连续18条实际赋值：任意旧值（含Vundef）→44字节初始化，并保有8项局部／参数及任意frame。优先级坐标和掩码由真实表达式求值；同一结果内存接到既有task record关系。独立base8有限入口分别使用Idle优先级12和Stat优先级11，各完成31项读回；**两次独立执行不是两个任务已共存**。详见[第58步](audit/STAGE58_TCB_INIT_FIELDS.md)。

整片段→sskip的前瞻消融及四项最终接口负控通过；首版Vundef typed-load错误、全图VM计算中断及后续语法／作用域／参数推断失败均保留，最终只读取精确所有权切片，冻结结论与fixture不变。215源构建复用1065旧产物，非cold；57信任根／四模块coqchk通过。最终回归、396条旧诊断保留及清理以本步final-report为准。只到Hook之前，不包含free-list pop、Hook调用、优先级表／任务链／ready位图发布及返回；**未接到第57步七调用的实际返回内存**。TCB中的rdy只表示内部状态，不表示已经可调度。Port栈初始化及函数地址表示仍开放，未假设Hook无操作；手工前端、存在性无交错执行，非local Hoare／全执行safety／完整OSInit或GOOD_OS。六门不晋级，uCOS3未开始，未提交／推送。下方历史正文仅代表当时证据。
<!-- tcb-init-fields-checkpoint-end -->

<!-- init-seven-calls-checkpoint-start -->
## 最新检查点：Q已接入前六个真实初始化调用

`V293_OSInit_seven_calls` 串联Misc／Ready／TCB／Event／Flag／Mem／Q：从实际Msix构造四个新鲜局部块，入口不假设中间内存或freshness。同一Mf保有全部前缀、Q及frame可写所有权；独立非零／Vundef有限入口同时读回293项（208前缀＋85队列），Q的12局部字节释放，caller同名变量仍为7。详见[第57步](audit/STAGE57_INIT_SEVEN_CALLS.md)。

前瞻只把第七call替换为sskip，仍真实执行前六call；队列非链接字节／链头保持旧值，Mem链接／Ready／frame不变。四项最终接口负控另计，不授内部机制独立消融信用；消融首候选缺少生产模块显式import，失败日志和快照保留，第二候选补import后在全量成员搜索上耗时过长，被明确中断；第三候选只改为精确资源定位，结论或fixture不变。213源构建复用1055旧产物，非cold；100信任根／四模块coqchk、最终回归与清理以本步final-report为准。仍是BeginHook后存在性无交错片段，手工前端，八函数fixture不是完整94P；非local Hoare、所有执行safety或完整OSInit。旧局部可能复用；旧失败保留、六门不晋级。GOOD_OS／同程序K1–K4开放，uCOS3未开始，未提交／推送。下方历史正文仅代表当时证据。
<!-- init-seven-calls-checkpoint-end -->

<!-- init-queue-checkpoint-start -->
## 最新检查点：队列初始化的完整调用

`V293_OS_QInit_call_return` 连接真实96字节清零、原生while三次迭代、四控制块空闲链、尾NULL和链头，并分配／释放源码四局部的12字节。独立全255入口、非空旧链头，在同一Mf读回88项（4链接、80其余零字节、链头、3frame），caller同名变量保持7。详见[第56步](audit/STAGE56_INIT_QUEUE.md)。

**尚未接入第55步六调用的实际返回内存，不是完整OSInit。** 泛型入口仍要求callee freshness／NoDup／Away；手工前端、存在性无交错执行，非local Hoare或所有执行safety；两函数fixture不是完整94P。整call no-op消融与四项最终接口负控分开计账；首版指针低字节预测被符号指针编码反驳，原计划及两次harness失败均保留，另行前瞻协议测量原始非链接字节。211源构建复用1045旧产物，非cold；100信任根／四模块coqchk、回归与清理见最终报告。旧失败保留、六门不晋级；GOOD_OS／同程序K1–K4开放，uCOS3未开始，未提交／推送。下方历史正文仅代表当时证据。
<!-- init-queue-checkpoint-end -->

<!-- init-six-calls-checkpoint-start -->
## 最新检查点：Mem已接入前五个真实初始化调用

`V293_OSInit_six_calls` 串联 Misc／Ready／TCB／Event／Flag／Mem：从实际 Mflag 构造两个新鲜局部块，入口无中间内存或freshness假设。同一Mf保有完整前缀、Mem及frame可写所有权；独立非零／Vundef有限入口读回208项，Mem6局部字节释放，caller同名变量保持7。详见[第55步](audit/STAGE55_INIT_SIX_CALLS.md)。

前瞻只删第六call，仍真实执行前五call；Mem字节／链头保持旧值，Flag／Ready／frame不变。四最终接口负控另计，不授内部机制独立消融信用。209源构建复用1035旧产物（非cold），93信任根／四模块coqchk、回归和清理见本步最终报告。仍是BeginHook后存在性无交错片段；手工前端，七函数fixture不是完整94P；非local Hoare、所有执行safety或完整OSInit。旧局部可能复用；旧失败保留、六门不晋级。GOOD_OS／同程序K1–K4开放，uCOS3未启动，未提交／推送。下方历史正文仅代表当时证据。
<!-- init-six-calls-checkpoint-end -->

<!-- init-mem-checkpoint-start -->
## 最新检查点：内存分区初始化的完整调用

`V293_OS_MemInit_call_return` 连接真实100字节清零、四次原生循环、五分区空闲链、尾NULL及链头，并分配/释放源码中两个局部的6字节。独立全255入口在同一Mf读回89项（5链接、80其余零字节、链头、3frame），caller同名变量仍为7。详见[第54步](audit/STAGE54_INIT_MEM.md)。

**尚未接到第五调用实际返回内存，不是完整OSInit。** 泛型接口仍要求callee freshness/NoDup/Away；手工前端、存在性无交错执行，非local Hoare或所有执行safety。两函数fixture不是完整94P。整call no-op消融与四最终接口负控分开记账；第一轮控制harness失败保留，第二轮独立前瞻计划纠正文本匹配。207源构建复用1025旧产物，非cold；92信任根/四模块coqchk、回归及清理见本步最终报告。旧失败保留，六门不晋级；GOOD_OS/同程序K1–K4开放，uCOS3未启动，未提交/推送。下方历史正文仅代表当时证据。
<!-- init-mem-checkpoint-end -->

<!-- init-five-calls-checkpoint-start -->
## 最新检查点：Flag 已接入前四个真实初始化调用

`V293_OSInit_five_calls` 串联 Misc／Ready／TCB／Event／Flag：从实际 Mevent 构造四个新鲜局部块；入口不假设中间内存或freshness。同一Mf保有全部前缀结果、Flag及frame可写所有权，独立非零／Vundef有限入口读回122项，Flag12局部字节释放，caller同名变量仍为7。详见[第53步](audit/STAGE53_INIT_FIVE_CALLS.md)。

前瞻只删第五call，仍真实执行前四call，Flag字节／链头保持旧值而Event／Ready／frame不变；只授整次调用消融信用。四项最终接口负控另计。205源构建复用1015旧产物，非冷构建；最终测试、85信任根／四模块coqchk和清理以本步final-report为准。仍是BeginHook后的存在性无交错片段，手工前端，六函数fixture不是完整94P；不是local Hoare、所有执行safety或完整OSInit。旧局部可能复用；旧失败保留、六门不晋级。GOOD_OS／同程序K1–K4开放，uCOS3未启动；未提交／推送。下方历史原文仅代表当时证据。
<!-- init-five-calls-checkpoint-end -->

<!-- init-flag-checkpoint-start -->
## 最新检查点：事件标志组完整清零、四次建链与调用生命周期

`V293_OS_FlagInit_call_return` 连接真实60字节清零、原生while四次迭代、5组Type／WaitList写入、尾NULL与空闲链头；完整分配／释放四局部的12字节并恢复caller。同一Mf保有全部字段、35其余零字节及frame可写所有权，独立全255入口读回49项，退出前ix=4，caller同名变量保持7。详见[第52步](audit/STAGE52_INIT_FLAG.md)。

**尚未接到第51步实际返回内存，不是完整OSInit、local Hoare或所有执行safety。** 入口显式要求四新鲜互异局部块及返回资源远离释放块；不是预置结果。Clang与Coq核对5×12字节、16位Flags及字段偏移，手工前端、非ABI证明。整次调用的前瞻no-op消融与四项最终读回负控分开记账，不授内部机制独立消融信用。203源构建复用1005旧产物（非coldbuild）；信任及回归以本步final-report为准。旧失败保留，六门不晋级；GOOD_OS／同程序K1–K4开放，uCOS3未启动，未提交／推送。下方历史原文仅代表当时证据。
<!-- init-flag-checkpoint-end -->

<!-- init-four-calls-checkpoint-start -->
## 最新检查点：四个真实初始化调用已接入同一轨迹

`V293_OSInit_four_calls` 串联 Misc／Ready／TCB／Event，事件旧资源作为frame穿过前三call；从实际TCB返回内存Mtcb构造四个fresh局部块，再真实调用事件初始化。入口无中间内存／freshness或预分配callee局部前提。同一Mf保有完整全局结果及frame的可写所有权，独立有限非零入口读回76项，事件12局部字节释放，caller同名变量保持7。详见[第51步](audit/STAGE51_INIT_FOUR_CALLS.md)。

只删除第四调用的前瞻单因素消融证明事件字节／链头仍旧，而ready／frame不变；这是整次调用消融，不是内部每个机制独立消融。四项最终接口负控另计。201源正式构建复用995旧产物，非source-only冷构建；完整测试及信任检查见本步最终报告。仍是BeginHook后的存在性无交错片段，不是local Hoare、所有执行safety或完整OSInit；旧ready／TCB局部可能被复用，不声称Mf仍缺失。手工语句分组前端，具体fixture仅五函数，不冒充完整94函数程序。旧失败保留，六门不晋级；GOOD_OS及同程序K1–K4仍开放，uCOS3未启动，未提交／推送。下方历史原文保留，只代表当时证据。
<!-- init-four-calls-checkpoint-end -->

<!-- init-event-list-checkpoint-start -->
## 最新检查点：事件初始化的完整清零、建链与调用生命周期

`V293_OS_InitEventList_call_return` 连接真实32字节 `OS_MemClr` 调用、原生while的一次迭代（两个16字节事件）、两次Type=unused写入、末尾NULL和空闲链头，并分配／释放四局部对象的全部12字节。独立全255字节入口及非空链头，在同一返回Mf证明30项读回（5项字段／链头、22项其余零字节、3项frame），非空同名caller变量保持7。详见[第50步](audit/STAGE50_INIT_EVENT_LIST.md)。

本步是单函数完整存在性无交错执行；**尚未接入第49步三call的返回内存**，不代表完整OSInit／OSStart、local Hoare或所有执行safety。入口显式要求四个fresh互异局部块及返回资源不在被释放块内，调用者还需提供准确函数绑定和全局环境；不是假设函数结果。手工前端，非已验证C转换。199源构建复用985旧产物，不是source-only冷构建；完整检查结果见本步最终报告。旧失败保留，六门不晋级；GOOD_OS和同程序K1–K4仍开放，uCOS3未启动，未提交／推送。下方历史原文保留，只代表当时证据。
<!-- init-event-list-checkpoint-end -->

<!-- init-chain-checkpoint-start -->
## 最新检查点：三个真实初始化调用已接成同一条内存轨迹

`V293_OSInit_three_calls` 连接 `OS_InitMisc → OS_InitRdyList → OS_InitTCBList`，不把中间内存或其fresh作为入口假设。局部块从前一步实际返回内存的上界构造；同一Mf返回全局结果及frame的可写所有权。独立非零／Vundef有限入口实例化固定十项Misc，在同一Mf证明49项读回，caller同名变量保持7。详见[第49步](audit/STAGE49_INIT_CHAIN.md)。

**片段位于尚无实现的OSInitHookBegin之后，不是完整OSInit入口可达性。** ready局部字节只保证在其返回Mrdy释放，后续分配可复用该块；TCB四局部10字节在Mf释放，不声称最终11字节都缺失。197源正式构建复用975旧产物（非source-only冷构建），64根／4模块coqchk及四项前瞻最终接口负控通过；全仓回归见最终报告，默认audit仍失败、旧失败保留、六门不晋级。完整OSInit／OSStart、任务／ISR、GOOD_OS和同程序K1–K4仍开放，uCOS3未启动，未提交／推送。下方历史检查点原文保留，只代表当时证据。
<!-- init-chain-checkpoint-end -->

<!-- init-tcb-call-checkpoint-start -->
## 最新检查点：TCB初始化的完整调用、四局部分配与释放

`V293_OS_InitTCBList_call_return` 从没有被调用函数局部存储的入口，执行四次真实分配、两次清零、建链及链头赋值，再释放全部10个局部字节并恢复caller。同一返回Mf保有全局结果和frame的可写所有权；独立非空同名caller入口读回33项，调用者变量仍为7，callee退出前计数为12。详见[第48步](audit/STAGE48_INIT_TCB_CALL.md)。

195源正式构建复用965旧产物（非source-only冷构建），58根／4模块coqchk及新增8项测试通过；全仓实际回归见第48步最终报告。四项前瞻单结论负控均按指定行拒绝，不是机制消融。入口仍明确要求新鲜／互异局部块、返回资源不在被释放块内及标识符排序约定；仅存在性执行，不是Hoare／所有交错safety。完整OSInit／OSStart、整核GOOD_OS和同程序K1–K4尚未完成，六门不晋级，uCOS3未启动；未提交／推送。下一步组合真实初始化路径。下方历史检查点保留原文，只代表当时证据。
<!-- init-tcb-call-checkpoint-end -->

<!-- init-tcb-list-checkpoint-start -->
## 最新检查点：TCB清零、原生空闲链循环及两个链头已纵向连接

`V293_OS_InitTCBList_body_execution` 将两次真实 `OS_MemClr` 的返回内存接入原生while，再执行末尾NULL和两个链头写入。同一Mf返回12条Next链接、第13项NULL、`OSTCBList=NULL`、`OSTCBFreeList=&OSTCBTbl[0]`，并保有676个其余TCB零字节、13个优先级NULL槽及frame的可写所有权。独立有限入口同时读回32项。详见[第47步](audit/STAGE47_INIT_TCB_LIST.md)。

193源正式构建复用955旧产物（非source-only冷构建），54根／4模块coqchk通过；4项前瞻单结论负控按指定行拒绝，不是机制消融。四个外围局部对象仍以已分配为入口；尚非完整函数调用／释放、OSInit／OSStart可达性或整核GOOD_OS／同程序K1–K4。全仓测试／默认audit仍非全绿，正式六门不晋级；uCOS3未启动，未提交／推送。下一步连接该函数外围生命周期，再推进真实启动组合。下方历史原文仅代表当时证据。
<!-- init-tcb-list-checkpoint-end -->

<!-- init-tcb-clear-checkpoint-start -->
## 最新检查点：TCB存储与13槽优先级表的真实连续清零

新增 `V293_OS_InitTCBList_cleared_tables`：真实数组地址／大小求值→两次实际OS_MemClr调用／分配／释放→同一Mf返回728个零字节、13个可写typed NULL槽及frame。第二次参数从真实M1构造新鲜，不借用入口M的新鲜性。独立有限非零／Vundef入口检查全部13槽、首末字节、保护值17／29及123。详见[第46步](audit/STAGE46_INIT_TCB_CLEAR.md)。

191源正式构建（复用945旧产物，非source-only冷构建）、50根／4模块coqchk和3项最终错误结论控制＋1项补充字节控制通过。189旧源、C、旧测试及旧证据未改；历史失败和诊断中断全部保留。全仓测试／默认audit仍非全绿，六门不晋级。仅两call前缀，不是TCBNext完整链、外围函数完整生命周期、OSInit／OSStart可达性、GOOD_OS或同程序K1–K4；uCOS3未启动，未提交／推送。下一步连接TCB空闲链及两个链头。下方历史原文只代表当时证据。
<!-- init-tcb-clear-checkpoint-end -->

<!-- mem-clear-call-checkpoint-start -->
## 最新检查点：清零函数的真实双参数调用与释放

新增 `V293_OS_MemClr_call_return`：实参求值→两个新鲜参数对象及真实store→原生循环→void／free→恢复caller。独立入口在同一返回Mf读回规范NULL、caller原指针／长度、两个保护字节及123，确认两个参数的全部6字节已释放；总程序实例排除不可满足入口。详见[第45步](audit/STAGE45_MEM_CLEAR_CALL.md)。

189源正式构建（复用940旧产物，非source-only冷构建）、47根／3模块coqchk及三项单因素错误结论控制通过。188旧源、固定C、旧测试及旧audit证据未改。旧失败与初次库名映射失败保留；默认audit仍非全绿、六门不晋级。仅无交错存在性轨迹，非完整TCB表／OSInit／OSStart、GOOD_OS或同程序K1–K4；uCOS3未启动，未提交／推送。下一步连接OS_InitTCBList两次实际调用与TCB空闲链。下方历史检查点保持原文，仅代表当时证据。
<!-- mem-clear-call-checkpoint-end -->

<!-- null-bytes-checkpoint-start -->
## 最新检查点：真实清零已连接规范空指针所有权

统一NULL为恰好4个零字节，新增 `V293_OS_MemClr_null_cell`：从任意4个旧字节（含Vundef）的可写存储执行原生循环，在同一Mf建立typed null所有权并读回；独立有限入口同时检查6项load。详见[第44步](audit/STAGE44_NULL_BYTES.md)、[表示决策](docs/adr/0006-清零与空指针采用唯一编码.md)。

原187源无旧产物隔离重建通过；正式188源构建与48根／3模块coqchk通过。5个旧文件中的526条定理陈述不变，另182旧活动源不变；固定C未改。模型语义有意变化，旧MNull不再解码为NULL；原始失败、反例、日志及935个旧产物归档保留，旧输入哈希不冒充当前证据。四项codec负控与一项实际错误读回负控各按自己的范围拒绝，不授下游安全信用。

**只是一个4字节指针槽，不是整张表、完整调用／生命周期或OSInit／OSStart可达性。** 全仓测试与默认audit仍非全绿，六门不晋级；GOOD_OS／同程序K1–K4／完整task与ISR仍开放，uCOS3未启动，未提交／推送。下一步接锁定OS_InitTCBList的两次清零与TCB链。下方历史检查点原样保留，其中“当前模型”等措辞只指当时的模型，不是本次新编码。
<!-- null-bytes-checkpoint-end -->

<!-- mem-clear-checkpoint-start -->
## 最新检查点：实际字节清零循环与指针零表示缺口

新增 `V293_OS_MemClr_loop_execution`／`V293_OS_MemClr_zero_size`：从实际可写参数和目标字节所有权执行原生 while，对长度0–65535证明全部字节置零、指针推进、计数归零及同环境 frame 保留；零长度不读取目的指针。独立有限非零／Vundef 三字节入口，在同一 Mf 读回7项，保护字节保持。详见[第43步](audit/STAGE43_MEM_CLEAR.md)。

**新反例已确认：当前模型四个零字节按指针 load 得到 Vundef，不是 Vnull。** 不能把字节清零冒充 TCB 指针表已初始化；本轮未改旧模型或 C。这里只是已分配参数上的无交错循环体执行，不含完整调用／释放、所有执行 safety 或 OSInit／OSStart 可达性。GOOD_OS／同程序 K1–K4／完整 task／ISR 仍开放，uCOS3未启动；默认 audit／旧失败保留，六门不晋级，未提交／推送，非全仓 source-only 构建。下一步先解决表示连接，再继续 TCB 与启动组合。旧缓存保留，lia 缓存自动更新单独报告。下方历史原样保留。
<!-- mem-clear-checkpoint-end -->

<!-- init-ready-checkpoint-start -->
## 最新检查点：实际就绪表两次循环、局部字节生命周期与启动前空指针

新增 `V293_OS_InitRdyList_execution`／`V293_OS_InitRdyList_call_return`：从原始可写全局单元推导实际 store，执行原生 while 的两次迭代；真实调用分配局部i、执行、释放并恢复 caller。独立有限非零／Vundef／非空指针入口，在同一返回 Mf 读回7个全局单元及123，确认局部已释放。详见[第42步](audit/STAGE42_INIT_READY.md)。

**仅无交错存在性执行轨迹，尚非完整 OSInit／OSStart 可达性或运行 Inv。** R 在 callee 环境保留到函数体退出，释放后仅保证局部块外字节不变，不任意搬到 caller。实际 OSTCBCur 被清为 Vnull，不能冒充已存在当前任务。GOOD_OS／同程序 K1–K4／全部 task／ISR safety 仍开放，uCOS3未启动；默认 audit 与旧失败保留，六门不晋级，未提交／推送，非全仓 source-only 构建。下一步接 TCB、任务／对象初始化，再组合 OSStart。下方历史原样保留。
<!-- init-ready-checkpoint-end -->

<!-- init-misc-checkpoint-start -->
## 最新检查点：真实 OS_InitMisc 的十次清零与具体调用／返回

新增 `V293_OS_InitMisc_execution`／`V293_OS_InitMisc_call_return`：从可写原始全局单元（允许 Vundef）推导实际 store，执行完整十次赋值，并通过真实空参数／空局部分配、void 返回恢复 caller；同一个 Mf 保留分离 frame。独立非零／未初始化入口与字面全10项读回详见[第41步](audit/STAGE41_INIT_MISC.md)。

**仅无交错执行，不是完整 OSInit／OSStart 可达性或运行 Inv。** 额外空指针只是未绑定 OSTCBCur 名称的 frame 示例，抽象时间仍57而物理时钟清零，尚未构造二者一致的启动 Inv。GOOD_OS、同程序 K1–K4、完整 task／ISR safety 仍开放，uCOS3未启动；默认 audit／历史失败保留、六门不晋级，未提交／推送，非全仓 source-only 构建。下一步接 OS_InitRdyList，再接实际任务／对象资源与 OSStart。下方历史原样保留。
<!-- init-misc-checkpoint-end -->

<!-- time-names-good-checkpoint-start -->
## 最新检查点：共享时间 GoodI 与真实 setter API 已使用同一 LocalInv

新增稳定接口 `V293_time_names_compatible`：同一个名称局部不变式、同一个共享时间 Inv、同一个调度器同时满足真正 GoodI 和 setter APIRule。新 GoodI 显式处理改变了的死任务局部资源归还分支，不把空 fixture 的旧结论直接替换类型。规范名称 LocalInv 的 GoodLInv／NoAbs／名称蕴含已证，独立字面联合接口同时包含 GoodI、实际 API、共享核心和非空 builder 入口。详见[第40步](audit/STAGE40_TIME_NAMES_GOOD.md)。

**名称 LocalInv 的物理／抽象 footprint 为空，不是完整任务资源 Inv；尚无真实初始化可达性。** API 仍 IE=true／清空 ISR；接口负控只授身份连接拒绝信用。GOOD_OS、同程序 K1–K4、完整 task／ISR safety 仍开放，uCOS3未启动。旧源／证据／失败保持、六门不晋级，未提交／推送；复用生产依赖而非全仓 source-only 构建。下一步从锁定 C 的 OSInit／全局资源构造连接同一套 Inv。下方历史原样保留。
<!-- time-names-good-checkpoint-end -->

<!-- time-set-api-checkpoint-start -->
## 最新检查点：OSTimeSet 接入真实 API 构造器与 APIRule

新增 `V293_TimeSet_api_contract`／`V293_TimeSet_api_rule`：对所有真实 builder 参数列表，把 `BuildPreA'` 接到原共享 setter 函数体，再把局部对象资源交给 `BuildRetA'`，构造真正 `APIRule`。全局名称来自局部不变式，调用者不持有共享时钟字节。独立字面实例证明实际 builder 结果、非空 GoodLInv／NoAbs、同份内存上的共享核心和 API 入口、非法输入拒绝；两项前瞻单因素负控及实际检查见[第39步](audit/STAGE39_TIME_SET_API.md)。

**依赖框架既有 call／return soundness，不是本轮新增完整具体分配／free trace；名称局部 Inv 对应的 GoodI 尚未连接。** IE=true／清空 ISR，非完整 task／ISR Inv／初始化；GOOD_OS 与同程序 K1–K4 仍开放，uCOS3 未启动。历史失败保留、六门不晋级，未提交／推送，复用生产依赖而非全仓 source-only 构建。下一步让 GoodI、API 和初始化使用同一个局部不变式。下方历史原样保留。
<!-- time-set-api-checkpoint-end -->

<!-- time-shared-set-checkpoint-start -->
## 最新检查点：OSTimeSet 同时连接物理写入和合法抽象时间更新

新增 `V293_OSTimeSet_shared_body`：对既有完整归一化 setter，保存单元清零→真实 encrit 取得共享时钟→实际赋值→框架 primitive 抽象更新 ostmid→重建同一共享 Inv→excrit→void return。入口没有时钟字节或成功 store oracle。独立字面入口检查旧7／参数42、局部资源与共享核心同时可满足，NoAbs 空局部 fixture 实际成立；反控及实际验证见[第38步](audit/STAGE38_TIME_SHARED_SET.md)与 final-report。

**仅 IE=true／所有 ISR 标志清零，要求 NoAbs li；局部存储已分配，不是完整 API 生命周期。** 退出后不声称全局时钟永久等于参数。初始化、完整任务／ISR Inv、GOOD_OS、同程序 K1–K4 仍开放，uCOS3 未启动；默认 audit／旧测试失败保留，六门不晋级，未提交／推送。复用生产依赖，非全仓 source-only 构建。下一步连接时间 API 的真实调用／分配／释放与规格。下方历史原样保留。
<!-- time-shared-set-checkpoint-end -->

<!-- time-shared-good-checkpoint-start -->
## 最新检查点：共享时间 Inv 的 GoodI 与真实任务指针切换

新增 `V293_time_shared_good`：对上一轮同一个 `V293_time_shared_inv` 完成四项 GoodI 义务，不借用旧 Inv 的结论。`V293_time_owned_switch` 从写权限推出实际 store 的存在，在同一个 Mf 检查新当前指针、四个抽象槽位和未变时钟，再关闭原 Inv。独立字面非空入口覆盖91→92及旧任务在／不在表，两个前瞻单因素错误读回结论被拒绝；详细实际验证和清理见[第37步](audit/STAGE37_TIME_SHARED_GOOD.md)及 final-report。

**GoodI 使用显式空 LocalInv fixture，不是完整任务资源生命周期；字面切换不声称92是最高就绪任务。** setter 抽象同步、初始化、所有 ISR safety、完整 API、GOOD_OS 与同程序 K1–K4 仍开放，uCOS3未启动。默认 audit 失败／六门不晋级、旧源／证据保持；复用依赖，非全仓 source-only 构建，未提交／推送。下一步连接临界区内 setter 的物理写入与 ostmid 同步更新。下方历史原样保留。
<!-- time-shared-good-checkpoint-end -->

<!-- time-shared-checkpoint-start -->
## 最新检查点：OSTimeGet 真正借用并归还共享时钟字节

新增 `V293_OSTimeGet_shared_body`：入口仅持有局部单元、名称绑定及 frame，不持有时钟字节；实际 encrit 从非空 IRQ Inv 取得时钟，读取到局部，再重建并 excrit 归还，最后返回本次快照。共享物理时间与抽象 ostmid 使用同一见证，precision／GoodInvAsrt／ISR 稳定性已证明。独立字面完整内存证明调用者与共享核心同时可满足，当前指针的两半权限来自真实分裂；调用者确实没有时钟块的字节。

**仅 IE=true／全部 ISR 活动标志清零的任务入口；新 Inv 的 GoodI、setter 抽象时间同步、嵌套入口、API 生命周期、初始化、GOOD_OS 与同程序 K1–K4 仍开放，uCOS3 未启动。** 不沿用旧 Inv 的 GoodI；不是所有 ISR safety。固定 C／原 getter AST 与旧证据保持，两项前瞻负控只授实际 ownership 连接拒绝信用。实际编译、coqchk、测试差分和清理见[第36步](audit/STAGE36_TIME_SHARED.md)及最终报告。默认 audit 失败、六门不晋级，未提交／推送；不是全仓 source-only 构建。下一步先证明扩展 GoodI 并连接 setter 抽象更新。下方历史原样保留。
<!-- time-shared-checkpoint-end -->

<!-- time-access-checkpoint-start -->
## 最新检查点：OSTimeGet／OSTimeSet 的真实归一化函数体 Hoare

新增两个稳定 body 接口：保存单元清零→真实临界区进入→从字节所有权推导读取／赋值→退出→快照返回或 void 返回；涵盖两种原 IE，并保留取得的 ISR 不变式。独立字面四块内存证明入口可满足，支持未初始化局部及真正 CurLINV。两项前瞻负控仅改错误返回值／旧时钟结论，所有 Proof 与 AST 保持；实际编译、coqchk、假设、测试诊断和清理见[第35步](audit/STAGE35_TIME_ACCESS.md)及最终报告。

**时钟当前仍是调用者拥有的资源，不是已经连接 IRQ 的共享时间不变式。** 手工宏映射不是原端口仿真；局部存储已分配，不是完整调用／释放／API 连接。CPU hook、共享 Inv／初始化／GOOD_OS 与同程序 K1–K4 仍开放，uCOS3 未启动。默认 audit 与历史测试失败保留，六门不晋级，未提交／推送；不是 source-only 全仓构建。下一步连接共享时间资源及函数生命周期。下方历史原样保留。
<!-- time-access-checkpoint-end -->

<!-- time-tick-lifecycle-checkpoint-start -->
## 最新检查点：OSTimeTick 的真实两局部分配、初始化与 void 释放返回

新增 `V293_tick_call_to_hook`：真实调用→空callee环境→两个新鲜局部对象→`cpu_sr=0`，在同一Mp检查ptcb仍为Vundef、保存值为0，并停在未删除的CPU hook及真实continuation。`V293_tick_suffix_void_lifecycle` 从hook返回边界连接既有完整后缀，在同一Ms归还任务／位图／时间／指针／保存单元和frame，再真实void return／释放两个对象／恢复caller。写权限由所有权推出，不假设store或free成功；不把任意R跨环境搬运。

独立六任务检查使用前缀产生的同一Mp；对任意时间、所有byte运行标志及两个IE成立，最终caller内存中逐字段读回字面预期任务／位图等，并检查两局部对象全部8字节缺失。两项前瞻单因素负控保持全部Proof：只改保存值0→1、只改已释放扫描字节仍存在，分别在读回／释放连接处拒绝，不授下游信用。实际编译、独立coqchk、假设、测试诊断和清理均见[第34步证据](audit/STAGE34_TIME_TICK_LIFECYCLE.md)及其final-report；全部既有174源／870依赖保留，新增登记后175源＝72目标＋103框架／tactics，未提交／推送。

**这是共享Mp的两个检查点，不是hook执行相连的完整函数。** CPU hook仍为`OPEN_BOUNDARY_CONTRACT`、无可执行体；cpu_sr初始化不等于原端口硬件token仿真。默认audit仍exit2（stale function evidence input identity），正式六门94／1／1／1／1／0不晋级；不是source-only全仓干净构建。所有ISR交错／共享Inv／初始化／GOOD_OS及同程序K1–K4仍开放，uCOS3未启动。下一步验证真实hook实现与契约，再接连续调用。见[已填生命周期表与中文讲解](docs/开发中/时钟中断如何跳过零延时任务.md#已继续两个局部变量的真实调用与释放)。下方历史原样保留。
<!-- time-tick-lifecycle-checkpoint-end -->

<!-- time-tick-storage-checkpoint-start -->
## 最新检查点：从真正未初始化的 ptcb 存储执行 OSTimeTick 后缀

新增稳定接口 `V293_tick_uninitialized_suffix_execution`，入口接受实际分配的原始 `Amapsto ... Vundef`，移除上一轮“扫描指针已初始化”的不必要要求；运行时由真实头赋值完成初始化，再接完整有限while；标志0／2不访问ptcb并保持Vundef。实际时间递增、最终指针／任务／位图及任意分离R连接同一Mf，恢复IE／控制栈。另证真实 `alloc`／`salloclv_step` 与同内存raw空间；分配frame明确在新环境求值，不偷换任意R的环境。

独立六任务入口先编码无扫描单元内存，证明块70新鲜后真实分配；显式证明Vundef不满足有效指针类型，且不同于Vnull。对任意32位时间、所有byte运行标志与两种IE成立；run1扫描到idle并检查最大时间回绕，run0／2保持未初始化扫描内容和任务／位图、时间仍递增。额外99／消息指针保持；不是初始化可达。

正式gate01八条实际命令符合预期，独立coqchk两模块通过；生产2根／probe6根仅既有classic／functional_extensionality_dep，无新增公理；新增10测试通过。两个预登记单因素错误结论仅改运行最终idle→链头／非运行Vundef→Vnull，所有Proof保持，均在FinalPointer连接拒绝，不给下游信用。全量1054测试366失败1错误：旧365诊断全部保留，新增2项是stage32冻结项目身份／精确append断言，不改旧tests／证据。默认audit仍exit2，六门94／1／1／1／1／0不晋级。

保持旧173源／865依赖，新登记后174源＝71目标＋103框架／tactics；保留5个新生产可复用产物。清理与清理后重核见本轮最终报告，旧缓存／源码／证据保留；未提交／推送，不是source-only全仓干净构建。**CPU hook仍为OPEN_BOUNDARY_CONTRACT；完整两个局部变量生命周期、cpu_sr初始化、hook／free／void return／caller恢复、所有ISR交错／共享Inv／初始化／GOOD_OS与同程序K1–K4仍开放，uCOS3未启动。** 下一步连接完整资源生命周期与真实hook契约。见[中文已填表与下一步](docs/开发中/时钟中断如何跳过零延时任务.md#已继续从真正未初始化的-ptcb-单元开始)、[第33步审计](audit/STAGE33_TIME_TICK_STORAGE.md)。历史正文原样保留。
<!-- time-tick-storage-checkpoint-end -->

<!-- time-tick-suffix-checkpoint-start -->
## 最新检查点：OSTimeTick 在 CPU hook 返回后的真实完整后缀

新增稳定接口 `V293_tick_post_hook_owned_execution`，把真实的临界区内时间递增、退出临界区、`OSRunning==1` 判断、链头赋值与整个有限任务链 while 接成同一次执行；同一 Mf 连接新时间／扫描指针读回及任务、位图、全局字段、任意分离 frame 的归还，恢复 IE／控制栈。时间允许32位回绕；入口没有执行、store成功或guard真值 oracle。`V293_tick_post_hook_exact` 保持原完整 AST 的 hook 调用，只用定义相等分解后缀，不冒充验证过的 C 前端。

独立编码入口初始扫描指针为idle而非链头；对所有byte运行标志、任意32位时间和初始IE给出执行与同内存字段读回。显式检查：运行标志1扫描且最大时间回绕到0，标志2不扫描但时间0→1，标志0不扫描但最大时间仍回绕。六任务混合链及额外99／消息指针保持按字面预期核查；不是初始化可达。

正式 gate01 八条实际命令达到预期，独立 coqchk 两模块通过，新增10测试通过。生产2根／probe5根只含既有classic／functional_extensionality_dep或闭合，无新增公理。两个预登记单因素错误结论保持全部Proof正文，在FinalTime／FinalPointer连接处拒绝，不给下游信用。旧1034测试仍364失败1错误：此前363项诊断全保留，新增2项为stage31冻结项目身份／精确append检查；不改旧测试或重绑证据。默认audit仍exit2，六门94／1／1／1／1／0不晋级。

**固定配置仍启用CPU的 `OSTimeTickHook`，其清单状态为 `OPEN_BOUNDARY_CONTRACT`、无可执行函数体，未删除或伪造空hook。** 本步只证明hook返回后的完整后缀，且局部扫描单元须已含有效指针；前缀／局部分配释放与返回、初始化、所有ISR交错／完整共享Inv、源码级GOOD_OS与同程序K1–K4仍开放，uCOS3未启动。旧172源／860既有依赖保持，新登记后173源＝70目标＋103框架／tactics；复用依赖，不是全仓source-only干净构建，未提交／推送。清理与清理后全量复核以本轮最终报告为准。下一步处理hook真实契约与函数资源生命周期。见[已补中文状态表与下一步讲解](docs/开发中/时钟中断如何跳过零延时任务.md#已继续连接-hook-返回后的完整后缀)、[本轮审计](audit/STAGE32_TIME_TICK_SUFFIX.md)。下方历史正文原样保留。
<!-- time-tick-suffix-checkpoint-end -->

<!-- time-tick-loop-checkpoint-start -->
## 最新检查点：真实 OSTimeTick 的有限任务链 while 执行

新增稳定接口 `V293_tick_while_owned_execution`，把0／未到期／到期三条真实循环体路径接成同一个有限 Next 链的实际 while：从字段所有权计算真实 Prio guard，逐轮传递实际内存与共享位图，在 idle 的 Prio12 处退出。同一 Mf 归还最终 idle 指针、全部所选节点字段、两行位图／group、idle 优先级和任意分离 R，恢复 IE／控制栈。入口没有执行／成功 store／guard 值 oracle；有限链和数值界仍须满足分离所有权。

独立六任务混合入口覆盖全部三条延时路径及四种到期状态，最终 group／row0／row1＝3／4／4；预期任务字段按字面写出并在同一 Mf 读回。初始 idle 没有 Dly／Next 字节，仍按真实 guard 退出；额外99与消息指针保持。具体入口可满足不等于初始化可达；扫描指针不是当前运行任务指针。

正式 gate01 七条实际命令符合预期，独立 coqchk 检查两个模块通过，新增9测试通过。生产4根／probe3根只含既有 classic／functional_extensionality_dep，无新增公理。两项预登记单因素负控保持全部 Proof 正文：错误最终指针在 readback 处拒绝；去掉非 idle 约束在 guard 连接处拒绝，不给下游信用。旧1025测试仍362失败1错误：此前361项诊断全部保留，新增2项为 stage30 冻结项目身份／精确 append 检查；不改旧测试或重绑证据。默认 audit 仍 exit2，六门94／1／1／1／1／0不晋级。

旧171源和855既有生产依赖保持，新登记后172源＝69目标＋103框架／tactics。复用依赖，不是当前 source-only 全仓干净构建；未提交或推送。**只构造存在的一条无 ISR 插入的完整 while 执行，不是所有中断交错下的 safety；完整函数前缀／局部分配释放与返回、初始化、完整共享 Inv、源码级 GOOD_OS 与同程序 K1–K4 仍开放，uCOS3未启动。** 下一步连接时间递增、hook 契约、OSRunning 判断和链头赋值，再接完整函数／ISR／共享 Inv。见[中文连续扫描表](docs/开发中/时钟中断如何跳过零延时任务.md#已继续把三个分支接成有限任务链的整个-while)、[本轮审计](audit/STAGE31_TIME_TICK_LOOP.md)。清理和清理后全量复核以本轮最终报告为准，下方历史正文原样保留。
<!-- time-tick-loop-checkpoint-end -->

<!-- time-tick-expiry-checkpoint-start -->
## 最新检查点：OSTimeTick 到期、等待结果与条件就绪位图的真实执行

新增 `V293_tick_expiry_iteration_owned_execution`：从Dly=1的真实写权限构造递减到0，重新读取Dly；按等待mask55清Stat／写独立StatPend，再重新读取Stat判断suspend，条件更新group／row，读取Next并推进局部ptcb，按真实loststep退出临界区。同一Mf连接执行、六项读回、十项字段及任意分离R的归还，IE／控制栈恢复。没有把成功store／执行当作入口。

具体入口独立构造，对全部256个Stat及两个初始IE成立；四个实际执行分支明确：无等待／无挂起→OK并置位，事件等待／无挂起→TIMEOUT并置位，无等待／挂起→OK且位图不变，事件等待／挂起→TIMEOUT且位图不变。另保持其他行、事件／消息指针及99。不是初始化可达或完整TCB／全局关系；设置位图也不是立即运行。

正式gate01七条实际命令达到预期，独立coqchk检查两模块通过；生产三根／probe四根仅既有classic／functional_extensionality_dep或闭合，新增9测试通过。两个预登记单因素错误结论均在最终readback证明处拒绝，整个主Proof后缀保持，downstream_credit=false。旧1016测试360失败1错误：上一轮359诊断全部保留，新增2项为stage29的冻结项目身份／精确append断言；不改旧测试或重绑证据。默认audit仍exit2，六门94／1／1／1／1／0不晋级。

旧170源、850既有依赖保持，新登记后171源＝68目标＋103框架／tactics。清理377项一次性文件／软链接与40目录（37实文件1691399字节），保留5个新生产可复用产物、源码及全部成功失败证据；未提交或推送。复用依赖，不是当前source-only全仓干净构建。**这里只补齐单次循环体到期路径；完整while／函数、初始化／完整Inv／GOOD_OS与同程序K1–K4仍开放，uCOS3未启动。** 下一步统一三条路径的链表循环不变量。见[中文表格与逐步讲解](docs/开发中/时钟中断如何跳过零延时任务.md#已继续dly1到期后是否进入就绪位图)、[本轮审计](audit/STAGE30_TIME_TICK_EXPIRY.md)。下方历史正文原样保留。
<!-- time-tick-expiry-checkpoint-end -->

<!-- time-tick-countdown-checkpoint-start -->
## 最新检查点：OSTimeTick 未到期递减的真实执行与同次资源返回

新增稳定接口覆盖 unsigned Dly=2至4294967295：构造Dly真实store得到M1，在M1重新判断未到期并读取Next，再写局部ptcb得到Mf；实际loststep循环体、Dly减一／最终指针readback、节点及任意分离R均连接同一Mf，IE／控制栈恢复。具体编码入口非空，对两个IE值成立，含非空控制栈、非零节点偏移、不同后继、Stat／Pend／位图／99保持，另检查两个端点的真实执行；不是初始化可达或完整TCB不变量。

正式gate02实际7命令达到预期，独立coqchk检查两模块通过；六根仅既有classic／functional_extensionality_dep或闭合，新增9测试通过。两个单因素负控拒绝，完整相关Proof保持，不给下游信用。gate01的新harness误判正常算术错误，失败与原runner快照保留；修正诊断匹配后完整重跑，不改旧门禁／白名单。旧1007测试358失败1错误，上一轮358诊断保留，新增1项为_CoqProject新登记后的旧stage28输入hash检查；默认audit仍2，六门94／1／1／1／1／0不晋级。

旧169活动源及845既有依赖保持，新登记后170源＝67目标＋103框架／tactics；清理534项一次性文件／软链接及57目录，实文件676441字节，保留5个新生产可复用产物、源码和证据。未提交／推送，没有当前source-only全仓干净构建。**Dly=1到期路径、完整函数／Inv／初始化／GOOD_OS及同程序K1–K4仍开放，uCOS3未启动。** 见[追加的中文讲解与表格](docs/开发中/时钟中断如何跳过零延时任务.md)、[本步审计](audit/STAGE29_TIME_TICK_COUNTDOWN.md)。下方历史正文原样保留。
<!-- time-tick-countdown-checkpoint-end -->

<!-- time-tick-zero-traversal-checkpoint-start -->
## 最新检查点：真实 OSTimeTick 零延时循环体的入口／执行／同次空间返回

新增完整配置后可执行语句模型，以及 `V293_tick_zero_iteration_owned_execution`：从局部指针写权限、Dly=0和Next字段所有权构造真实store，经loststep执行临界区内的零延时判断与Next赋值，在同一Mf中归还节点和任意不相交R，并恢复原IE／控制栈。字面入口独立构造，后继不同、偏移非零、控制栈非空；不把入口可满足当作初始化可达。

实际编译和独立coqchk通过；两个单因素错误版本被拒绝，整个相关Proof后缀保持，不给予下游信用。7根假设检查通过（仅既有classic／functional_extensionality_dep或闭合），新增9测试通过。原167生产／框架源不改；新增2模块登记后为169源。旧998测试357失败1错误，原347诊断保留，新增11项均为_CoqProject冻结身份／精确登记断言；不改旧证据。默认audit仍2，正式六门94／1／1／1／1／0不晋级，没有source-only全仓干净构建。

清理361项一次性材料／软链接及42目录，实文件531514字节；保留源、全部成功失败证据、835既有依赖及10个新生产可复用产物。未提交／推送。**只证明循环体的零延时分支，不是完整时钟函数或GOOD_OS；初始化、其他路径及同程序K1–K4仍开放，uCOS3未启动。** 下一步证明非零延时递减但尚未到期的真实路径。见[已填资源表与中文教程](docs/开发中/时钟中断如何跳过零延时任务.md)、[本轮审计](audit/STAGE28_TIME_TICK_TRAVERSAL.md)。下方历史正文原样保留。
<!-- time-tick-zero-traversal-checkpoint-end -->

<!-- physical-access-checkpoint-start -->
## 最新检查点：真实 C 资源清单与可满足的物理字段缺项反例

保持全部167生产／框架Coq源及C/config/port、旧门禁／测试／证据不变。新增直接访问清单覆盖固定配置94函数／12结构／1007语法访问点；重建源码及每个函数体身份均与冻结版本相符，不给予证明覆盖信用。

新增Coq空间反例：既有 `V293_shared_task_records` 可满足，但其中ready任务的Dly(44)、Next(20)、StatPend(49)字节可缺失，读取返回None。因此选定任务字段断言不足以替代完整TCB不变量。两个probe重编及新probe独立coqchk通过，5根假设仅classic／functional_extensionality_dep；不是初始化可达、tick执行、完整table-joint断言或GOOD_OS的反例，也不是全仓source-only构建。

新增16测试通过；旧982与全量998均346失败1错误，347诊断与上一检查点按kind／id重数完全相同，无新增历史失败。默认audit仍2（stale function evidence input identity）；正式六门94／1／1／1／1／0不晋级。10个一次性probe产物／318011字节经全体重核后清理，源、成功失败证据及既有缓存保留。

**整核GOOD_OS、初始化及同程序K1–K4仍未完成，uCOS3未启动。** 下一步沿真实 `OSTimeTick` 补齐链表、每任务延时／等待结果、时间与位图资源及关系，连接入口／执行／返回，而不是重命名为“全局正确”。见[已填TCB表格与逐步教程](docs/开发中/从真实C访问集合补齐物理不变量.md)、[本步审计](audit/STAGE27_PHYSICAL_ACCESS.md)。下方历史正文原样保留。
<!-- physical-access-checkpoint-end -->

<!-- table-joint-return-checkpoint-start -->
## 最新局部检查点：整张优先级表与指针、任务、位图在同一次返回中联合归还

`V293TaskRecordOwnership.v` 原2505行逐字保持，追加420行至2925行／188211字节；SHA256 `8368f6b6099841d30eef1df0c6ef491c758ec4ceb5e75a2a663aafe086dd1394`。其他166活动源、12保护输入、9439历史文件与HEAD保持，仍167源；不改C/config/port/framework、旧测试／门禁／证据、白名单和正式覆盖，未提交。

新根 `V293_critical_wait_table_joint_owned_execution` 在旧联合入口上增加真实52字节完整写权限及全部指针值合法性。只调用一次真实bitmap-return执行，在同一Mf联合归还当前指针读半份额、任务表中各任务的选定字段、六个位图字节、更新后的13槽整表及抽象shared_fields。表从实际联合片段的剩余内存分离，不能拼接两份独立最终内存；shared_fields不是完整物理Inv。任意R不承诺跨local free保持。

字面入口目标8→6但仍等待SEM，另一任务ready／优先级4；旧槽8清空、新槽6更新、槽4不变。逐槽store可保持其他联合资源，但不声称任意写后仍满足语义不变量。当前指针仍半份额，不据此取得切换写权限。开发中的参数推断、类型别名匹配失败及最小化诊断全部保留。

gate01因deprecated引理警告被原严格假设解析器拒绝，24项执行／负控结果与预期一致但尚未进入coqchk；完整失败记录保留。仅将新probe中等价除法界证明改用lia消除警告，不改解析器或白名单。正式gate02完整重跑，实际27项符合预期，202冻结输入保持；19旧fixture、生产／整源Positive／新probe重编通过；两项单因素负控拒绝，三个模块各自coqchk通过，6+6根仅classic、functional_extensionality_dep。指针条件在执行前中和为True以保留intros参数个数，拒绝定位在支持辅助根；旧表负控只改最终联合表。整个目标Proof后缀保持，downstream_credit=false，不给所有下游机制信用。

新增6测试通过；旧976与全量982、清理后982均346失败1错误，347诊断按kind／test重数一致。原344诊断保留，新增3项旧priority-table输入身份／生产绑定／负控整源快照诊断；不能把全部347项叫作快照问题。默认audit仍2（stale function evidence input identity）；正式六门94／1／1／1／1／0不晋级，没有当前身份source-only全仓干净构建。

清理前逐项记录并全体重核124个一次性文件／12904278字节；835既有缓存路径保留，830无关产物哈希不变，5生产产物绑定本次实际coqc／coqchk。保留源、所有成功失败日志与快照；门禁隔离树另按manifest清理。

**本步只闭合选定等待分支的同次联合返回；完整Inv、初始化、正常无锁调度、其他API／ISR、GOOD_OS与同程序K1–K4仍未闭合，uCOS3尚未启动。** 下一步按真实函数读写集合核对完整物理不变量的缺项，再继续入口／执行／返回连接。见[中文教程与已填表格](docs/开发中/整张优先级表如何与任务位图同次归还.md)、[本轮审计](audit/STAGE26_TABLE_JOINT_RETURN.md)。下方旧正文逐字保留原身份。
<!-- table-joint-return-checkpoint-end -->

<!-- priority-table-ownership-checkpoint-start -->
## 最新局部检查点：完整优先级表入口所有权与两次真实写入保持

`V293TaskRecordOwnership.v` 原2212行逐字保持，追加293行至2505行／159232字节；SHA256 `4fa7487a69950b0864d1941abc34297aa8476309b99587ff284df7c9e003e63d`。其他166活动源、12保护输入、9291历史文件及HEAD保持，仍167源。未改C/config/port/framework、旧测试／门禁／证据、白名单和正式覆盖，未提交。

新增整表入口根从真实52字节完整权限、13槽loads及显式指针类型Forall构造分离所有权；two-store根使用输入的真实M1／M2，在同一M2归还更新后的13槽及任意R。R只跨这两次store，不承诺跨local free；逻辑片段分离不是额外程序free。字面表验证先清p8再写p6、p4不变、旧表被排除；半份额表可读不可写，稀疏两槽不等于完整表。独立表probe不证明任务状态或初始化可达。

正式gate01实际26项符合预期，201冻结输入保持；18旧fixture、生产／整源Positive／新probe重编，两项单因素负控拒绝，三个模块各自coqchk通过。6+6根假设仅classic、functional_extensionality_dep，整个目标Proof后缀保持，downstream_credit=false。原前瞻完整API联合返回主题仍开放；控制只针对本轮构造器和two-store根，不给下游机制信用。

新增6项测试全通过；旧970与全量976项均343失败1错误，344诊断按kind／test重数相同。原340诊断保留，新增3项旧joint-return身份／快照及1项跨Qed计数诊断；未改旧断言或重绑证据，不能将全部344项统称为快照问题。范围／冻结C只读通过；默认audit仍2（stale function evidence input identity），正式六门94／1／1／1／1／0不晋级，没有当前身份source-only全仓干净构建。

113项一次性材料／probe产物按完整manifest全体重核后清理；835既有缓存路径保留，830无关产物哈希不变，5生产产物绑定本次实际coqc／coqchk新身份。源及全部成功失败证据保留，gate临时树12项另行按manifest清理。

**尚未将整表与当前指针／任务／位图在API同一次返回中联合归还，完整Inv、正常调度、其他API／ISR及初始化也未闭合；整核GOOD_OS与同程序K1–K4未完成，uCOS3未启动。** 下一步连接同一Mf中的联合资源，而不是拼接独立存在量词。见[中文教程与已填表格](docs/开发中/为什么两个优先级槽可写还不等于整表可写.md)、[本轮审计](audit/STAGE26_PRIORITY_TABLE_OWNERSHIP.md)。下方旧正文逐字保留原身份。
<!-- priority-table-ownership-checkpoint-end -->

<!-- joint-return-checkpoint-start -->
## 最新局部检查点：同次返回联合归还指针、任务字段与位图

`V293TaskRecordOwnership.v` 原1861行逐字保持，追加351行至2212行／144244字节；SHA256 `93b194a1496dde4c6d640f0d9e827aa3f14871873397f56a19d8df1c1de0de57`。其他166活动源、12项保护输入、9118历史文件与HEAD保持；仍167源，未提交，不改C/config/port/framework、旧测试／门禁／证据或正式覆盖。

新根 `V293_critical_wait_joint_owned_execution` 保持旧入口契约，只调用一次真实bitmap-return执行。在其同一Mf／Os'／OO'联合归还 `(((CurTid ** all_selected_task_fields) ** six_bitmap_bytes) ** shared_fields) ** Atrue`。从实际片段的剩余内存分离位图权限，不拼接独立弱后置条件，不从load反推权限。五store模型不是第二次API执行；CurTid仍只读半份额，不保任意R跨local free。

字面入口目标8→6但仍等待SEM，另一任务ready且优先级4，current仍60；ready16/0不变，event0/1→64/0，run／ISR／lock为1/1/0。七个probe根包含一次位图store后保留整份联合空间资源；不等于任意写保持完整Inv，也不代表正常无锁调度或初始化可达。

gate01行号判定错误的失败记录完整保留；只修正负控自身Proof行号计算后，gate02完整重跑25项符合预期，200冻结输入保持。生产／整源Positive／新probe及17旧fixture重编通过，两项单因素负控拒绝，三个模块各自coqchk通过；4+7根假设仅classic、functional_extensionality_dep。整个目标Proof后缀保持，downstream_credit=false，旧白名单未改。

新增6项测试通过；旧964与全量970项均339失败1错误，340诊断按kind／test重数相同。原335诊断保留，新增3项旧bitmap源身份／快照和2项跨Qed计数诊断，不改旧测试或重绑旧证据。候选新测试的两项失败也保留，并记录生产重编产物与既有缓存身份的边界修正。

范围／冻结C只读／diff通过；默认audit仍2：stale function evidence input identity，正式六门94／1／1／1／1／0不晋级。没有当前身份source-only全仓干净构建。120项一次性开发材料／probe产物按完整manifest全体重核后清理；835既有缓存路径保留，其中830个无关产物哈希不变，5个生产产物绑定本次coqc／coqchk新身份。全部源与成功失败证据保留，两次gate临时树各12项另按manifest清理。

**完整priority table所有权、其余共享Inv、正常调度、其他API／ISR和初始化仍未闭合；整核GOOD_OS与同程序K1–K4未完成，uC/OS-III未启动。** 下一步先取得完整priority table的真实入口空间资源并连接实际执行保持。见[中文入门与已填表格](docs/开发中/一次返回如何联合指针任务和位图.md)、[本轮审计](audit/STAGE26_JOINT_RETURN.md)。下方旧正文逐字保留原身份。
<!-- joint-return-checkpoint-end -->

<!-- bitmap-permissions-checkpoint-start -->
## 最新局部检查点：同次成功返回的位图联合资源与完整权限

`V293TaskRecordOwnership.v` 原1528行逐字保持，追加333行至1861行／119,434字节；SHA256 `fafb787168450426e1f6039ac1649edd362d1bb1179ffeb780da82ee459a7060`。其他166活动源、12项保护输入、8914个历史文件和HEAD保持；仍167源，未提交，不改C/config/port/framework、旧测试／门禁／证据或正式覆盖。

新根 `V293_critical_event_return_bitmap_owned` 的入口契约与旧执行根相同，只调用一次实际update execution和一次tail return；在同一Mf归还非local完整权限保持及ready/event六字节联合空间资源，保留原执行／loads／frames／free结论。完整权限来自真实入口与执行保持，不从load反推；NoDup列表逐个分离真实singleton，不拼接独立的cell ** Atrue。被free的local不在permission保持范围内。

新字面入口仍是目标8→6但等待SEM，另一任务ready／优先级4，ready16/0不变、event0/1→64/0，run／ISR／lock为1/1/0。六个probe根验证同次返回、六字节实际可写、两个四字节priority槽分别可store、旧event被排除、半份额可读不可写、已释放local不可写。两个槽的store存在量词不代表顺序执行或任意写保持Inv；未取得完整priority table空间所有权。

gate01实际8项符合预期、199个冻结输入保持：生产／隔离整源Positive／新Probe coqc通过，两项单因素负控拒绝，三个模块各自coqchk通过。4+6根假设仅classic、functional_extensionality_dep；整个目标Proof后缀保持，downstream_credit=false，旧白名单未改。16个旧fixture实际重编通过；新增6项测试通过。旧958项与全量964项均334失败1错误，335诊断按重数相同；相较上一轮新增3项旧current-all源／生产快照／负控快照身份诊断，旧332诊断全部保留，不将其统称为快照问题，不重绑旧证据。

范围／冻结C只读／diff通过；默认audit仍2：stale function evidence input identity。正式六门94／1／1／1／1／0保持。增量make build退出0，仅COQDEP／nothing-to-be-done，无当前身份source-only全仓干净构建。116项本轮一次性材料按完整manifest整体核对后清理；835个既有缓存路径、生产依赖、源和全部成功失败证据保留。

**尚未把位图与上一轮CurTid／全部任务字段在一个执行根里联合归还；不能把两个独立exists Mf直接拼起来。整核GOOD_OS与同程序K1–K4仍未完成，uC/OS-III未启动。** 下一步联合这些空间资源与priority table，再推进正常调度、其他API／ISR及初始化。见[中文入门与已填表格](docs/开发中/位图可读为何还不等于返回后可写.md)、[本轮审计](audit/STAGE26_BITMAP_PERMISSIONS.md)。下方旧正文逐字保留原身份。
<!-- bitmap-permissions-checkpoint-end -->

<!-- current-all-ownership-checkpoint-start -->
## 最新局部检查点：同次成功返回的当前指针与全部任务字段联合资源

`V293TaskRecordOwnership.v` 原1235行逐字保持，追加293行至1528行／97,023字节；SHA256 `7070546811cd77db6750c73c39f38ed0054c3bbdd335cce7064d35d0a4bab3f5`。其他166活动源、12项保护输入、8813个历史文件与HEAD保持；仍167源。不改C/config/port/framework、旧测试／门禁／证据或正式覆盖，未提交。

新稳定根 `V293_critical_wait_current_all_owned_execution` 只调用一次旧全任务成功执行根，在同一Mf／Os'／OO'归还 `((CurTid current ** all_records updated_tasks) ** shared_fields updated_tasks) ** Atrue`。整体搬运入口联合片段，不从两个独立弱后置条件或load重构权限。CurTid仍是框架定义的只读半份额。非目标任务块和非目标current块必须避开实际写／free集合；current块等于目标TCB块时用整块精确frame处理，没有额外块互异要求，不保任意R跨free。

新字面入口真正组合current块80半份额与任务41／60的选定字段，不复用旧完成执行trace。同次返回后current仍60，目标8→6但仍等待SEM，另一任务仍ready／优先级4；从同一终态可读current并分别实际store两任务字段，另排除错误current和旧规范任务表。run／ISR／lock仍1/1/0；不是正常无锁切换或完整Inv。

gate01实际8项符合预期，198个冻结输入保持：生产／隔离整源Positive／新Probe编译通过，两个单因素负控拒绝，三个模块各自coqchk通过。4+5根假设仅classic、functional_extensionality_dep，旧白名单未改，整个目标Proof后缀保持，负控downstream_credit=false。15个旧fixture实际重编通过，新增6项测试通过；旧952与全量958项均331失败1错误，332诊断按重数相同。相较上一轮增加4项旧all-task身份／快照及跨Qed计数断言诊断，旧328项保留，未删改旧测试或绑定旧证据。

范围／只读冻结C／diff通过，默认audit仍2：stale function evidence input identity；正式六门94／1／1／1／1／0不晋级。增量make build退出0但仅COQDEP／nothing-to-be-done，没有当前身份source-only全仓干净构建。87项一次性材料按完整manifest重核后已清理，835个既有缓存路径、生产依赖、源及全部成功失败证据保留；最终复核见[本轮审计](audit/STAGE26_CURRENT_ALL_OWNERSHIP.md)。

**整核GOOD_OS与同程序K1–K4仍未完成，uC/OS-III未启动。** 下一步联合ready位图／priority table／event真实空间资源，再推进正常调度、其他API／ISR和初始化。见[中文入门与已填表格](docs/开发中/当前任务和全部任务字段为何要一起归还.md)。下方旧正文逐字保留原身份。
<!-- current-all-ownership-checkpoint-end -->

<!-- all-task-ownership-checkpoint-start -->
## 最新局部检查点：同次成功返回的全部任务字段所有权

`V293TaskRecordOwnership.v` 原899行逐字保持，追加336行至1235行；当前SHA256 `2085d67814b7e720cee8c02873f4184feb63b1944700e562c5fbb22ba011441a`。其他166活动源、12项受保护输入、8746个历史audit/scripts/tests身份及HEAD保持；仍167源，未提交，不改C/config/port/framework或旧测试／门禁／证据，不晋级正式覆盖。

新稳定根 `V293_critical_wait_all_records_owned_execution` 只执行一次既有真实成功更新与返回，在同一Mf／Os'／OO'归还实际更新任务表规范枚举的全部选定字段资源，并联合更新后的shared_fields。完整空间列表作为一个片段搬到最终内存，不从load或若干独立record**Atrue拼出所有权。非目标任务块须避开实际写／free集合；不增加任务块互异前提，不承诺任意R跨local free保持。CurTid／全部位图／event的联合空间Inv仍未完成。

字面入口重新合并目标(41,8)等待任务与(60,0)ready任务的真实资源；同次返回后目标8→6但仍等待，另一任务仍ready／优先级4，两者仍可写；旧规范表所有权另被终态定理排除。run／ISR／lock仍1/1/0，仅受阻调度成功更新／返回，不是所有API分支、正常无锁调度或初始化可达性。

gate01实际8项符合预期：Production／隔离整源Positive／新Probe coqc通过，两项单因素负控拒绝，三个独立coqchk通过；197个冻结输入保持，4+4个根假设仅classic与functional_extensionality_dep。两个控制保持整个目标Proof后缀，downstream_credit=false，不从提前拒绝授下游信用。14个旧fixture重编通过。新增6项测试通过；全量952项仍327失败1错误，328个诊断与同轮旧946项按重数相同。相较上轮新增3项旧API-ownership身份／快照诊断，旧325项全保留，未弱化旧门禁或重绑历史证据。

范围／只读冻结源码／diff通过；默认audit仍2：stale function evidence input identity，正式六门94／1／1／1／1／0保持。增量make build退出0；没有当前SHA的source-only全量干净构建。75个本轮一次性Coq产物（9,262,776字节）按整个预先确认manifest清理；835个既有缓存路径、生产可复用依赖及全部源／成功失败证据保留，gate临时树12项另按manifest清理。

**整核GOOD_OS与同程序K1–K4未完成，uC/OS-III未启动。** 下一步联合当前任务指针、全任务字段与位图／event资源，再推进正常调度、所有API／ISR及初始化。见[中文入门与已填表格](docs/开发中/一次返回如何归还全部任务字段.md)、[本轮审计](audit/STAGE26_ALL_TASK_OWNERSHIP.md)。下方旧正文保留原身份。
<!-- all-task-ownership-checkpoint-end -->

# 验证进度

<!-- api-task-ownership-checkpoint-start -->
## 最新局部检查点：同次成功返回的目标字段写权限与抽象任务表更新

`V293TaskRecordOwnership.v` 原422行逐字保持，追加477行至899行，SHA256 `c019819f51fda2b656b8a422d82fd54bcb0c1d629be632b18a7b6c2074002dd2`。其他166活动源、12项受保护输入、8547个既有audit/scripts/tests文件与HEAD保持；仍167源，未提交，不改C/config/port/framework、旧测试／门禁／报告或正式覆盖。

稳定根 `V293_critical_wait_record_owned_execution` 在同一真实成功更新与尾部返回的Mf／Os'／OO'上组合：实际执行、spec_step、新优先级目标字段完整写权限、实际抽象任务表更新，以及ready／priority table／event位图对应。权限来自入口真实资源，不是从load反推；整个TCB块字节／权限frame连接五赋值中间内存与最终返回内存。只归还选定记录与shared_fields，**不声称任意R跨local free保持、所有任务记录／CurTid已联合保持或完整共享Inv已证**。

字面入口重新构造(41,8)从8→6、同一SEM等待(72,5)、delay1、非NULL消息(120,7)，另实际安装ready任务(60,0)优先级4，不复用旧完成trace。同次返回后目标仍等待，ready16/0不变、event0/1→64/0，返回0、caller恢复、locals释放。另在同次终态条件下排除旧8所有权、证明实际可写；半权限可读不可写反例保留。run／ISR／lock仍1/1/0，只覆盖受阻调度及成功更新／返回，不含完整外部调用／所有入口分支或初始化可达性。

gate01实际退出0，8项符合预期：3次coqc、两项预期负控拒绝、3次独立coqchk（生产208.12／probe222.20／Positive209.63秒）。196个不同冻结输入保持；4个正控根和5个probe根假设并集仅classic与functional_extensionality_dep，白名单未改。隔离正控整源重证，不导入候选模块。DroppedPermissionFrame只将精确get块frame改为typed-load相等，680行Proof／690行拒绝；StaleReturnedPriority只改最终new→old，853行Proof／897行拒绝。整个目标Proof后缀保持，均downstream_credit=false；不从早拒绝授下游信用。13个未改fixture重编通过，全部开发失败／人工中断和最终快照保留。

新增6项测试通过；最终身份旧940项和全量946项均324失败1错误，325个诊断按重数相同。较前轮322诊断新增3项旧task-owned-update源SHA／生产及负控快照过期检查，逐条核对trace；旧诊断与旧证据全部保留。范围审计、冻结源码只读重验及diff通过。默认audit仍2：stale function evidence input identity；正式六门94／1／1／1／1／0不晋级。

增量make退出0，仅COQDEP／nothing-to-be-done。没有当前身份source-only全量干净构建；旧167源干净构建不能套用本轮新SHA。70个本轮工作树一次性Coq产物（8,454,751字节）在首次删除前整体逐项确认、全部验证结束后重核并清理；835个既有Coq缓存路径及生产可复用依赖保留。gate临时树12项另按完整manifest清理，全部源与成功／失败证据保留。

**整核GOOD_OS与同程序K1–K4未完成，uC/OS-III未启动。** 下一步统一选定资源与全部任务／当前任务／位图和event的共享不变量，再推进正常无锁调度、所有API／ISR及初始化。见[中文教程与已填表格](docs/开发中/成功返回后仍然拥有TCB字段.md)、[本轮审计](audit/STAGE26_API_TASK_OWNERSHIP.md)。下方旧检查点保留其历史身份。
<!-- api-task-ownership-checkpoint-end -->


<!-- task-owned-update-checkpoint-start -->
## 最新局部检查点：同一次真实五赋值的字段所有权更新与frame保持

在 `V293TaskRecordOwnership.v` 原227行逐字前缀后追加195行，现422行，SHA256 `a576182aefb5da1b35475c51cc1453dd66db71368329ce6a5a378333b0a1053d`。其余166活动源、12个受保护输入（含_CoqProject）、8426个既有audit/scripts/tests文件及HEAD保持，未提交。仍167源；不改C/config/port/framework或旧测试／门禁／报告，不晋级正式覆盖。

一般字段写入根使用真实完整Amapsto／join和标准store_mapstoval_frame1，返回实际store所得内存的新字段所有权与原物理／抽象frame。列表选择保留前缀／后缀；任务根按50／52／51／54／53更新五字段，可写权限由入口推出。`V293_task_prio_tcb_owned_execution`仅调用一次旧五赋值执行根，保留全部旧输出，并在同一明确M'追加新所有权与任意R。没有连接完整调用／返回、抽象任务表更新、全局Inv或全部共享资源。

字面probe183行，重新构造目标(41,8)从8→6的全部入口：同一SEM等待(72,5)、delay1、message(120,7)、pend0保持；非空frame含另一ready任务(60,0)、优先级4、NULL和完整指针／操作数locals。同一次终态另证目标优先级6、其他任务4与操作数6，并排除旧优先级8所有权。抽象域为空，不授事件相容、完整合法内核入口或初始化可达性信用。

gate01退出0，9项实际检查符合预期：4次coqc（生产、隔离整源Positive、未改旧fixture、新probe）、两项预期负控拒绝、3次独立coqchk（207.49／214.66／204.29秒）。184个不同冻结输入保持。4个正控根与7个probe根假设并集仅classic和functional_extensionality_dep。StaleCellValue只改字段出口为old，240行Proof开始／254行拒绝；StaleTaskPriority只改任务出口为旧priority，322行Proof开始／384行拒绝。全部目标Proof后缀保持，均downstream_credit=false，不从早拒绝授下游信用；独立同次终态反例另证。所有开发失败快照与日志保留，白名单未改。

新增6项测试通过；全量940项／321失败1错误，322个诊断与同轮旧934项按重数相同。前轮320个诊断全部保留，仅增两项旧ownership生产SHA／快照差异，逐条trace核对，不重绑旧证据。范围审计、冻结源码只读重验与diff通过；默认audit仍2：stale function evidence input identity，正式六门94／1／1／1／1／0保持。

增量make退出0，仅COQDEP／nothing-to-be-done。没有本轮身份source-only全量干净构建；上一轮167源成功构建只属于旧所有权SHA651b1d1c...。本轮编译实际变更源，并独立coqchk其依赖闭包，不能冒充全仓验收通过。

工作树11个一次性文件（509,797字节）已在第一次删除前逐项确认整个集合后清理：10个probe Coq产物及1个未用临时查看副本。903个既有缓存路径保留。修改前已明确将新CriticalReturn／所有权模块10个Coq产物视为后续可复用依赖并保留，避免每轮重建重型依赖。门禁临时树12文件另按manifest核对清理。源文件、依赖、用户数据及全部成功／失败证据保留。

下一步将所有权接回已有完整API执行，再联合物理TCB、抽象任务表、位图与event的共享相容关系；后续仍需初始化、所有API／ISR、正常无锁调度、源码级GOOD_OS及同程序K1–K4。阶段一未完成，uC/OS-III未启动。见[中文教程与已填表格](docs/开发中/写入TCB后如何归还资源.md)、[审计](audit/STAGE26_TASK_OWNED_UPDATE.md)及audit/logs/stage26-task-owned-update/。
<!-- task-owned-update-checkpoint-end -->

<!-- task-ownership-checkpoint-start -->
## 最新局部检查点：任务字段空间写权限与当前167源干净构建

新增227行 `V293TaskRecordOwnership.v`，使用实际完整Amapsto／分离合取和 `TcbMod.lst` 规范枚举；一般定理从全部任务字段所有权推出旧全称读数关系，再连接同一物理内存和实际抽象任务表槽位。双任务空间实例与单字节半权限“能读、不能写、不具完整所有权”反例通过Coq。不是完整TCB／共享Inv，也未证明同一次真实API执行上的所有权保持；具体例子使用空ECB表，不能推出事件／任务相容或初始化可达。

原166活动源（含7773行CriticalReturn）全部逐字保持，现167源；_CoqProject仅在原字节前缀后登记新模块，其余11个受保护输入、8274个既有audit/scripts/tests文件与HEAD保持，未提交。不能宣称12个受保护输入全部不变。不改C/config/port/framework或旧测试／门禁／报告，不晋级正式覆盖。

gate02退出0，8项实际检查符合预期：3次coqc、两项预期负控拒绝、3次独立coqchk。184个不同冻结输入保持，4个正控根与8个probe根的假设并集仅classic与functional_extensionality_dep。两项单因素控制固定全部lemma声明及Proof后缀，均downstream_credit=false；不能由早拒绝授下游或API保持信用。gate01的未限定classic假设输出导致的严格检查失败原样保留；仅删除probe未用导入后重跑，白名单／检查器未改。

**当前身份source-only隔离干净构建实际通过。** 170个输入（167源＋3构建文件）逐一核对；入口无旧Coq产物，默认make build、Coq8.18.0、JOBS2，1032.53秒，退出0，生成167个vo，输入保持。该构建不等于GOOD_OS或正式函数证据刷新；增量make单独仅COQDEP。默认audit仍2：stale function evidence input identity，正式六门94／1／1／1／1／0不变。

新增8项测试通过；全量934项／319失败1错误，320个诊断与同轮旧926项按重数一致。上一轮310个诊断全保留，新增6项_CoqProject SHA和4项活动源集合旧快照差异，逐条trace核对；不把其他历史失败统称快照问题。工作树15个一次性Coq产物（9,847,254字节）清理前逐项确认整个集合及保留源／快照；903个基线缓存路径保留，不声称缓存字节不变。门禁／干净构建临时树按各自清单另行清理。

下一步是实际API执行上的资源更新归还与全局相容关系，之后仍需初始化、全部API／ISR、源码级GOOD_OS及同程序K1–K4；阶段一未完成，uC/OS-III未启动。见[审计](audit/STAGE26_TASK_OWNERSHIP.md)、[中文教程](docs/开发中/读到TCB字段不等于拥有写权限.md)及 `audit/logs/stage26-task-ownership/`。
<!-- task-ownership-checkpoint-end -->

<!-- task-records-checkpoint-start -->
## 最新局部检查点：同一次完整返回的全称任务字段对应

`V293CriticalReturn.v` 保留原7530行逐字前缀，追加243行，现7773行／517,619字节，SHA256 `4aad6f83db4904514bee4f7b4eab7e149df24679faf46a6fe58497d0eaa7d1ee`。仍166活动源；其余165源、12个受保护输入、8058个既有audit/scripts/tests文件及HEAD按基线保持，未提交。不改冻结C/config/port/framework、旧测试／门禁／报告或正式覆盖。

新 `V293_task_records` 对抽象表每个成员要求优先级／行列／掩码及按ready／timewait／IPC区分的状态、消息、延时和事件对应。一般根 `V293_critical_event_task_records_execution` 保留旧接口全部前提与输出，另外要求入口全称关系和其他任务块不在写集合或locals释放集合；只调用一次旧完整执行根，目标用实际写入，其他成员用该次完整块frame，得到同一Mf／Os'／OO'上的新任务表对应。不是完整TCB所有权、链表／分配器不变量或fullreadyinv，也不覆盖同block多个TCB的布局。

新字面输入真实安装current `(60,0)` 的选定物理字段，重新构造指针权限和所有入口，不复用旧完成trace。目标 `(41,8)` 从8→6仍等待同一SEM，delay1、非空消息、等待结果0保持；current优先级4、ready、NULL保持，ready16/0、事件0/1→64/0、SEM类型3／计数0／NULL保持，返回0、caller恢复及locals释放。现有CurTid／共享字段空间组合与全部任务字段同属一个终态。独立语义定理证明旧输入缺失current记录，并在同一次新执行上排除过期任务表。run／ISR／lock仍1/1/0，实际调度受阻，不授正常无锁切换信用。

实际配置后函数SHA仍c29b633e...，两授权修复程序身份74390755...。只授源码身份／手工对应，不授验证C前端或ABI信用。gate01实际退出0，20项检查符合预期：生产与12probe共13次coqc，隔离FrozenPrefix／PositiveRoots两次coqc，两项预期负控拒绝，三次coqchk。192个不同冻结输入保持；3个正控根和9个probe根打印假设并集仅classic与functional_extensionality_dep。正控不导入候选生产模块。DroppedOtherFrame只移除helper的其他任务块相等前提，第73行开始Proof／79行拒绝；StaleTaskRecord只把最终关系改回旧任务表，241行开始Proof／266行拒绝；整个目标Proof后缀均逐字保持，downstream_credit=false。不能从早拒绝推断所有下游机制有效；独立同次语义反例另行支持。

新增8项测试实际通过；全量926项／309失败1错误，310个诊断与本轮追加后旧918项按重数完全一致。前轮308个诊断全部保留，另增两项旧current-ownership快照／门禁SHA过期检查；不重绑旧证据，也不把所有历史失败都解释为快照问题。增量make退出0，仅COQDEP、无Coq重编，不授当前身份source-only全量干净构建信用。范围审计、冻结源码只读检查、diff通过；默认audit仍2，正式六门94／1／1／1／1／0保持。

已在第一次删除前逐项确认整个集合的路径／类别／大小／SHA及保留快照，清理82个一次性文件，共26,170,973字节：工作树Coq产物65、开发临时树12、临时生成器5。903个基线缓存路径保留，不声称缓存字节不变。全部源文件、依赖、用户数据和成功／失败证据保留；正式gate与配置源码临时树按各自manifest清理、另计。

**局部证明通过不等于整仓验收通过。** 下一步将物理ready／优先级表／任务字段／event对应接入可保持的共享不变量，再推进正常无锁调度、API／ISR和初始化。源码级GOOD_OS与同程序K1–K4尚未闭合；阶段一未完成，uC/OS-III未启动。见[中文教程与已填表格](docs/开发中/从抽象任务表到物理TCB字段.md)、[本轮审计](audit/STAGE26_TASK_RECORDS.md)及 `audit/logs/stage26-task-records/`。下方旧检查点保留历史身份。
<!-- task-records-checkpoint-end -->

<!-- current-ownership-checkpoint-start -->
## 最新局部检查点：同一次完整返回的当前指针权限与共享核心

`V293CriticalReturn.v` 保留原7252行逐字前缀，追加278行至7530行／500,625字节，SHA256 `accba980a6b7edcb6532f698dd43e6e9c8b27ecd89577fa0608f962714a0d2f2`。仍166活动源；其余165源、12个受保护输入、7936个既有audit/scripts/tests文件及HEAD保持，未提交。不改冻结C/config/port/framework、旧测试／门禁／报告及正式覆盖。

新一般根 `V293_critical_event_current_owned_execution` 只调用一次旧完整执行根，保留全部旧输出和同一Mf／Os'／OO'。入口明确加强为 `(CurTid current ** shared_fields ...) ** R`，另显式要求标准OSTCBCur指针块不在写集合或释放locals集合。由入口实际拥有的完整读取片段和同次执行的逐地址块frame，运输相同片段；再利用CurTid抽象域为空、shared_fields物理域为空重建最终空间组合。不是从typed load反推权限，不声称任意物理R保持，不宣称原接口与新接口的入口相同。

字面probe沿用上一轮原始内存与普通选择器8，直接构造完整编码的读取半份额和加强后的全部入口前提，再调用新根；没有复用旧已完成执行结果充当新入口证明。目标(41,8)从8→6仍等待，当前(60,0)优先级4的抽象ready成员保持，标准OSTCBCur存储块80保留，ready16/0、事件0/1→64/0、SEM类型3／计数0／NULL保持，返回0／caller恢复／locals释放。在同一最终Mf／OO'封装现有 `V293_shared_core ** Atrue`，并独立排除等待目标41的CurTid。另证明空物理内存不能拥有CurTid。run／ISR／lock仍1/1/0，实际调度受阻，不授正常无锁切换信用。

共享核心没有内置current必须ready，也不是完整的物理TCB／ready／优先级数组／ECB／资源链全局合法性。一般根仅保留原有关于ready成员的条件结论；字面例子的抽象ready成员不是完整物理TCB或初始化可达性证明。实际配置预处理／Clang函数身份仍c29b633e...、两授权修复程序身份74390755...；只授源码身份／手工对应信用，不授验证C前端或ABI信用。

gate01实际退出0，19项检查符合预期：生产与11probe共12次coqc，隔离FrozenPrefix／PositiveRoots两次coqc，两项预期负控拒绝，三次coqchk。191个不同冻结输入保持（166源＋11probe＋12受保护输入＋Before／baseline／gate三项＋2helper，扣除3重叠）。5个正控根和7个probe根实际打印假设并集仅classic与functional_extensionality_dep。正控不导入候选生产模块。DroppedBlockFrame只移除块相等前提，完整Proof后缀不变，45行开始、50行首次拒绝；ChangedCurrent只将最终CurTid改为等待目标，入口及整个Proof保持，277行开始、301行最终tauto拒绝。均downstream_credit=false，只授固定Proof敏感性，不能用早拒绝推断所有下游机制；独立语义反例另外提供证据。开发失败、源快照与日志均保留。

新增7项测试通过；全量实际918项／307失败1错误，308个诊断与本轮追加后旧911项按重数完全相同。对照前轮911项，306个旧诊断全部保留，新增两项逐条trace核对为旧当前任务一致性快照／门禁生产SHA过期；不重绑旧证据。增量make退出0，仅COQDEP、无Coq重编，不授当前身份source-only全量干净构建信用。范围审计／冻结源码只读检查／diff通过，默认audit仍2，正式六门94／1／1／1／1／0保持。

已逐路径／类别／大小／SHA确认全部目标后清理84个一次性文件，共24,612,534字节：新工作树Coq产物60、开发临时树24（含4个已保留逐字快照的临时源）。903个基线缓存路径均保留，不声称缓存字节不变。源码、依赖、用户数据和全部成功／失败证据保留；正式gate及配置源码临时树按各自manifest清理、另计。见cleanup-plan.json／cleanup-result.json。

**局部证明通过不等于整仓验收通过。** 下一步把现有共享核心与物理ready／TCB／event对应接入API保持接口，再推进正常无锁调度、ISR、初始化。同程序K1–K4与源码级GOOD_OS尚未闭合；阶段一未完成，uC/OS-III未启动。见[中文教程与补全表格](docs/开发中/从指针读数到共享核心的权限保持.md)、[本轮审计](audit/STAGE26_CURRENT_OWNERSHIP.md)及 `audit/logs/stage26-current-ownership/`。下方旧检查点保留历史身份。
<!-- current-ownership-checkpoint-end -->

<!-- current-consistency-checkpoint-start -->
## 最新局部检查点：同一次完整返回的当前任务纯对应

`V293CriticalReturn.v` 保留原7054行逐字前缀，追加198行，现7252行／481,555字节，SHA256 `5b134f38afad34e6de8027c9d32dc0c1816417ae23e14d5f6301b26def9fb72c`。166活动源中其余165源、12个受保护输入、7829个历史文件及HEAD保持，未提交。不改冻结C/config/port/framework、旧测试／门禁／报告或正式覆盖。

一般根`V293_critical_event_current_execution`只调用一次旧完整执行根，保留全部原始入口条件、旧输出和同一Mf／Os'／OO'。从该次执行的完整块frame和locals释放集合，保持标准OSTCBCur指针块的完整typed load；从实际最终共享字段取得OO'的curtid；由被改任务wait而current为ready推出两者不同，单点更新保持current成员。新增结论以入口对应／ready成员及指针块不被写和释放为条件，**没有从load反推CurTid所有权，也没有重建共享不变量**。

新字面例子另外构造同一原始内存：普通选择器8查找等待任务(41,8)，标准OSTCBCur标识符60显式绑定指针块80，其完整指针为现有ready任务(60,0)。抽象current、tasks、events不改，重建全部入口前提，未复用另一输入的已完成trace。同一次Mf／OO'观察目标8→6仍等待、ready16／0不变、事件0／1→64／0、SEM类型3／计数0／NULL保持，返回0、locals释放和caller恢复，以及物理／抽象current60、ready优先级4成员保持。run1／ISR1／lock0，真实调度仍受阻，不授正常无锁切换信用。

独立语义定理在同一次完整Mf／OO'上排除物理指针或抽象current等于等待目标41。另有旧输入错配定理，保留旧SELF物理41／抽象60的事实；不是简单改编号后认定旧入口合法。标准标识符映射及配置后Clang定位仅授源码身份／手工对应信用，不是验证过的C前端或ABI。函数SHA仍c29b633e...，两授权修复身份74390755...不变。

gate01实际退出0，18项检查符合预期：生产与10probe共11次coqc，隔离FrozenPrefix／PositiveRoots两次coqc，两项预期负控拒绝，三次coqchk。190个不同冻结输入保持（166源＋10probe＋12受保护输入＋Before／baseline／gate三项＋2helper，扣除3个重叠）。2个正控根和7个新probe根打印假设并集仅classic与functional_extensionality_dep。两个前瞻单因素负控仅将最终物理指针或抽象current换成等待目标，完整Proof逐字保持，172行开始、208行最终tauto拒绝。downstream_credit=false，不从最终拒绝推断全部中间机制有效；独立语义反例另外提供证据。开发生产／依赖／probe失败源及日志全部保留，正式gate在probe07实际成功后启动。

新增8项测试通过；全量实际911项／305失败1错误，与本轮追加后旧903项的306个诊断按重数完全一致。对照上一轮903项，原304个诊断全部保留，新增2项逐条trace核对为历史生产快照／门禁输入SHA过期；旧门槛和证据不重绑。增量make退出0，仅COQDEP而无Coq重编，**不授当前身份source-only全量干净构建信用**。范围审计、冻结源码只读检查及diff通过；默认audit仍2，正式六门94／1／1／1／1／0不变。

已逐路径／类别／大小／SHA确认全部目标后，清理67个专用一次性文件，共22,895,640字节：工作树新Coq产物55个、具有精确保留源码快照的开发临时树文件12个。903个基线缓存路径均保留，不声称缓存字节不变；源码、依赖、用户数据、所有成功／失败证据和快照保留。正式gate与配置源码临时树按各自manifest清理，另计。清单见cleanup-plan.json／cleanup-result.json。

**局部证明通过不等于整仓验收通过。** 下一步运输真实CurTid权限并重建共享核心，再接API／ISR保持、初始化及正常无锁调度。同程序K1–K4与源码级GOOD_OS尚未闭合；阶段一未完成，uC/OS-III未启动。见[中文教程与填好的表](docs/开发中/改优先级的目标任务不等于当前任务.md)、[本轮审计](audit/STAGE26_CURRENT_CONSISTENCY.md)和`audit/logs/stage26-current-consistency/`。下方旧检查点保留历史身份。
<!-- current-consistency-checkpoint-end -->

<!-- event-data-checkpoint-start -->
## 当前局部检查点：同一完整返回的SEM/MBOX头数据对应

`V293CriticalReturn.v` 保留原6851行逐字前缀，追加203行至7054行／467,008字节；SHA256 `b6b11977b5914a6cf857793f5b77ef7b69ee68b58a73c6986d0bc95ce0589686`。仍166活动源（103框架／tactic＋63目标）；其他165源、12项受保护输入、7630个既有证据文件与HEAD保持，未提交。不改C/config/port/framework、旧测试／门禁／报告或正式覆盖。

新增SEM/MBOX头数据关系：实际类型、完整Tint16计数及完整四字节指针，SEM计数界65535且指针NULL，MBOX计数0且指针等于抽象消息。完整typed-load frame检查整个读取足迹，不只首字节。完整适配根仅调用一次旧完整队列根，保留全部原前提／输出及同一Mf/Os'/OO'，数据参数来自同一实际持有ECB查询。新数据结论为入口对应成立蕴含同一出口对应成立；没有建立入口全局合法性。队列后备存储、互斥锁owner明确不在本关系内。

字面probe在同一原始内存安装SEM类型3、完整NULL和count0，重建全部入口前提后实际调用一般根：等待8→6，ready不变，事件0/1→64/0、group2→1，计数0／NULL保持，返回0、locals释放、caller恢复。独立语义定理在同一完整返回Mf排除count1；另用同类型且低字节同0的count256排除count0，用非空邮箱消息排除NULL。后两项仅授各自头数据语义信用，不是整邮箱API或正常调度执行。

gate02的17项实际检查符合预期：生产／9probe共10次coqc、隔离前缀与完整正控2次coqc、2次预期负控拒绝、3次coqchk。189个不同路径输入保持：166活动源＋9probe＋12受保护输入＋Before／baseline／gate三项＋2helper共192项分类归属，扣除3个重叠受保护源。正控只导入不含目标根的FrozenPrefix与依赖，不导入候选生产模块。4正控根及9probe根实际打印假设并集仅classic与functional_extensionality_dep。

前瞻单因素ChangedSemCount／NullMailboxMessage只改变最终SEM计数／MBOX消息，完整目标Proof逐字保持；均162行开始、175行tauto首次拒绝。两者downstream_credit=false，仅授固定Proof后置敏感性，不能替代独立语义反例，也不授C突变或一般不可证明性。开发probe四次失败及最小harness语法失败保留；gate01误在development04退出前启动，实际第12项重复该probe失败，没有负控／coqchk成功信用，冻结输入在其退出时保持，临时树按manifest清理；修正后另建gate02，不覆盖失败。

新增8项测试通过。全量实际903项／303失败1错误，304个诊断与本轮旧895项基线按重数完全一致；对照前轮895项，原302诊断全部保留，新增2项逐条trace复核为旧生产快照及门禁SHA身份过期。旧门槛／报告不重绑。范围审计、冻结源码只读检查及diff通过；实际配置预处理／Clang定位的OSTaskChangePrio函数SHA仍c29b633e...，另定位上游SEM/MBOX创建字段赋值。这只是源码身份及手工映射，不是验证过的C前端或ABI。增量make退出0、无Coq重编，不授当前身份source-only全量干净构建信用。默认audit仍2，正式六门94／1／1／1／1／0不变。

已先逐路径／类别／大小／SHA确认全部目标，再清理69个专用一次性文件，共21,541,763字节：工作树新Coq产物50、开发临时树18、具有逐字保留快照的一次性generator1。903个基线缓存路径全部保留，不声称缓存字节不变。生产源／probe／gate／测试／中文文档、成功及失败证据、精确开发快照、依赖和用户数据保留；gate01／02及配置源码临时树按各自manifest清理，另计。详见cleanup-plan.json与cleanup-result.json。

物理SELF41与抽象current60仍未一致；run1／ISR1／lock0的实际调度调用受阻。下一步建立当前任务一致性，再接共享不变量、API／ISR保持、初始化与正常无锁调度。同程序K1–K4和源码级GOOD_OS未闭合，阶段一未完成，uC/OS-III未启动。见[中文入门](docs/开发中/事件类型正确还不等于事件数据正确.md)、[审计](audit/STAGE26_EVENT_DATA.md)与`audit/logs/stage26-event-data/`。下方旧检查点保留历史身份。
<!-- event-data-checkpoint-end -->

<!-- event-return-frame-checkpoint-start -->
## 当前局部检查点：同一次完整return/free的ECB字节frame与类型保持

当前 `V293CriticalReturn.v` 为6851行／452,778字节，SHA256 `c9a9fcee4386465d90729366537ee47b964c9de91770ffa26ea5383b8f71ebef`。本轮原地增强六个构造性核心，旧六个公开定理的全部命题逐字不变，旧名称仅投影增强结果；并移动已有类型/frame定义到首次消费者之前。**不是旧6129行前缀逐字追加**，不沿用旧前缀身份的成功信用。166活动源中另165源、12项受保护输入、7549个既有证据文件及HEAD不改，未提交。

实际S1/S2任务表store、事件指针store、ready分支与TCB更新提供同一执行的细粒度frame，再穿过坐标、SELF／入口解析、真实受阻调度和return/free。完整队列根仅调用一次增强payload根，保留全部旧结果及同一Mf/Os'/OO'，在相对偏移10～12之外保持事件字节；条件类型结论绑定实际events查询中的同一data。未把入口一致性当成已证明的全局不变量。

固定probe在同一原始内存安装SEM类型3并重建入口前提；实际完整执行后类型仍3、事件两行0/1→64/0、group2→1，任务表8→6而任务指针不变，ready16/0与等待payload保持，返回0／locals释放／caller恢复。语义控制分别排除同一入口为邮箱，以及从同一次完整返回Mf证明绝对偏移17原值1／终值0和内存单元不等；不再仅观察纯写表达式。

gate01的16项实际检查全部符合预期：生产与8个probe共9次coqc、目标前冻结前缀与完整目标后缀2次coqc、3次coqchk、2次预期负控拒绝。185个**不同路径**输入保持（166源＋8probe＋12受保护输入＋Before快照＋gate脚本共188项分类归属，其中3个受保护源与活动源重叠）。隔离正控仅导入不含目标根的FrozenPrefix及依赖，不导入候选生产模块。8个正控根和5个probe根实际打印假设的并集仅classic与functional_extensionality_dep。

前瞻单因素负控完整目标Proof均保持：WrittenByteFramed仅将最终frame扩大到所有字节，Proof从161行开始、182行exact EventHeader首次拒绝；MailboxSubstituted仅将最终种类替为邮箱，183行exact Kind首次拒绝。两者downstream_credit=false，仅授固定Proof后置敏感性；不以早拒绝声称验证C突变或一般不可证明性。

新8项测试通过；全量895项实际301失败、1错误。对照本轮887项重构后基线，302个诊断按重数完全一致；对照前轮887项，原276个诊断全部保留，新增26项已逐条trace复核：23项旧prefix/hash/身份检查、3项旧Proof-body布局检查（实现仍在增强核心）。旧测试、门禁、报告不修改，不通过重绑历史身份制造通过。开发probe两次失败日志亦保留。范围审计、锁定源码检查及diff通过，实际配置预处理与Clang定位的函数SHA仍c29b633e...；只是源码身份／手工映射核对，不是验证过的C前端或ABI。增量make退出0且无重编，不授新身份全量干净构建信用；默认audit仍2，正式六门94／1／1／1／1／0不变。

所有目标逐路径／类别／大小／SHA确认后，清理48个一次性文件，共11,908,508字节：工作树新Coq产物45个、具有完整保留快照的一次性generator3个。903个既有缓存路径保留，不声称缓存字节不变；源码／probe／脚本／测试／文档／成功失败证据／可复用依赖保留。门禁及源码临时树按各自manifest清理、另计。

文档与清理后复验895项／301失败1错误，302个诊断按重数完全相同；新8项再次通过。最终范围／冻结源码／diff通过、audit仍2；165／12／7549项与HEAD保持、185项门禁输入保持、903个基线缓存路径均保留。全部真实结果见 `audit/logs/stage26-event-return-frame/`。

**局部证明通过不等于整仓验收通过。** 例子run1／ISR1／lock0，正常无锁调度未接入；物理SELF41与抽象current60尚未一致。ECB count/pointer与抽象内容、共享不变量、API／ISR保持及初始化仍开放。下一步建立ECB数据内容对应与当前任务一致性，再向共享不变量和初始化连接；同程序K1–K4与源码级GOOD_OS尚未闭合，阶段一未完成，uC/OS-III未启动。见[中文教程](docs/开发中/事件类型怎样穿过完整返回与释放.md)与[审计](audit/STAGE26_EVENT_RETURN_FRAME.md)。下方旧检查点为历史身份。
<!-- event-return-frame-checkpoint-end -->

<!-- event-type-checkpoint-start -->
## 最新局部检查点：非空事件子语句的物理类型与细粒度frame

`V293CriticalReturn.v` 原6018行／394,826字节逐字保持，追加111行至6129行／400,563字节，SHA256 `18c385b26da990e0e50f0606121b2399fdd32fcf89ee577bebb4bc9b8296dcb1`。166活动源；其他165源、12项受保护输入、旧测试／报告／门槛及HEAD保持，未提交。

重新校验锁定源码inventory和两授权修复全部hash。初次源码定位记录中350～800行探索性筛选为空；保留这条观察，在configured-source补充实际134～143行单事件语句，并实际重跑配置预处理及Clang定位，函数SHA仍为c29b633e...。临时源码树已按清单移除。模型内类型字段是偏移0的Tint8；真实ECB代码MBOX1／Q2／SEM3／MUTEX4，不与TCB等待状态位混用。

`V293_event_rekey_byte_frame` 从真实写表达式建立事件块偏移10～12之外的细粒度frame。`V293_event_nonnull_type_execution` 只调用一次原非空事件执行根，保留其确切Store／Me／Mf及全部原子语句结果；用该Store和局部块不别名条件将frame接回原始M，再推出同一Mf上的类型保持。入口匹配的是显式edata种类，不是实际持有的抽象events查询；不能把新增入口类型条件当作已建立的全局不变量。

字面probe在同一原始内存安装SEM类型3，构造全部物理前提并实际调用新一般根；8→6，事件位图0／1／2→64／0／1，头字节保持。独立语义定理排除同一入口为MBOX类型1，并证明真实写表达式的等待字节原值1、结果0和原单元不等；后者不授整段返回执行反例信用。

正式gate01的14项实际通过，179输入保持：生产与7个probe共8次coqc、冻结前缀与完整后缀2次coqc、3次coqchk及1次预期拒绝的负控。正控只导入冻结旧前缀而非候选生产模块。九个实际打印根的假设并集仅classic与functional_extensionality_dep。HeaderChanged仅改变最终类型为邮箱、目标完整Proof保持，106行开始、119行exact Kind首次拒绝；downstream_credit=false，只授固定Proof后置敏感性。

新增8项测试通过。全量Ran 887 tests in 51.232s；FAILED (failures=275, errors=1)。原274个诊断按重数全部保留；新增两项逐条复核为旧队列报告的生产SHA和完整负控输入SHA过期，旧测试和报告不改，不递归重绑或弱化门槛。初次局部测试在门禁尚未结束时缺少result.json而有2错误，后续8项全部通过；初次freeze误传不支持的--check参数退出2，使用既有无参数只读检查后通过，失败日志保留。增量make通过且无重编，不授当前身份source-only全量干净构建或旧完整函数门禁重放信用。默认audit仍2，正式六门94／1／1／1／1／0保持。

文档后全量复验887项／275失败1错误，276个诊断按重数完全一致。先逐路径／类别／大小／SHA确认，再清理60个一次性文件，共17,419,230字节（新工作树Coq产物40个、隔离开发树20个）；903个既有缓存路径全部保留，不声称缓存字节不变。门禁及源码临时树按自身manifest清理、另计；源／probe／脚本／测试／中文文档／成功失败日志／快照／依赖／用户数据保留。

**范围未扩大为完整返回保持。** 下一步把事件细粒度frame接过真实前缀／坐标／TCB更新，再穿过同一次完整return／free，并与原实际ECB查询／列表相连。计数／pointer数据内容、当前任务一致性、共享不变量、正常无锁调度、API／ISR保持和初始化仍开放。同程序K1–K4及GOOD_OS未闭合，阶段一未完成，uC/OS-III未启动。见[中文逐步说明](docs/开发中/事件类型字节为什么不会被改坏.md)及[审计](audit/STAGE26_EVENT_TYPE.md)。
<!-- event-type-checkpoint-end -->

<!-- event-queue-checkpoint-start -->
## 最新局部检查点：实际ECB等待列表与同一Mf的事件位图相连

`V293CriticalReturn.v` 原5797行／379,633字节逐字保持，追加221行至6018行／394,826字节，SHA256 `6efff6628f97496864f7874e32a53d58b4b56615d6465738463827c9c1873eae`。仍166活动源，其他165、12项受保护输入及HEAD保持，未提交。固定C只读核对并在自有临时树应用两授权修复，全文件hash与冻结记录一致，临时源码树已移除。

`V293_event_wait_queue` 连接实际持有的同一events查询、edata种类／事件地址以及waiters与同一tasks的wait成员双向等价；`V293_event_wait_queue_rekey` 保持同一列表与指针身份。`V293_event_queue_priorities_bound` 把既有事件wait位图关系连接到该列表，在p<13域内成立；没有另行证明任意入口列表的全局优先级范围或NoDup。

稳定一般根 `V293_critical_event_queue_execution` 保留上一轮全部入口与出口，不以完成执行或出口load为前提。实际调用原一般payload执行根，在同一Mf／Os'／OO'上保留返回0、局部释放、caller恢复、抽象步骤／所有权、TCB与表迁移、ready不变、事件位图迁移和payload保持；新增同一ECB列表成员关系及其与最终真实位图的对应。出口仅fields ** Atrue，不保持任意物理R。

固定字面probe使用实际信号量ECB与单元素等待列表，在同一原始内存构造全部前提并调用新一般接口；8→6但任务指针(41,8)不变，ready16/0不变，事件0/1→64/0。不是第二份独立实现证明；物理SELF仍41而abstract current仍60，未称一致或初始化可达。运行1／ISR1／锁0，实际调度调用受阻。

正式gate01保留具体ECB查询lemma elaboration失败，无完整成功信用；改用具体EcbMod.map_get_sig并修复同类lookup否定证明后，gate02的14项实际通过、178输入保持：生产与6个probe共7次coqc，生产／新probe／隔离完整正控3次coqchk，冻结前缀与完整后缀2次coqc，两负控。正控只导入FrozenPrefix及其依赖，不导入候选生产模块。四个probe根与三个正控根的实际假设并集仅classic与functional_extensionality_dep。

两个前瞻单因素负控只改出口列表／edata，目标完整Proof保持，均223行开始、242行exact FinalQueue首次拒绝；downstream_credit=false，只授固定Proof后置敏感性。固定空列表语义定理先因查询拒绝，不能授成员方向信用；因此另行在Lookup及sem类型／地址显式正确的输入中，分别漏登记真实wait任务和加入ready幽灵任务，实际coqc／coqchk检查两个成员方向，并核查两项查询／类型见证；这四根实际假设仅classic。

新增9项局部测试通过；全量Ran 879 tests in 50.944s；FAILED (failures=273, errors=1)。前轮273个诊断按重数保留，新增1项逐条trace复核为旧wait-payload报告生产SHA过期。旧测试／报告不改，不递归重绑或弱化门槛。范围审计、冻结源码只读核对、diff及增量make通过；make无重编，不授当前身份source-only全量干净构建或旧完整函数门禁重放信用。默认audit仍2、正式六门94／1／1／1／1／0不变。

逐路径／类别／大小／SHA确认清理56个一次性文件，共17,144,941字节（工作树新Coq缓存35、隔离开发树18、一次性generator／runner3）；门禁临时树按自身manifest清理、另计。903个基线缓存路径全部保留，不声称缓存字节不变；源码／probe／测试／中文文档／成功失败日志／snapshot／依赖与用户数据保留。

边界：仅未挂起单事件等待局部连接；物理OSEventType／ECB数据及count／pointer、当前任务一致性、完整共享不变量、正常无锁调度、API／ISR保持和初始化仍开放。同程序K1–K4及GOOD_OS未闭合，阶段一未完成，uC/OS-III未启动。下一步先从真实写集合给事件头细粒度frame，再绑定物理事件类型，不能把新增入口前提当作已建立的不变量。见[中文步骤与表格](docs/开发中/事件位图怎样对应真正的等待队列.md)与[本轮审计](audit/STAGE26_EVENT_QUEUE.md)。
<!-- event-queue-checkpoint-end -->

<!-- wait-payload-checkpoint-start -->
## 前一局部检查点（5797行历史身份）：真实TCB等待字段与抽象wait在同一Mf保持

`V293CriticalReturn.v` 原5422行／353,188字节逐字保持，追加375行至5797行／379,633字节，SHA256 `c7e749a65e8274e4b83ebc60bf254cc04b9dfbade7e47649b33d1383bdf86cba`。活动源仍166，其他165、12项受保护输入和HEAD保持，未提交。固定C先只读核对，再在自有临时树应用两项授权修复；核对全文件hash，记录真实字段／状态位源码定位，源码树已移除。

新增 `V293_critical_event_return_tcb_frame` 保留完整事件返回路径的全部原前提／结论，并暴露TCB相对偏移50～54之外的字节保持：事实来自已有真实update根，穿过真实受阻调度、return及free，而非预给出口load。`V293_wait_payload_field_layout` 核对Msg32／Dly44／Stat48／StatPend49的类型和偏移。`V293_wait_payload` 仅绑定未挂起的信号量／邮箱／队列／互斥锁等待，超时和消息对应同一抽象wait参数；pend是显式原始字节，不冒充完整超时／abort生命周期。

稳定根 `V293_critical_wait_payload_execution` 保留上一轮一般等待事件入口、实际shared_fields所有权与同一任务表的ready／table／event关系，再加原始M中的字段绑定；同一Mf给出真实返回、释放、TCB与表迁移、ready不变、event迁移、实际抽象步骤、仍等待的成员与最终字段绑定。出口仍是fields ** Atrue，不保持任意物理R。

固定字面probe先在同一原始M安装非空消息Vptr(120,7)、超时1、SEM状态1和pend0，再构造全部一般条件，实际调用新一般接口。它不是旧固定execution oracle；另有语义定理否定该输入同时绑定成NULL消息。physical SELF来源仍41，abstract current仍60；未称当前任务一致、全局合法或初始化可达。运行1／ISR1／锁0，调度受阻。

门禁13项实际通过，177输入保持；6次coqc检查生产和五probe，生产／新probe／隔离完整正控3次coqchk，冻结5422行前缀与完整新增后缀2次coqc。临时正控只导入FrozenPrefix，不导入候选生产模块。三个probe根和三个正控根的实际假设并集仅classic与functional_extensionality_dep。TimeoutChanged／MessageErased只改出口payload，完整目标Proof保持，在目标Proof后按预定因子拒绝；各自首次拒绝见review，downstream_credit=false，不授C修改或命题不可证信用。

新增9项局部测试通过。完整测试：Ran 870 tests in 44.947s；FAILED (failures=272, errors=1)。原271个诊断按重数保留，新增2项逐条trace复核为历史生产／负控输入SHA过期，旧测试／报告均原样保留；不递归重绑或削弱门槛。范围审计、冻结源码只读核对、diff和增量make通过；增量无重建，不授当前身份source-only全量干净构建或旧完整函数门禁重放信用。默认audit仍2，正式六门94／1／1／1／1／0保持。

逐路径／大小／SHA确认清理56个本轮一次性文件，共16,713,167字节；门禁临时树按自身manifest移除，另计。开发源／generator均有文本snapshot；903个基线缓存路径保留，不声称缓存字节不变。源码／固定probe／测试／中文文档／成功失败日志／依赖／冻结证据／用户数据保留。

边界：不是完整TCB／事件／共享不变量、完整API Hoare、前向模拟或GOOD_OS。下一步连接OSEventType、ECB队列和当前任务一致性，再接正常无锁切换、函数环境、ISR/API保持和初始化。同程序K1–K4及GOOD_OS未闭合，阶段一未完成，uC/OS-III未启动。见[中文入门](docs/开发中/把等待状态绑定到真实TCB字段.md)与[审计](audit/STAGE26_WAIT_PAYLOAD.md)。
<!-- wait-payload-checkpoint-end -->

<!-- wait-event-owned-checkpoint-start -->
## 前一局部检查点（5422行历史身份）：等待事件任务改优先级，仍保持等待

原5063行／330,382字节逐字保持，`V293CriticalReturn.v` 追加359行至5422行／353,188字节，SHA256 `6d9acfd12e10f1428681e37f443d377b50af9b6e3e56ac1a26634d3638bac624`。166活动源、其他165源和12项受保护输入保持；148项历史测试／报告原样保留，未提交。

新一般根 `V293_critical_wait_event_owned_execution` 从同一原始M、实际持有的shared_fields及同一任务表的table／ready／事件关系出发，不预给执行完成或出口关系。物理空新槽导出抽象fresh；同优先级指针唯一性排除另一个ready任务，导出ready测试为false。实际构造保留完整wait原因／超时／消息的框架原语步骤，接原一般事件完整返回根。同一Mf上有返回0／释放locals／caller恢复、TCB／表迁移、ready两行不变、事件位图迁移和EventPtr保持；出口关系对应同一更新后的任务表。只给fields ** Atrue，不保持任意物理R。

固定字面接口probe在同一原始M构造全部条件并实际调用新一般根：wait8→wait6、另有ready4、ready16/0不变、事件0/1→64/0。独立语义定理否定迁移后位图仍对应原表。仍运行1／ISR1／锁0、调度受阻；物理SELF来源与抽象current尚未一致，不能称完整共享合法性或初始化可达。物理TCB状态／超时／消息、OSEventType、ECB抽象等待队列等完整绑定仍开放。

新门禁12项实际通过，176项输入保持；5次coqc检查生产与四probe，3次coqchk检查生产／新probe／隔离完整正控，冻结5063行前缀及完整新增后缀实际coqc。三个probe根及三个正控根的实际假设并集仅classic与functional_extensionality_dep。两负控保持目标完整Proof，均350行开始，WakeWaiter于382行map_get_set拒绝，StaleEventRelation于381行FinalEvent拒绝；只授固定Proof后置敏感性，全部downstream_credit=false。

新增8项局部测试通过。全量861项实际270失败1错误，原269个诊断按重数全部保留；新增两项分别为旧一般ready报告的生产SHA及负控输入SHA过期，逐条trace已复核，旧测试／报告未改。范围审计、冻结源码只读核对、增量make、diff通过；增量无需重建，不授当前身份全量source-only干净构建或旧完整函数门禁重放信用。默认audit仍因正式证据身份过期退出2，六门94／1／1／1／1／0不变。

已逐路径确认清理50个本轮一次性文件，共14,864,046字节（开发树25个、工作树新Coq缓存25个）；门禁临时树按自身清单清理，另计。903个基线缓存路径、源码／probe／测试／中文文档／成功失败日志／快照／历史证据／依赖／用户数据全部保留，不声称基线缓存字节不变。

不是整函数Hoare、前向模拟或完整共享不变量。下一步先补物理TCB／事件／当前任务与抽象状态的绑定，再接正常无锁切换、完整API及函数环境、ISR保持和初始化。GOOD_OS与同程序K1–K4未闭合，阶段一未完成，uC/OS-III未启动。见[中文入门](docs/开发中/等待任务改优先级为什么不会被唤醒.md)与[本轮审计](audit/STAGE26_WAIT_EVENT_OWNED.md)。
<!-- wait-event-owned-checkpoint-end -->

<!-- ready-general-entry-checkpoint-start -->
## 前一局部检查点（5063行历史身份）：一般NULL-ready成功入口与实际持有任务表配对

原4849行／316,712字节逐字保持，仅追加214行（含分隔空行）至5063行／330,382字节，SHA256 `abe6ad33db96bbfea234f9930c2cb5f76cbd76ddd0129de4bba4a0b65b256122`；仍166活动源，其他165源及12项受保护输入不变，未提交。

`V293_critical_ready_null_owned_execution` 保留原一般完整NULL成功路径全部物理前提，再接同一原始M的 `shared_fields ** R`、实际目标ready成员、bitmap／table关系及外部抽象帧。由物理新槽NULL与同一表load关系导出抽象fresh，不要求执行／store／free／spec_step完成或最终关系oracle。出口同一Mf上实际return0、恢复caller、释放locals，观察TCB／ready／table／NULL事件与明确具体frame；实际抽象步骤和外部帧保持；bitmap／table对应同一set后的tasks，最高ready任务的指针在同一Mf中实际可读。

新增空堆／运输引理只运输抽象字段，出口为 `shared_fields ** Atrue`，不声称任意物理R跨写／free仍成立。固定字面一般接口及统一入口probe已实际coqc；后者在同一原始M构造全部物理条件和所有权，实际调用新一般根，不借用旧固定执行见证代替。运行1／ISR1／锁0，调度调用仍走受阻分支。

新门禁11项实际通过，175项输入保持，门禁临时树已移除；4次coqc检查生产与三probe，3次coqchk检查生产／新probe／隔离完整正控，冻结4849行前缀及完整后缀实际coqc。两probe根与三正控根的实际假设并集仅classic和functional_extensionality_dep。两单因素负控保留完整目标Proof：均184行开始，NoOwnedEntry于200行owned_step应用拒绝，StaleTaskRelation于233行FinalBitmap拒绝；全部downstream_credit=false，不授修改C或命题不可证信用。

新增12项测试通过。完整853项实际268失败1错误，比上轮841项／263失败1错误多5项：逐条核对均为旧4849行报告SHA与新5063行源码SHA不匹配；原264个诊断按重数全部保留，无删除。60项历史测试／driver／上轮报告原样保留，不递归重绑或放宽门槛，不宣称完整测试通过或旧门禁已在当前身份重放。范围审计、固定源码只读复核、增量make和diff通过，增量无需重建；已逐路径／类别／大小／SHA确认并清理39个本轮一次性文件，共13,346,457字节（隔离开发树19个，工作树新Coq缓存20个）。门禁临时树由自身清单清理，另计、不重复计入39个；903个基线缓存路径全部保留，不声称字节不变。源码、probe、测试、中文文档、成功／失败日志、文本快照、历史证据、依赖与用户数据保留。见本轮cleanup-result.json。正式六门仍94／1／1／1／1／0，默认audit仍因旧正式证据身份退出2。没有当前身份全量source-only干净构建或旧完整函数门禁重放信用。

边界：不是整函数Hoare、前向模拟、完整ready／TCB／事件不变量、初始化或正常无锁切换。下一步接非ready／事件、完整共享关系、源码切换、API分配／函数环境和ISR／初始化。GOOD_OS与同程序K1–K4未闭合，阶段一未完成，uC/OS-III未启动。见[中文逐步说明](docs/开发中/一般入口如何配对共享任务表更新.md)及[本轮审计](audit/STAGE26_READY_GENERAL_ENTRY.md)。
<!-- ready-general-entry-checkpoint-end -->

<!-- ready-owned-checkpoint-start -->
## 前一局部检查点（4849行历史身份）：ready 成功具体轨迹配对实际持有的抽象任务表更新

原4586行／302,952字节逐字保留，追加263行至4849行／316,712字节，SHA256 `419f807645f73200f9a9959e6ce09a65eb10cfe5a7ce7efd51662469e79db71d`。仍166活动源，固定C／配置／分析端口／框架／正式证据与覆盖不改，未提交。

`V293_ready_prio_owned_step` 从 `V293_shared_fields ... ** R` 取得真正持有的任务表，保持任意外部帧，实际构造框架 `spec_prim_step` 并证明域与当前任务保持。原语只覆盖已解析的ready情形，显式要求新优先级空闲，不是完整API规格。`V293_ready_prio_branch_relations` 从入口ready成员与位图关系导出实际测试为真，再推导位图和任务表对应同一个set后的抽象表，无出口oracle。

`V293_critical_ready_owned_success` 将上述结果接到完整NULL成功具体见证，同一Mf观察返回零／caller恢复、TCB五字段、ready80/0、物理任务表、NULL事件指针、全部局部释放和最终共享字段所有权。原语的抽象帧独立保留。固定probe实际构造所有权入口，消掉该条件及空外部帧。另两条语义否定定理证明旧抽象表不能对应出口位图，移动任务优先级6不是最高（优先级4任务仍就绪）。

新门禁gate01的15项实际检查通过，177项输入保持，临时树已清理；四probe根及五根完整／单根正控的实际假设并集仅classic与functional_extensionality_dep。三个单因素负控保留目标完整Proof：NoAbstractWrite在100行Proof后114行的出口identity首次拒绝；ReadyNotUpdated／TableNotUpdated均在215行Proof后254行的FinalBitmap／FinalTable首次拒绝。只授固定Proof后置敏感性，全部downstream_credit=false；两个语义反例另行证明，不混授信用。

旧入口13项、旧完整返回17项门禁均在当前4849行身份实际重放通过，分别175／173项输入保持；原driver／probe不改，假设并集仍仅上述两项。旧测试只重绑实际新报告，48／31个assertion AST保持，历史证据不覆写。各负控首次拒绝已复核，不授下游信用。新增14项、相关91项局部测试通过；完整841项仍263失败1错误，264个FAIL／ERROR标签与前轮827项按重数完全相同，无新增或删除。范围审计、冻结只读核对、增量make及diff通过；增量无需重建，不授当前身份source-only全量干净构建或全部旧函数门禁重放信用。默认audit仍2，拒绝旧正式函数证据身份；六门仍94／1／1／1／1／0。

逐项确认路径／类别／大小／SHA后，清理26个本轮一次性文件，共6,453,467字节（工作树新Coq缓存20个，隔离开发树6个）。三个门禁临时树另有清单且已消失，不重复计入26个；903个基线缓存路径全部保留，不声称其字节不变。源码、probe、测试、文档、成功／失败日志、文本快照、冻结证据、依赖和用户数据保留。详见本轮cleanup-result.json、full-test-comparison.json与各首次拒绝复核。

边界：只是固定NULL成功见证与局部抽象原语配对，不是前向模拟或完整API规格；`shared_fields ** Atrue` 不约束剩余堆，不等于完整ready不变量，也不证明全部TCB／事件合法性、初始化可达或正常无锁切换。仍运行1／ISR1／锁0，具体调度调用受阻。下一步连接一般入口资源、非ready／事件情形及真实共享不变量，再补源码切换、函数环境、入口分配、ISR/API保持及初始化。GOOD_OS与同程序K1–K4未闭合，uC/OS-III未启动。见[中文入门](docs/开发中/把物理就绪位图连接到共享任务表.md)和[本轮审计](audit/STAGE26_READY_OWNED_TRANSITION.md)。
<!-- ready-owned-checkpoint-end -->

<!-- success-entry-witness-checkpoint-start -->
## 前一检查点（4586行历史身份）：两种完整成功入口的全部条件各自在同一内存成立

`V293CriticalReturn.v` 原4107行／264,621字节逐字节保持，追加479行至4586行／302,952字节，SHA256 `fb8047b322b3b9207c3badfcd5570374ffe76c65615e85dfa01a1cdc056eea31`。仍166活动源，其他165源、12项受保护输入及HEAD不变，未提交；固定C／配置／分析端口／框架／正式证据与覆盖不改。

新增 `V293_critical_null_success_return_witness`／`V293_critical_event_success_return_witness`，只量化ir、原IE及相关栈，没有资源或执行完成前提，分别在自己的一个原始具体内存上实际应用完整成功返回根。SELF255解析为8再改为6，初始ptcbNULL、四坐标255；同一最终Mf观察任务表、TCB、ready／事件更新、11个局部块共17字节全部释放、guard全块保持和空caller／kstop恢复。ready入口16／1变80／0，非空事件入口0／1变64／0，最终两组字节均1。运行1／ISR1／锁0：实际调用调度器，但只走中断受阻分支。仍不是共享合法性、初始化可达、完整API入口分配或正常无锁切换证明。

新门禁 `audit/logs/stage26-success-entry-witness/gate02/result.json` 的13项实际检查通过，175项输入身份保持。生产／旧字面probe／新字面probe实际coqc，生产／新probe及临时完整正控实际coqchk，冻结4107行前缀及完整／NULL／event三正控实际coqc，三个前瞻单因素负控均在目标Proof内首次拒绝。临时正控不导入候选生产模块，固定probe不是第二份独立证明。实际两probe根及三正控假设并集仍仅classic与functional_extensionality_dep。ReturnOne／LocalRetained／EventBitmapNeutralized保留目标完整Proof，88／88／89行Proof后于266／268／278行分别在exact Exec／Removed／EventReady首次拒绝；只授后置敏感性，不授C修改、命题不可证或下游有效性信用，全部downstream_credit=false。

旧完整返回17项门禁在新身份下实际重放通过，173项输入保持；三个probe根、四正控的实际假设仍仅上述两项。六负控在目标Proof内与历史相同行首次拒绝，前五项Proof不改，第六项只中和第二次store权限传递，不授C修改或下游信用。旧12测试的31个assertion AST保持，仅将当前身份结果绑定到实际新重放；原历史证据不覆写。新增14项和既有63项相关局部测试合计77项通过；完整827项仍263失败1错误，264个FAIL／ERROR标签与前轮813项按重数完全相同，无新增或删除。范围审计、冻结只读核对、增量make和diff通过；增量无需重建，不授当前身份source-only全量干净构建或旧函数完整门禁重放信用。默认audit仍2，正式六门仍94／1／1／1／1／0。

逐项确认路径／大小／SHA后，清理37个本轮一次性文件，共11,903,415字节（工作树新Coq缓存15个、隔离开发树和生成模板22个）。三次实际门禁的临时树另有清单，均已消失，不重复计入37个；903个基线缓存路径全部保留，不声称其字节不变。源码、固定probe、测试、文档、成功／失败／取消日志、文本快照、冻结证据、依赖和用户数据保留。详见本轮cleanup-result.json、full-test-comparison.json及final-validation-summary.json。

开发第02次整内存求值主动取消、gate01主动中止、各次开发／导入错误及第10次生成失败后误编译旧文件的退出0均保留，不记新成功信用。第13次实际通过强化的两个见证，生产追加部分不含vm_compute或未完成证明占位符。

下一步把物理ready／TCB／事件连接到同一抽象任务表及共享不变量，处理准确当前缓存、源码切换对应和无锁调度，随后完整函数环境、入口分配、ISR／API保持及初始化。GOOD_OS和同程序K1–K4未闭合，uC/OS-III未启动。见[中文入门](docs/开发中/把成功入口的全部条件放到同一内存.md)及[本轮审计](audit/STAGE26_SUCCESS_ENTRY_WITNESS.md)。
<!-- success-entry-witness-checkpoint-end -->

<!-- success-complete-return-checkpoint-start -->
## 前一检查点（4107行历史身份）：同一原始内存到成功返回、释放与调用者恢复

`V293CriticalReturn.v` 原2605行／166,699字节逐字保持，追加1502行至4107行／264,621字节，SHA256 `e12712865a0eb880c270d1307c0f3e7ccf7db18e99ca17e57a3f7a35da31fc89`。其他165活动Coq源、12项受保护输入及HEAD保持，仍166源、未提交。固定C／配置／分析端口／框架／正式函数证据及覆盖不改。

新增稳定根 `V293_critical_null_success_return_execution`／`V293_critical_event_success_return_execution`，从同一个原始M连续执行参数guard、encrit、SELF／lookup、坐标／任务表／ready／事件／TCB更新、excrit、OSRunning条件及真实受阻调度调用、return0、free全部locals，恢复caller／continuation、原IE／相关栈及ir。完整局部写权限仅要求在原始M成立，沿实际S1／S2／Store及有限pure字节更新推导FinalWritable，再实际应用旧返回尾根；没有中间内存可释放、store成功、执行完成oracle。后置在最终Mf保留表／TCB／ready／事件观察和非local非written frame，全部局部字节为None。新增原始入口NoDup及heap/local分离是充分条件，不宣称最弱；heap分离只保护后置明确观察的对象，不是任意全局环境的完整分离。

`V293_success_load_free_permission_ablation` 以同地址／同字节7仅翻转permission布尔位：load相同，free Tint8仅完整权限时成功。这不是新两根全部入口前提的统一见证。**新完整入口同状态物理见证尚未通过**；旧更新见证和旧返回尾见证不能替代。一次无界vm_compute探索超过4.6GB RSS后主动中止，保留源码快照与取消记录，无成功或负控信用。

规范 `audit/logs/stage26-success-complete-return/gate02/result.json` 的17项实际检查通过：生产及独立固定字面probe两次coqc／两次coqchk，冻结2605行prefix、权限helpers、完整根及NULL／event／table-store投影六次coqc，完整正控coqchk，六个前瞻单因素负控。临时正控不导入候选生产模块；probe独立固定字面AST与接口，不由门禁运行时生成，但不是第二份独立证明。三probe根及四正控的实际Assumptions并集仍仅classic与functional_extensionality_dep；173项输入身份保持。

负控前五项保留目标完整Proof后缀：ReadableNotWritable／NoDupRemoved／HeapTableMayBeLocal在115行Proof之后，于138／141／146行分别拒绝原始写权限传递、尾根NoDup应用、FinalLoad成员域；ReturnOne／CallerNotRestored均在151行拒绝exact Return。SecondTableStoreNeutralized为实现侧单因素消融，只中和第二次store权限传递，264行Proof后348行因M2／M1无法统一拒绝；不冒称Proof未改或C store被删除。全部downstream_credit=false，只授实际首次拒绝依赖信用，不证明改动命题不可证或所有下游机制有效。逐项定位见negative-first-rejection-review.json。

新增12项、既有51项相关局部测试合计63项通过。完整813项仍263失败1错误，264个FAIL／ERROR标签与前轮801项按重数完全相同，无新增或删除。范围审计、冻结只读核对、增量make及diff通过；增量make无需重建，生产源另有实际coqc／coqchk。默认make audit仍2，原因为旧正式函数证据身份过期；不覆写它获得假通过。无当前4107行身份source-only全量干净构建或旧函数完整门禁重放信用，正式六门覆盖仍94／1／1／1／1／0。gate01主动中止、开发错误、统一见证中止及门禁未终结时的测试错误全部保留。

逐项路径／大小／SHA确认后删除34个一次性文件，共10,556,088字节（新工作树Coq缓存10个，开发树及一次性生成器24个）；生成器和探索源码已保留不可执行的文本快照。两次实际门禁临时树另有清理清单，均已消失，不重复计入34个；903个本轮基线缓存路径保留，不声称字节不变。源码、固定probe、测试、文档、成功／失败／中止日志、控制快照、依赖与用户数据保留。见cleanup-result.json、identity-review.json及final-validation-summary.json。

下一步先用有界地址／偏移和既有资源引理，为两根新增全部前提构造统一入口见证，避免无界vm_compute；随后接无锁调度与同一物理共享关系，再闭合真实API入口分配、函数环境、初始化及顶层定理。仍仅有限非运行／ISR／锁定路径与显式临界宏抽象，不是raw port、硬件、所有并发交错或完整函数Hoare。GOOD_OS及同程序K1–K4未完成，uC/OS-III未启动。见[中文逐步说明](docs/开发中/从原始入口一直执行到返回零.md)。
<!-- success-complete-return-checkpoint-end -->

<!-- success-sched-return-checkpoint-start -->
## 前一检查点（2605行历史身份）：真实受阻调度调用已连接，成功返回仍为分段根

`V293CriticalReturn.v` 原1934行／123,526字节逐字保持，追加671行至2605行／166,699字节，SHA256 `2019d05a00af959cbc948bfa02d930595c62f1919648aeb1635776edbd37c57e`。其他165活动源、12项受保护输入、HEAD、固定C／配置／分析端口／框架／正式证据／覆盖保持；仍166源、未提交。重新物化配置C核对OSRunning==1u、OS_Sched及OS_SchedNew的当前函数体，保留完整unlocked后缀；人工AST身份回归不是新前端或端口实现。

新增 `V293_success_sched_call_execution` 从真实函数环境绑定和原始guard字节资源，实际snpcall／sfexec、构造fresh／alloc、cpu_sr=0、encrit、受阻guard、excrit、sret／free，恢复完全同一M、caller、IE及栈。非运行条件根无需函数定义；中断非零分支无需锁绑定，字面probe有专用无绑定实例。实际有限轨迹只覆盖非运行／ISR／调度锁定，**不授正常选择、计数或switch信用**；仍是显式中断宏抽象，不是原始端口／token字节仿真或所有并发交错。

`V293_critical_null_schedule_execution`／`V293_critical_event_schedule_execution` 从原始M连续执行原参数／临界／SELF／lookup／坐标／表／ready／事件／TCB更新、excrit和真实条件调度调用，使用实际更新frame运输运行／guard读数，保留完整数据与frame后置。没有中间执行／store／调度完成oracle，终点仍sskip None。额外全局读块away条件是保守充分条件，不是最弱前置。`V293_success_tail_return_execution` 则从更新后边界M及全部locals写权限出发，实际return0／free／恢复task caller；**尚未从原入口导出这些全部最终权限并接为同一个完整API根**。尾部同状态物理见证覆盖任意合法运行／嵌套／锁字节、任意IE及栈，只在运行时要求受阻；不替两条完整更新根所有新前提提供统一见证，也不是初始化／共享合法性可达性证明。

规范 `audit/logs/stage26-success-sched-return/gate04/result.json` 的16项实际检查通过：生产与独立固定字面probe两次coqc／两次coqchk，冻结1934行prefix、完整与call／schedule／tail四个不导入候选模块的正控coqc、完整正控coqchk，以及六个单因素负控。六probe根和四正控的实际假设并集仍仅classic及functional_extensionality_dep；173项输入匹配。固定字面probe不由门禁运行时从候选接口生成，不是第二份独立证明。

负控保持目标完整Proof：RunningZero／WrongCall在299行Proof后于305／307行拒绝；NoFunctionBinding／ExitSti在204行后于232／256行拒绝；ReturnOne／CallerNotRestored在328行后均于339行拒绝。首拒绝分别为真实条件求值／调用根应用／sfexec函数绑定／excrit规则／返回根应用；只记脚本敏感性，downstream_credit=false，不宣称修改命题不可证明或下游机制有效。两个中和表达式以计算擦除的typed let保留参数类型，不保留原函数绑定。gate01保留prefix分隔空行错误；gate02的WrongCall在Proof前类型推断拒绝不计信用；独立预检又发现裸True绑定中和的同类问题，gate03主动中止、清理并保留失败终态。经前瞻修订及六项快速预检后才运行gate04，未放宽门槛或改生产证明。

新增13项、既有38项critical局部测试合计51项通过；完整801项仍263失败1错误，264个FAIL／ERROR标签与前轮788项按重数完全相同，无新增或删除。此前门禁未结束／失败时的局部与完整失败日志保留。范围审计、冻结只读核对、增量make及diff通过；增量make实际无需重建，生产源另有实际coqc／coqchk。默认make audit仍2，原因为旧正式函数证据身份过期。没有当前2605行身份source-only全量干净构建或完整旧函数门禁重放信用，正式六门覆盖仍94／1／1／1／1／0。

逐项路径／大小／SHA确认后删除本轮35个一次性文件，共6,212,364字节（工作树新缓存20个、专属开发树文件15个），并移除空gate01目录。配置C、两次预检及三次实际门禁临时树均有清理记录；901个基线缓存路径保留，不声称其字节不变。源码、固定探针、成功／失败／中止日志、控制副本、证据、可复用依赖及用户数据保留。见本轮cleanup-result.json、identity-review.json、negative-first-rejection-review.json和final-validation-summary.json。

下一步从原入口真实写权限推导全部更新后locals可释放，再合成同一原入口到return0／free／caller根，不能新增“中间可释放”oracle。正常调度、共享不变量、实际API分配、完整函数环境与初始化仍开放。GOOD_OS及同程序K1–K4未完成，uC/OS-III未启动。见[中文逐步说明](docs/开发中/成功尾部如何真正调用调度并返回.md)。
<!-- success-sched-return-checkpoint-end -->

<!-- critical-success-checkpoint-start -->
## 前一检查点（1934行历史身份）：成功入口实际更新数据，并恢复原中断状态

`V293CriticalReturn.v` 原1132行逐字保持，追加802行至1934行／123,526字节，SHA256 `7ce3552f82e96b602c8e89b92e0bcc979c95e477100e51cdce313e57c970d7dc`。其他165活动源、12项受保护输入、固定C／配置／分析端口／框架／正式证据／覆盖及HEAD不变；仍166活动源、未提交。重新物化配置C，核对同一 `OSTaskChangePrio` hash `c29b633e71cf54c2d244eb87c7a5910a1f2973e6cd23d7a23769070b24bc2dbf` 及五次同一cpu_sr地址实参；只是人工建模身份回归，不是新前端或端口实现。

新增两个公共稳定根 `V293_critical_null_update_execution`／`V293_critical_event_update_execution`：从同一原始M的参数、表、TCB、位图／事件、可写权限和分离资源，连续执行参数guard、encrit、空新槽、SELF解析写回oldprio、真实lookup写ptcb、NULL／保留判断，运输原资源到当前版本坐标／表／ready／事件／五字段TCB后端，最后实际excrit。没有中间执行／store／scheduler完成前提；内部顺序helper有执行前提，公共根将其完整消去。终态保留同一ge／le／ks和全部局部变量，是sskip None，任意原IE／si／ci／ir恢复／保持；**尚未调用OS_Sched、return0、free或恢复caller**。

两条物理见证覆盖SELF／普通、ready／非ready、NULL／非NULL事件及任意IE／保存栈，事件字节任意合法值。初始ptcbNULL、四坐标255，实际解析8→6；ready低行按分支为80或16，高行为0，TCB五字段准确，两个表槽真正迁移；NULL事件保留物理事件块72，非NULL更新其独立事件行／group并保留原事件指针。仅同状态物理可满足，不声称完整共享不变量、API局部分配、初始化或可达性。CPU_SR字节未仿真。

规范 `audit/logs/stage26-critical-success/gate01/result.json` 的16项检查实际通过：生产／固定字面probe两次coqc与两次coqchk、完整及entry／segment／NULL／event四投影共五个不导入候选模块的正控、七个前瞻单因素负控。probe在本检查点按接口转录后独立保存、显式展开控制AST，门禁不从待测源码生成它，不是第二份独立证明。六probe根及全部正控的实际Assumptions并集仍仅classic与functional_extensionality_dep；173门禁输入保持。完整原Proof后缀保持，downstream_credit=false。

七项首拒绝人工对照冻结副本：SkipSelf／SkipLookup于521行目标Proof后577／578行的实际SelfStep／LookupStep；EnterCli、ExitSti、WrongIE于618行后630／637／638行的encrit_step／excrit_step／最终refl；WrongTCB于726行后786行Updated；WrongEvent于891行后954行EventOut。ExitSti将同一tail在程序和continuation声明的五处表示一致改为sti，确实走到末尾excrit_step，不是前面的continuation错配。只信用原脚本敏感性，不宣称修改命题不可证或前面拒绝后的下游有效。

新增9项、合计38项critical局部测试通过；完整788项仍263失败1错误，264个FAIL／ERROR标签与前轮779项逐项相同，无新增或删除。范围审计、冻结只读复核、增量构建及diff检查通过；默认make audit仍2，原因仍为旧正式函数证据身份过期。保留所有探索失败、旧断言和正式报告；没有完整旧函数门禁重放或当前1934行身份source-only全量干净构建信用。正式六门覆盖仍94／1／1／1／1／0。

逐项路径／大小／SHA复核后清理本轮15个新一次性文件，共2,480,021字节（10个Coq产品、1个Python缓存、4个生成器）；本轮开始的901个既有缓存路径全部保留，不声称字节不变。配置C及门禁专属临时树也按清单复核删除；源码、固定probe、成功／失败日志、冻结控制副本、证据、依赖和用户数据保留。见本目录cleanup-result.json及final-validation-summary.json。

本轮仍只为显式宏抽象的局部有限构造执行，不是原始sfexec／token仿真、所有并发交错、整函数Hoare或GOOD_OS。下一步沿同一成功链连接真实OS_Sched调用及其资源借还，再接能返回路径的return0／free／caller，随后补真实局部分配、共享物理关系、函数环境与初始化。GOOD_OS与同程序K1–K4未完成，uC/OS-III未启动。中文逐步说明见[成功路径如何更新数据并退出临界区](docs/开发中/成功路径如何更新数据并退出临界区.md)。
<!-- critical-success-checkpoint-end -->

<!-- critical-invalid-checkpoint-start -->
## 前一检查点（1132行历史身份）：参数非法42，检查后直接释放并返回调用者

`V293CriticalReturn.v` 保留原980行，追加152行至1132行／64,716字节，SHA256 `5b2d8a4cdf877f03a0c372290e8092e2d635a4050a66c65c00e04a8b76477d8a`。其他165活动源、12项受保护输入、固定C／配置／分析端口／框架／正式证据／覆盖及HEAD不变；仍166活动源，未提交。

`V293_invalid_critical_return` 在与40／41／67相同的显式临界前缀上，从原参数字节执行非法guard、return42求值、真正sretv／构造free／sfreeend和caller恢复，跳过任意suffix，局部字节全None、非局部块保持。构造路径只走cstep，不执行encrit／excrit，对任意IE、si、ci、ir保持原中断状态；没有中间执行／store／free oracle，不要求任务表／current／reserved／ptcb或端口函数绑定。新helper从已求值返回状态开始，未重复执行return表达式。NoDup、全局部可写和两个参数load仍是显式充分条件，不声称最小或由实际入口分配建立。

空ge的物理见证覆盖任意合法字节与非法条件，手写probe实例化(12,6)、(8,12)、(255,12)三条guard路线；保存局部四字节固定23，与IE无关。实际释放old／new各1字节、saved4字节，保留非局部哨兵23，后缀scall999被跳过且无定义前提。只是可满足物理入口，不是初始化／共享合法性／可达性证明。

`audit/logs/stage26-critical-invalid/gate01/result.json` 的10项检查通过：生产／独立literal probe两次coqc与两次coqchk、完整／隔离两个不导入候选模块的正控、四个前瞻单因素负控。三probe与两个正控的实际根假设并集仍仅classic及functional_extensionality_dep；所有门禁输入保持。WrongReturn、AdmitValidOld、WrongIE、NoWritable分别仅改结论42→43、old下界12→0、终态IE取反、全局部可写前提→True；目标Proof后首拒绝位置见result.json，完整Proof后缀保持、downstream_credit=false。只信用目标脚本敏感性，不声称修改命题不可证或前面拒绝后的下游机制有效。

新增6项、全部29项critical局部测试通过。完整779项仍263失败1错误，264个FAIL／ERROR标签集合与前轮773项逐项相同，未改旧断言或正式报告。范围审计、冻结只读复核、增量构建和diff检查通过；默认make audit仍因旧正式函数证据身份过期退出2。本轮没有新身份source-only干净全量构建或完整旧函数门禁重放信用，不能挪用980行历史快照结果。

本轮只为局部有限构造执行，不是所有交错／整函数Hoare／原始sfexec执行／token字节仿真。正式覆盖仍94／1／1／1／1／0，GOOD_OS与同程序K1–K4未完成，uC/OS-III未开始。下一步连接同一入口的成功更新、excrit、真实调度调用和成功返回，再补局部分配、物理共享关系、完整环境与初始化。中文逐步说明见[参数非法为什么不能先进入临界区](docs/开发中/参数非法为什么不能先进入临界区.md)。清理与最终身份复核记录见本目录的cleanup-result.json及final-validation-summary.json。
<!-- critical-invalid-checkpoint-end -->

<!-- critical-errors-checkpoint-start -->
## 前一检查点（980行历史身份）：同一显式临界前缀的41／67连续返回与资源运输

`V293CriticalReturn.v` 原659行逐字节保持，追加321行至980行／56,085字节，SHA256 `c00c990eeff444c280718deb072bc7b459783b3347460edb9d187671a317fb05`。其他165个活动源、12项受保护输入、固定C／配置／分析端口／框架／正式证据／覆盖及HEAD保持，仍166源，未提交。新鲜配置C物化核对同一函数hash `c29b633e71cf54c2d244eb87c7a5910a1f2973e6cd23d7a23769070b24bc2dbf` 和同一五次取地址调用；不是新前端或端口实现。

`V293_resolve_lookup_resources` 实际执行SELF解析写oldprio及lookup写ptcb，统一NULL／任意指针，无预先正确ptcb／中间执行／store oracle。put_byte及storebytes保持逐字节true权限，再从原入口资源推出返回可释放条件。`V293_lookup_error_critical_return` 为同一 `V293_primitive_critical_prefix` 的41／67稳定接口：实际guard→encrit→空新槽→SELF／lookup→NULL或reserved判断→excrit→return／free／caller恢复，对任意enabled、si、ci和未执行suffix使用同一程序；保持非局部块，全部局部字节None。absent只选入口数据与结果，不改程序；无different-slot条件排除old=new。保留符号绑定只在实际保留路径要求。NoDup／逐字节可写与地址区分是显式充分条件，不声称最小或实际API分配自动建立。

物理实例 `V293_lookup_error_critical_witness` 覆盖SELF／普通、absent／reserved及任意IE；absent解析old=new=8，reserved解析old=8/new=6；ptcb初始70而非正确NULL／90。CPU_SR局部四字节固定编码23，与IE无关，明确揭示字节擦除而非仿真。实际释放ptcb／cpu_sr各4字节、old／new各1字节，共10字节，共享旧槽保持；scall999被返回跳过且无定义要求。不是初始化／真实共享状态可达性。

规范 `audit/logs/stage26-critical-errors/gate01/result.json` 实际11项通过：生产／手写literal probe两次coqc、两次coqchk、完整／lookup投影／error投影三个不导入候选模块的正控、四个前瞻负控。三probe与三个正控的实际Assumptions并集仅既有classic与functional_extensionality_dep。所有门禁输入哈希保持。SkipSelf／SkipLookup各只把helper声明的对应待执行语句换sskip，目标Proof第541行后于583／578行拒绝；WrongReturn只对调最终41／67，目标Proof第628行后于685行拒绝；ExitSti只改primitive_error定义，同Proof后于683行拒绝。执行投影排除先前normalization／occupied根，避免早拒绝。所有原Proof后缀保持、downstream_credit=false；只信用脚本敏感性，不声称修改命题不可证或下游机制获验证。

新8测试通过，合计23项critical局部测试通过。首次局部测试有1项注释文字误匹配，记录保留；仅在该测试剥离Coq注释后复查，未改证明／控制门槛。完整773项仍263失败1错误，264个诊断标签集合与前轮逐项相同；254块为旧正式身份拒绝、10项既有断言冲突；遮蔽断言不计通过。范围审计／冻结只读复核／增量构建／diff为0，默认make audit仍2；旧完整函数门禁与旧probe未重放。

当前166源source-only独立干净构建实际通过，未复制既有产品，生成166个.vo，169项输入保持；实际耗时 923.469 秒。专属临时树逐项大小／SHA确认后删除。工作树本轮20个调试／编译缓存文件（1,457,836字节）亦经逐项确认删除，901个基线缓存路径保留，不声称其字节不变；源码、日志、物理见证与可复用依赖保留。见本轮 `clean-build-result.json`、`cleanup-result.json`、`final-validation-summary.json`。

本轮只为显式宏抽象的局部有限执行；原始sfexec无函数体时仍无下一步，未证明原token与框架栈一致仿真，也不是所有交错／整函数Hoare／整核safety。参数非法42在进入临界区前的真实返回、成功更新／调度调用／返回、实际局部分配、共享关系和初始化仍待连接。正式覆盖保持94／1／1／1／1／0，GOOD_OS与同程序K1–K4未完成，uC/OS-III未开始。见[中文逐步说明](docs/开发中/同一临界前缀的三种错误返回.md)；下一步先接42错误真实返回，再在同一抽象程序接成功后端，不假设调度或端口已返回。
<!-- critical-errors-checkpoint-end -->

<!-- critical-elaboration-checkpoint-start -->
## 前一检查点（659行历史身份）：显式中断宏抽象下，占用错误连续执行到真实返回

`V293CriticalReturn.v` 原398行保持，追加至659行／35,683字节，SHA256 `8ba9dde984c7eac06c50e8fda09675b89ec033d6d5b0e32f20b2f1d651f2e058`。其他165源哈希、12项受保护输入（含_CoqProject）、固定C／配置／分析端口／框架／正式证据／覆盖及HEAD保持；仍166源、未提交。新鲜配置后C再次物化：函数hash仍 `c29b633e71cf54c2d244eb87c7a5910a1f2973e6cd23d7a23769070b24bc2dbf`；cpu_sr初始化0，全部五个引用仅为一次进入／四次退出的同一取地址实参。这是本函数手工映射回归，不是通用逃逸分析或已验证前端。

原始调用模型及缺定义sfexec无下一步定理保留。新 `V293_port_normalize` 显式检查标记不碰撞和单个同一保存变量地址，拒绝传值／错变量／运行时节点，保持guard、SELF、查表与返回结构。归一化根核对完整前缀到已有encrit／excrit的语法映射；**擦除CPU_SR字节存取，不证明原调用执行或token内存与保存栈的仿真**。这是ADR-0001已有中断抽象边界内的另一份明确表示，不是静默替换原目标；见ADR-0005。

`V293_occupied_critical_return` 在原loststep的标准有限步闭包上，实际执行原参数guard、encrit压入原IE并关闭、占用表项判断、excrit恢复同次原IE并弹栈、return40／构造性free／caller恢复。对任意enabled、si、ci和未执行suffix使用同一程序；无中间执行／store／free oracle。局部NoDup和逐字节可写仍是显式充分条件，不是实际API入口分配或初始化已证明。它是构造性路径存在，不是所有并发交错／Hoare／整核safety结果；41／67及成功分支本轮无连续执行信用。

具体三局部物理见证覆盖SELF／普通及任意enabled，保存局部四字节刻意固定编码23——明确不可把它当原始token一致性证明。实际释放保存变量4字节及old／new各1字节，共享表占用指针保持；待执行scall999被return跳过，对任意P无999定义要求。不是共享合法性或初始化可达性。

规范 `audit/logs/stage26-critical-elaboration/gate02/result.json` 实际11项通过：生产／手写literal probe两次coqc、两次coqchk、完整／连续执行投影／归一化投影三个独立正控、四个前瞻负控。正控不导入候选CriticalReturn，仅使用原依赖；probe独立写出完整预期AST和接口。六probe根、五完整正控根及单个执行投影根的实际假设并集仅既有classic与functional_extensionality_dep，归一化投影根无假设。174项门禁输入保持。

补充投影协议在门禁前冻结，避免改原语先在归一化证明早拒绝：ExitSti／EnterCli只改对应定义，目标occupied Proof第508行后分别于541／532行拒绝；WrongReturn只改最终40→41，于543行拒绝。ValueArgument只改同一地址接受因素（两个分支），目标归一化Proof第462行后于471行拒绝。所有原Proof后缀不变，downstream_credit=false，仅信用脚本敏感性，不将拒绝当修改命题不可证或下游机制有效。gate01保留因probe缺直接导入V293_byteval定义模块而失败的记录；补齐导入后独立运行gate02，没有改门槛或控制因素。

新增8项测试通过；完整765项仍263失败1错误，264个诊断标签与前轮集合逐项相同，254块为旧正式身份拒绝、其余10项既有断言冲突。原测试、失败、正式证据均未重写，被早拒绝遮蔽断言不计通过。范围审计／冻结只读复核／增量构建／diff为0，默认make audit仍2。旧完整函数门禁／旧probe未重跑；当前166源source-only独立干净构建实际通过，未复制既有产品，生成166个.vo，169项输入保持；专属临时树按逐项大小／SHA确认后删除，不挪用旧快照信用。实际结果见本轮 `clean-build-result.json`。

任务专属12个工作树新产品（655,587字节）按路径／大小／SHA逐项确认后清理；825个基线Coq产品路径保留，不声称其字节不变。清理后15项新旧critical局部测试及diff复核通过；交付源码、文档、日志和可复用依赖保留。门禁、配置C物化和干净构建临时树分别有完整清理清单。见 `cleanup-result.json`／`final-validation-summary.json`。

下一步在同一显式抽象程序上连接41／67和成功路径，再接真实局部分配、共享关系和整函数接口；最终源码级声明仍须明确固定程序映射和端口契约。原始字节token仿真未证明；不能将两份表示的结论混用。正式覆盖仍94／1／1／1／1／0，GOOD_OS与同程序K1–K4未完成，uC/OS-III未开始。
<!-- critical-elaboration-checkpoint-end -->

<!-- critical-return-checkpoint-start -->
## 前一检查点（398行历史身份）：保存值保持、框架恢复与真实返回，尚未接通原始端口调用

新增 `V293CriticalReturn.v`，398行／21,503字节，SHA256 `ac153d62802324b65df0008a8df26a7780b9124a0274255d056f5cc2211ec5ad`。原165个活动源哈希全部不变；`_CoqProject` 仅末尾追加新模块，现166源（framework／tactics 103、v293 63）。另外11项受保护输入、固定C／配置／分析端口／框架／正式函数证据／覆盖及HEAD保持；未提交。独立重新物化配置后C与调用实参，未将手工映射说成已验证前端。

`V293_reserved_entry_preserves_saved` 从真实保留错误入口和原资源开始，实际执行SELF解析、查表、ptcb写入，到带指针的退出sfexec／return67 continuation；保存值块只额外排除oldprio／ptcb两个实际写块，证明同一出口内存保存值仍可读。不预给正确ptcb、中间执行或store结果。本轮只为reserved接保存值接口，不把occupied／absent记成也已接通。物理见证覆盖SELF／普通入口及saved真／假，不是初始化／完整共享状态可达性。

`V293_saved_ie` 的Tint32值0／1仅编码局部IE观察，不是完整CPU_SR范围或最终端口规范。`V293_excrit_restores_saved` 检查实际loststep，要求栈顶saved与该保存值一致，恢复原先true或false，内存不变；它不读取token内存，也没有证明真实进入建立此一致性。`V293_missing_port_has_no_step` 证明P中没有定义时sfexec不能小步执行。分析端口只有声明，本轮没有编造函数体、没有把sfexec换成excrit、没有假设端口执行oracle。

`V293_error_return_execution`／`V293_error_after_port_return` 从实际局部NoDup及各字节可写资源构造真实free过程，执行return值求值／sfree／恢复caller环境，所有局部字节None、非局部块保持。后者入口明确是sskip None（端口已经返回），不是sfexec；完整API局部分配可达性仍未证明。具体return67见证释放四字节保存变量和一字节局部、保持共享哨兵23，跳过pending的scall999，对任意P无函数999定义前提。另有单因素物理反例只改保存块首字节1→8、其余地址不变，破坏原保存值；不是真实C可达别名结论。

规范 `audit/logs/stage26-critical-token-return/gate01/result.json` 实际通过9项：生产／手写字面probe两次coqc、两次coqchk、隔离正控和四负控。隔离正控复制完整新源，只导入原依赖、不导入新模块本身；九probe根和八正控根实际假设并集均仅既有classic与functional_extensionality_dep。负控只改目标header：恢复结果saved→true、bs<>bc→True、最终返回error→error+1、NoDup→True，保留原Proof后全部字节；首拒绝均在指定Proof之后，downstream_credit=false。不把证明敏感性当修改命题不可证，不授早拒绝后的下游信用。169项门禁输入哈希保持。

开发失败保留；dev15／16因转换检查慢、dev17因vm_compute巨量求值，精确识别进程后主动停止，143无数学拒绝信用。最终使用显式布尔实例和四字节结构load／encode-decode证明，未改命题或弱化门禁。新增7测试通过；完整757项仍263失败、1错误，264个失败／错误标签与前轮逐项集合相同。254诊断块含旧正式身份拒绝，其余10项既有断言冲突；原测试、失败和正式证据保留，被遮蔽断言不计通过。范围审计／冻结只读复核／增量构建／diff退出0；默认make audit仍2。旧完整门禁／19probe本轮未重跑，当前166源独立source-only干净构建也未重跑，不转移旧165源构建信用。

身份、实际回归和清理分别见同目录 `identity-review.json`、`regression-comparison.json`、`validation-results.json` 与 `final-validation-summary.json`。任务专属10个新编译产品（455,714字节）按路径／大小／SHA核对后清理，清理后7项测试和diff复核均通过；既有825产品路径、交付源码／probe／测试／文档、日志和依赖保留，不声称既有缓存字节不变。

下一步必须连接同一真实调用的临界进入保存、saved内存与框架栈对应、端口调用到原语及返回桥，不能继续把孤立定理当整函数。参数段／OSRunning／调度、统一NULL／非空上层接口、共享关系／API与ISR保持性／函数环境／初始化等仍开放。源码级GOOD_OS及同程序K1–K4未完成，正式覆盖仍94／1／1／1／1／0；阶段一未完成，uC/OS-III未开始。中文教程：[退出临界区与真正返回是两回事](docs/开发中/退出临界区与真正返回是两回事.md)。
<!-- critical-return-checkpoint-end -->

<!-- error-entry-checkpoint-start -->
## 前一局部检查点（165 源身份）：从真实入口走到40／41／67三个错误退出调用

本轮程序仍227行字节不变；主proof原7265行全部保留，仅追加406行，当前7671行。其他164个活动源、12项受保护输入、固定C／配置／分析端口／框架／正式函数证据及HEAD保持；活动源仍165个、未提交。重新物化配置后C核对同一函数身份和一个进入／四个退出的`&cpu_sr`调用，不把手工映射当已验证前端。

三个稳定接口均从真实`V293_task_prio_entry_reserved`开始：occupied实际读取新槽并执行判断，不要求旧参数／ptcb／RESERVED读取，内存不变；absent通过新槽为空判断，实际SELF解析／查表／构造ptcb=NULL的store，再执行NULL判断；reserved复用真实非空查表，把实际读出的保留指针送入符号比较。最终都到`sfexec exit_id [Vptr(bs,0)] [Tptr Tint32]`，保留各自40／41／67的return及真实pending continuation。没有中间执行／store／出口oracle，不预给ptcb正确初值。absent保留13槽逐项frame；两条写路径均保留相对原内存的外部frame。

六个生产根包含三个具体物理见证，SELF与普通参数均实际实例化通用根。absent专门覆盖解析后的old=new=8，不能从成功路径错误搬入Different前提；局部ptcb初值为不同指针70，之后实际变成NULL。reserved也从指针70写成token90；occupied保持整个内存。这些不是完整共享状态／局部分配合法性／初始化可达性证明；不同kind夹具不是单因素对照。

规范门禁`audit/logs/stage26-task-prio-error-entry/gate02/result.json`实际通过12项检查：主proof完整重编、独立手写完整AST和三个字面接口、code／proof／probe三次coqchk、重新编译新增定理之前的固定前缀、隔离正控及四项单头负控。隔离依赖无六个新根且不导入候选主proof；负控分别将占用槽读取改NULL、absent最终41改40、旧表token offset改1、reserved最终67改41，均保留原proof并在指定Proof之后退出1，全部downstream_credit=false。占用槽及token offset两项资源变更可能在guard之前拒绝，不据此授予下游信用或断言变更命题不可证。探针七个检查根与隔离六根的实际假设并集均仅既有classic和functional_extensionality_dep。

初版gate01负控因移除next唯一类型约束而在头部失败，门禁如实失败，未授有效负控信用；gate02用可归约unused let维持类型推断，仍只把该负载改NULL，不修改原命题／proof或放宽Proof后拒绝门槛，全部检查重跑。开发缺直接导入的失败、dev03缺完成记录和两次巨量求值主动终止均保留；后两次143不算数学拒绝。最终用既有byte／table frame引理取代大范围求值，不改命题制造通过。

新增6项Python退出0；局部250项退出1（10失败），完整750项退出1（263失败、1错误）。264个诊断块中254含旧正式身份拒绝；其余六项历史完整程序保持／哈希、两项旧门禁文本、两项旧错误传值期待。原测试／正式证据不改，被遮蔽断言不计通过。其余26项命令逐项记录：范围审计、冻结只读复核、增量构建、diff和直接cast边界coqc／coqchk退出0，默认make audit仍退出2；19旧probe类型重编15通过、Entry／Reserved／EntryUpdate／EntryNull四项旧静态AST失败。旧完整负控门禁未重放。

**当前227／7671行身份的独立source-only干净构建实际退出0，耗时939.29秒，生成165个.vo，168项输入保持。** 仅复制活动源和三个构建入口，不带既有产品／探针／参考材料。临时构建树998项文件（165,282,571字节）逐路径／大小／SHA核对清理；两个规范门禁临时树也逐项确认清理。根工作树确认后删除99个非交付产品／一次性开发源（4,367,066字节，开发源快照保留），另清理一份本轮无用摘录；837个基线cache路径全部保留，不声称其字节不变。交付源码／probe／测试、日志、用户数据与依赖保留。实际汇总：`audit/logs/stage26-task-prio-error-entry/final-validation-summary.json`。

下一步接真实临界进入／退出与saved token／中断状态协议，再接实际return；当前不要求saved存储可读或与写块分离，不能据取地址成功声称保存值保持或恢复中断。参数段／OSRunning／调度／完整API、统一NULL／非空上层接口、RESERVED统一绑定／非冲突／前端对应、共享关系／API与ISR保持性／函数环境／初始化仍开放。源码级GOOD_OS及同程序K1–K4未完成，正式覆盖仍94／1／1／1／1／0，uC/OS-III未启动。中文教学见[从真实入口走到三个错误退出调用](docs/开发中/从真实入口走到三个错误退出调用.md)。
<!-- error-entry-checkpoint-end -->

<!-- critical-args-checkpoint-start -->
## 前一局部检查点：纠正错误退出调用，真实传入 &cpu_sr

以下为227／7265行旧proof身份记录；其原证明前缀在本轮完整重编，但不将旧完整门禁／回归记录冒称为当前身份重放。

发现并纠正手工源码模型的真实对应错误：固定分析端口声明`V293_ExitCritical(OS_CPU_SR *saved)`，宏实际传`&cpu_sr`，原模型三个错误分支却传`cpu_sr`。本轮只改程序三处实参和一处注释，仍227行；proof保留原7179行并追加86行，当前7265行。固定C／配置／分析端口／框架、其他163个活动源、八项受保护输入及HEAD保持；活动源仍165个、未提交。这不是增加第三类内核补丁。

独立命令重新物化冻结源码、运行Clang AST，核对同一60–172行函数身份、一个进入／四个退出调用的UnaryOperator &、变量unsigned int和参数OS_CPU_SR *。当前模型只含其中三个错误退出，不冒称另两个调用已建模。修复前红灯`red-02.log`完整捕获40／41／67三分支；修复后同命令退出0。最初提取器只抓两项的失败另存，不以该结果替三分支信用。根假设／字面期望仍不是已验证C前端。

稳定接口`V293_task_prio_error_exit_arguments`用真实入口AST结构等式确定两个错误分支，连同实际reserved_error一起逐步执行到`sfexec exit_id [Vptr (bs,0)] [Tptr Tint32]`，分别保留return40／41／67的continuation，内存不变。唯一执行前提是局部cpu_sr的Tint32绑定，无load／P函数定义／执行oracle。闭合空内存见证显示读值None、地址可求，直接实例化真实保留错误分支；这不是合法完整共享状态或初始化可达证明。

当前主程序和完整主proof实际重编退出0。新手写probe五个字面根、code／proof／probe三次coqchk、仅import框架／当前code／List的独立suffix正控，以及五项单因素Coq负控均完成：分别回退三个真实调用参数，或仅把通用后置实参改整数／去局部绑定。负控均保留原证明，在指定Proof之后拒绝，全部downstream_credit=false；三处程序变更可能先在结构等式拒绝，不授后续调用语义信用。假设实际并集仅既有classic与functional_extensionality_dep。初版检查器错误期待所有根零假设的失败完整保留，最终复用原有允许集合，没有增加Axiom／白名单／修改命题制造通过。

新增6项Python退出0；局部244项退出1（10失败），完整744项退出1（263失败、1错误）。264个诊断块中254含旧正式身份拒绝；其余六项历史完整程序哈希／保持断言、两项旧门禁条件文本、两项明确期待错误传值写法。原测试、旧探针、失败日志和正式证据未改写，被早拒绝遮蔽的断言不计通过。19个旧探针实际类型重编15通过、4失败（Entry／Reserved／EntryUpdate／EntryNull的旧静态AST期待传值），不宣称这些旧字面门禁仍匹配；既有成功根的原proof在当前模型下已实际重编。旧完整负控门禁未重放。

其他实际检查：范围审计／冻结只读复核／增量构建／diff和直接整数cast边界coqc／coqchk退出0，默认make audit仍退出2。本轮没有重跑当前身份的独立source-only干净构建，不借用227／7179旧身份的构建信用。

已按路径／大小／SHA核对并清理99个本轮非交付产品／一次性开发源（4,036,449字节，开发源快照保留），837个基线产品路径全部保留，不声称其字节不变；两个Coq临时树及每次C定位专用临时树均核对清理。交付源码／测试／probe、日志、用户数据及依赖保留。实际汇总：`audit/logs/stage26-task-prio-critical-args/final-validation-summary.json`。

下一步从原入口实际执行各错误guard，再连接真实临界进入／退出与保存token、中断状态的对应。当前只到调用前置边界，既未执行端口函数、恢复中断，也未执行错误返回。统一NULL／非空上层接口、OSRunning／调度／返回、共享关系／全API与ISR保持性／函数环境／初始化、源码级GOOD_OS及同程序K1–K4仍开放。正式覆盖仍94／1／1／1／1／0，阶段一未完成，uC/OS-III未启动。中文教学见[临界区退出为什么要传地址](docs/开发中/临界区退出为什么要传地址.md)。
<!-- critical-args-checkpoint-end -->

<!-- entry-null-checkpoint-start -->
以下为227／7179行旧模型身份历史；本轮纠正其未执行错误分支的实参后，旧字面probe不再匹配，不能将本节旧门禁信用转移到当前模型。

## 前一局部检查点：NULL事件成功入口连续执行93–166行

程序227行字节保持；proof在6703行后追加476行，当前7179行。其他164个活动源、八项受保护输入及HEAD保持；活动源仍165个，未提交。固定C／配置／分析端口／框架、正式函数证据与覆盖不改。重新定位同一60–172行配置后函数，保留完整入口／保留guard／坐标／独立事件if／TCB五写AST和布局。

稳定接口`V293_task_prio_entry_null_update_execution`从原始参数、表／TCB／ready、内部EventPtr=NULL、局部权限及充分分离连续执行93–166行。没有入口正确ptcb／新坐标、中间执行／store／出口oracle或old<>new前提；从空新槽与非空旧槽实际推出Different，SELF解析结果贯穿后缀。真实kseq入口产生Ma，byte／permission frame运输资源，调用新通用NULL坐标／迁移接口，最终同一Mh导出13槽、ready、TCB五字段、局部pevent=NULL／ptcb实际指针、内部EventPtr=NULL、TCB未写字节及相对最原M的外部frame。NULL路径不要求虚构事件对象或事件位图，粗frame不排除不存在的be；分离充分而非最弱。NULL根尚不提供非空根的TCB写权限后置，统一上层接口仍开放。

`V293_task_prio_entry_null_update_witness`直接实例化新通用根：原ptcb=NULL、四新坐标目的255，实际完成8→6；SELF／非SELF、ready假／真均覆盖。相对同参数旧非空物理夹具，仅内部EventPtr的四字节变成NULL，由`V293_entry_null_fixture_outside`逐地址检查其他字节相同；整个旁边事件哨兵block72最终逐地址不变，不把它变成NULL分支资源。ready假仍16／0，ready真80／0，不从EventPtr=NULL推断ready。见证只证明物理可满足性，不是完整共享合法性／初始化可达性，ready两状态不作为单因素对照。符号RESERVED仍受ADR-0004局部边界限制，统一绑定／无局部遮蔽／真实TCB不冲突／C前端对应尚未闭合。

规范门禁`run-20261028-205559/result.json`实际退出0：14项检查、三根独立手写字面接口、三次coqchk、同环境正控及四项前瞻单头负控，184项输入保持。去ptcb写权限、去内部EventPtr=NULL读取、真实程序谎称仅后缀、最终pevent谎称实际TCB指针，均保留完整原proof后缀，在指定Proof.之后拒绝，全部downstream_credit=false。只授予原证明敏感性，不宣称修改命题均不可证或下游机制通过。实际根假设并集仅classic与functional_extensionality_dep；expected从旧手写静态AST人工扩展，不读取新candidate header，但仍不是独立C前端。开发阶段缺直接导入和只rewrite一次的失败日志原样保留；修复不改命题。开发脚本是初始适配记录，不是最终手工修正版生成器，最终开发源字节另存快照。

新增10项Python退出0；局部238项退出1（5失败），完整738项退出1（258失败、1错误）。259个诊断块中254含旧正式证据身份拒绝；其余三项为历史全文件哈希冲突，两项为旧reserved／entry-update测试冻结旧门禁条件文本。实际条件增加entry_null并继续强制指定Proof后拒绝；没有改旧测试／失败／正式证据或伪造兼容字符串，被遮蔽断言不计通过。范围审计、冻结只读复核、增量构建、18个旧probe实际类型重编、直接cast边界coqc／coqchk和diff均退出0；默认make audit仍退出2。旧probe完整负控与旧补充权限probe的coqchk未重放。

**当前227／7179行身份独立source-only干净构建实际退出0，耗时930.98秒，生成165个.vo，168项输入保持。** 仅复制165个活动源和三个构建入口，不带既有产品／探针／参考材料；不沿用旧身份构建信用，也不是局部门禁的预编译闭包。临时树逐路径／大小／SHA核对清理。

已逐路径／大小／SHA确认并清理110个本轮新产品（5,098,321字节）及2个一次性开发源（35,697字节，原字节快照保留）；839个基线产品路径全部保留，不声称缓存字节不变。成功／失败日志、交付源／probe、用户数据与依赖保留；规范门禁／源码定位／独立构建临时树均核对清理。实际汇总见`audit/logs/stage26-task-prio-entry-null/final-validation-summary.json`。

下一步统一NULL／非空接口，接真实临界入口／退出、参数错误调用／参数段和OSRunning／调度／返回。统一token环境、等待／ready共享关系、全API与ISR保持性、函数环境／初始化、源码级GOOD_OS与同程序K1–K4仍开放。正式覆盖仍94／1／1／1／1／0，阶段一未完成，uC/OS-III未启动。中文教学见[NULL事件路径也要连续执行](docs/开发中/NULL事件路径也要连续执行.md)。
<!-- entry-null-checkpoint-end -->

<!-- entry-update-checkpoint-start -->
## 前一局部检查点：成功入口连续接通非空优先级迁移93–166行

以下为227／6703行旧proof身份历史记录，不表示其完整规范门禁在当前227／7179行身份重放。

程序在219行后追加8行，当前227行；proof在6330行后追加373行，当前6703行。其他163个活动源、八项受保护输入及HEAD保持；活动源仍165个，未提交。固定C／配置／分析端口／框架、正式函数证据与覆盖不改。重新定位同一60–172行配置后函数，保留入口／保留guard／坐标／事件／TCB五写AST及布局；没有将空行视为执行步骤。

稳定接口`V293_task_prio_entry_update_execution`从原始参数、表／TCB／ready／非空事件、局部权限及充分分离连续执行93–166行。入口不预给正确ptcb、新坐标、中间执行／store／出口oracle，也不假设old<>new；从空新槽、非空旧槽实际推出Different，SELF解析结果用于全部后缀资源和结果。原入口在真实后缀kseq下产生Ma，byte／permission frame运输资源，再在同一Ma上执行坐标及迁移。最终同一Mh检查13槽、ready／event、TCB五字段、局部指针、内部EventPtr及TCB未写字节；外部粗frame正确额外排除入口写块bo／bc。分离是充分条件而非最弱别名契约，含部分重复事实，不宣称整函数。

`V293_task_prio_entry_update_witness`直接实例化新通用接口：原局部ptcb=NULL，四个坐标目的值均255，实际计算并完成8→6。SELF与非SELF复用同一物理夹具，仅oldprio选择字节不同，由逐地址差异定理检查；ready假仍16／0，ready真迁移到80／0，等待不被唤醒。此见证是物理可满足性，不是合法完整共享状态或初始化可达性；ready真／假不是单因素对照。符号token继续采用ADR-0004的局部边界，统一绑定／无局部遮蔽／真实TCB非冲突及源码前端对应未自动消解。

规范门禁`run-20261028-203600/result.json`实际退出0：14项检查、三根独立手写字面接口、三次coqchk、同环境正控及四项前瞻单头负控，184项输入保持。去ptcb写权限、去入口资源隔离、程序谎称仅后缀、最终旧槽谎称仍原指针，均保留完整原proof后缀并在指定Proof.之后拒绝，全部downstream_credit=false。拒绝只说明原证明对该变更敏感，不授予下游信用或声称变更命题均不可证。三个根的实际假设并集仅classic与functional_extensionality_dep；expected复用旧手写AST并人工扩展，不从新候选header提取，不是独立C前端。开发中的缺导入／错误展开／夹具转换失败及人为终止慢tactic日志全部保留；143不算数学拒绝证据。通过缩小算术上下文改善速度，不改命题制造通过。

新增10项Python退出0；局部228项退出1（4失败），完整728项退出1（257失败、1错误）。258个诊断块中254含旧正式证据身份拒绝；其余三个为历史全文件哈希冲突，新增一个为旧reserved测试冻结了旧门禁条件文本`if entry or reserved:`，实际条件增加entry_update并继续要求指定Proof后拒绝。原测试／失败／正式报告均未改写，不据早拒绝给被遮蔽断言信用。范围审计、冻结只读复核、增量构建、17个旧probe实际类型重编、直接cast边界coqc／coqchk、diff均退出0；默认make audit仍退出2。旧probe完整负控及旧补充权限probe的coqchk未重放。

**当前227／6703行身份的独立source-only干净构建实际退出0，耗时923.58秒，生成165个.vo，168项输入保持。** 只复制165个活动源及三个构建入口，不带既有产品／探针／参考材料；不是局部门禁的预编译依赖闭包。临时树逐路径／大小／SHA核对后清理。

已逐路径／大小／SHA核对清理105个本轮新产品（4,561,988字节）及2个一次性开发源（27,765字节，原字节快照保留）；839个基线产品路径全部保留，不声称cache字节不变。成功／失败原日志、交付源码／probe、用户数据及依赖保留。规范门禁／源码定位／独立构建临时树均已核对清理；实际汇总见`audit/logs/stage26-task-prio-entry-update/final-validation-summary.json`。

下一步补NULL事件通用入口连续路径、真实临界／错误调用／参数段连接、OSRunning／调度／返回；统一token、等待／ready共享关系、全API／ISR保持性、函数环境／初始化、源码级GOOD_OS与同程序K1–K4仍开放。正式覆盖仍94／1／1／1／1／0，阶段一未完成，uC/OS-III未启动。中文教学见[把入口接到优先级迁移](docs/开发中/把入口接到优先级迁移.md)。
<!-- entry-update-checkpoint-end -->

<!-- reserved-checkpoint-start -->
## 前一局部检查点：保留标记比较与93–107行连续入口

以下为219／6330行旧身份历史记录，不表示其规范门禁在当前227／6703行身份重放。

程序在199行后追加20行，当前219行；proof在6135行后追加195行，当前6330行。其他163个活动源、八项受保护输入及HEAD保持；活动源仍165个，未提交。固定C／配置／分析端口／框架、正式函数证据与覆盖未改。重新定位同一60–172行配置后函数，保留105行实际IntegralToPointer AST及全部16处宏出现（含定义）；直接宏用法为比较／存表，未发现对宏直接解引用。

现有表达式规则不支持整数1到TCB指针的直接cast，旧边界probe仍闭合返回evaltype=None。本轮复用静态全局符号address-of表示保留token，不读内存，不删guard／不换NULL。该符号不是源C新增存储对象，不是已验证的数值地址1或C前端；全局绑定、无局部遮蔽、真实TCB与token非冲突必须由上层统一环境／共享不变量／初始化建立，当前局部接口公开这些义务。ADR-0004只接受局部表示，不授予整函数信用。

六根分别证明任意内存下符号求值、NULL／token／非冲突真实指针的三类相等、实际guard两支选择、连续成功入口、非冲突必要的值级证据、SELF／非SELF同一物理夹具的直接实例。稳定接口`V293_task_prio_entry_reserved_execution`从原始表／参数／权限资源连续执行93–107行，不要求入口ptcb正确，不给中间执行／store／比较结果oracle；原lookup在真实guard continuation下执行，再从其实际出口load通过保留判断，最终同一Mf保留原参数／两个表槽／ptcb／权限和块外frame。保留真支只到真实exit(cpu_sr);return67语句入口，不声称调用或caller返回完成。见证只证明物理可满足性，不是完整共享合法性或初始化可达性。

规范门禁`run-20261028-200048/result.json`实际退出0：14项检查、六根手写静态字面接口、三次coqchk、同环境正控与四项前瞻单头负控，182项输入保持。去全局绑定、去非冲突、程序谎称skip、最终ptcb谎称NULL，均保留完整原proof后缀并在指定Proof.之后拒绝，全部downstream_credit=false；不据早拒绝授予下游信用，不宣称四项变更命题均数学不可证。实际根假设并集仅classic和functional_extensionality_dep；字面expected不是独立C前端。开发阶段comment终止符、缺导入和展开错误的失败日志保留；无Admitted／新Axiom。

新增10项Python退出0；局部218项退出1（3失败），完整718项退出1（256失败、1错误）。257个诊断块中254含旧正式证据身份拒绝，另3项仍为NULL／NONNULL／generic历史全程序哈希冲突，旧测试／失败／正式报告未回写，被遮蔽断言不计通过。范围审计、冻结只读复核、增量构建、16个旧probe实际类型重编、diff检查退出0；默认make audit仍退出2。旧probe完整负控和旧补充权限probe的coqchk未重放。旧直接cast边界probe本轮coqc／coqchk均退出0。

**当前219／6330行身份的独立source-only干净构建实际退出0，耗时914.57秒，生成165个.vo，168项输入保持。** 只复制165个活动源与三个构建入口，不带既有产品／audit探针／参考材料；不同于局部门禁的预编译依赖闭包。

已逐路径／大小／SHA确认并清理95个本轮新产品（3,718,542字节）与1个一次性开发源（10,869字节，原字节快照保留）；839个基线产品路径全部保留，不声称缓存字节不变。规范门禁、源码定位、独立构建临时树各自核对清理；成功／失败原日志、交付源码／probe、用户数据与依赖保留。实际汇总见`audit/logs/stage26-task-prio-reserved/final-validation-summary.json`。

下一步将成功入口接实际坐标计算／迁移后缀，再补完整临界／错误调用／OSRunning／调度／返回；统一token与真实TCB非冲突、等待／ready共享关系、全API／环境／初始化、源码级GOOD_OS与同程序K1–K4仍开放。正式覆盖仍94／1／1／1／1／0，阶段一未完成，uC/OS-III未启动。中文教学见[区分保留标记与真实任务指针](docs/开发中/区分保留标记与真实任务指针.md)。
<!-- reserved-checkpoint-end -->

<!-- entry-checkpoint-start -->
## 前一局部检查点：参数检查、SELF解析与真实任务表读取

以下为199／6135行旧身份历史记录，不代表其门禁在当前219／6330行身份重放。

程序在166行后追加33行，当前199行；proof在5711行后追加424行，当前6135行。其他163个活动源、八项受保护输入及HEAD保持；活动源仍165个，未提交。固定C／配置／分析端口／框架、正式函数证据及覆盖未改。重新定位同一60–172行配置后函数，保留完整入口Clang AST、源码及布局；冻结默认只读复核退出0。

`V293_task_prio_argument_execution` 对全部字节输入给出实际83–89行执行：old<12或SELF255且new<12则skip且内存保持，否则实际求值错误42；非法路径停在kret下返回value，不声称释放局部或调用方返回。`V293_task_prio_argument_accepts`提供成功接口。

`V293_task_prio_entry_lookup_execution` 从实际入口资源执行93–104成功路径：新槽空检查、SELF时从全局OSTCBCur读取实际Prio字段并写oldprio、真实旧槽load写ptcb、NULL判断假支。没有入口正确ptcb load、中间执行／store／出口oracle；四字节store由权限构造。current资源只在old=255下需要。空new槽和非空old槽实际推出resolved<>new，最终同一Mf保留参数／两个表槽、ptcb读回、写权限与块外frame。new仍<12；SELF解析后的resolved<13是表容量，不把输入限制机械套给解析结果，细化理由先于规范门禁记录。

`V293_task_prio_entry_witness` 用同一程序／夹具的SELF与非SELF两支直接实例化新接口；入口ptcb均NULL，出口才成为真实表中指针。两个入口仅差oldprio选择字节，逐地址差异由`V293_entry_fixture_delta`证明。它只是物理资源可满足性，不是完整共享状态或初始化可达性；参数段和93–104段分别给执行，不用人为组合跳过92行而冒称连续整函数。

规范门禁`run-20261028-193725/result.json`实际退出0：14项检查、三根手写静态字面接口、三次coqchk、同环境正控及四项前瞻单头负控，182项输入保持。删ptcb写权限、删真实旧槽load、程序谎称skip、最终ptcb谎称NULL，均保留完整原proof后缀，在指定新定理Proof.之后拒绝；全部downstream_credit=false，不据早拒绝授予下游信用。首次运行的skip负控因未使用参数类型推断而在声明头部早拒绝；已保留该报告、不授予语义信用，给原参数补显式类型并加强门禁为必须在Proof.后拒绝，再按当前身份重跑全部本轮检查。实际根假设并集仅classic与functional_extensionality_dep，字面expected不是独立C翻译器。

新增10项Python退出0；局部208项退出1（3失败），完整708项退出1（256失败、1错误）。257个诊断块中254含旧正式证据身份拒绝，另3项为NULL／NONNULL／generic历史全程序哈希冲突；此次程序追加新增generic身份冲突。原测试／失败日志／正式证据均保留，被遮蔽断言不计通过。范围审计、增量构建、15个旧probe实际类型重编、diff检查退出0；默认make audit仍退出2。旧probe完整负控未重放，旧补充权限probe未重放coqchk。**本轮未运行当前身份的独立source-only干净构建，不沿用上一身份信用。**

补充边界probe的coqc／coqchk实际退出0、根闭合：非零整数转TCB指针的evaltype=None。这说明105行RESERVED表达式尚不能由现有表达式类型规则处理，不证明源码有错，不改框架，也不把该条件删掉／换NULL来制造整函数通过。临界入口、错误exit调用、RESERVED、与110–166后缀的连续连接、OSRunning／调度／返回仍开放。

已逐路径／大小／SHA确认并清理90个本轮新产品（3,760,092字节）及1个一次性开发源（25,714字节，完整源码快照保留）。839个基线产品路径全部保留，不声称缓存字节不变；规范门禁与源码定位各自临时树已核对清理。成功／失败原日志、交付源码／probe、用户数据及依赖保留，实际汇总见`audit/logs/stage26-task-prio-entry/final-validation-summary.json`。

下一步先解决保留指针的忠实语义连接，再接完整临界／错误／后缀／返回，继续等待／ready共享关系、全API／环境／初始化、源码级GOOD_OS与同程序K1–K4。正式覆盖仍94／1／1／1／1／0，阶段一未完成，uC/OS-III未启动。中文教学见[入口检查与真实任务指针读取](docs/开发中/入口检查与真实任务指针读取.md)。
<!-- entry-checkpoint-end -->

<!-- generic-update-checkpoint-start -->
## 前一局部检查点：任意参数的坐标计算接通非空连续迁移

以下为166／5711行旧源码身份的历史记录，不代表其门禁已在当前199／6135行身份重放。

程序166行字节保持，仅在proof5441行后追加270行，当前5711行；其他164个活动源、八项受保护输入、HEAD不变，活动源仍165个，未提交。未改固定C／配置／分析端口／框架、正式函数证据或覆盖；使用已定位且身份不变的同一110–166行程序，冻结只读复核退出0。

`V293_task_prio_coordinates_update_execution` 对old／new、入口内存、地址及表／位图参数全称量化，不再仅有8→6连续见证。入口移除预先正确的新坐标局部与X索引load，只保留原内存实际资源、四绑定／权限和充分分离；真实四赋值产生Mc，再由byte／permission与load frame运输表、TCB、ready／事件资源，构造后缀新坐标并调用原通用后缀，组成同一次执行。无中间执行／成功store／出口读回或后缀资源oracle。最终同一Mh导出13槽、ready／event、五字段、ptcb／pevent、内部EventPtr及TCB未写字节；外部粗frame正确排除四个新写局部块，不声称最弱分离或精确四地址frame。

`V293_generic_coordinate_update_witness` 直接调用新通用接口，在同一四目的均255物理入口完成执行；不借旧连续见证出口或坐标恢复等式，排除契约空洞。其具体8→6只是可满足性见证，通用性来自全称定理；不声称完整共享状态合法或初始化可达。old/new<13仍只是片段容量，完整API的newprio<12 guard、NULL路径通用组合仍开放。

规范门禁`run-20261028-185451/result.json`实际退出0：14项检查、两根手写静态字面接口、三次coqchk、同环境正控与四项前瞻单头消融；181项输入保持。删目的写权限、删资源隔离、程序谎称仅后缀、最终内部EventPtr谎称NULL，均保留完整原proof后缀，在新定理5444–5611行内拒绝，全部downstream_credit=false；不据早拒绝授予下游信用。实际假设并集仅classic与functional_extensionality_dep；字面expected不是独立C前端，人工对应信任边界保留。

新增8项Python退出0；局部198项退出1（两项旧全程序哈希失败），完整698项退出1（255失败、1错误）。256个诊断块中254含旧正式证据身份拒绝，另两项为上一轮已存在的NULL／NONNULL frame历史全文件哈希冲突。旧测试、失败日志和正式证据均未改写，被遮蔽断言不计通过。范围／冻结审计、增量构建、14个旧探针实际类型重编和diff检查退出0；默认make audit仍退出2。旧探针完整负控与补充权限probe的coqchk未重放。**本轮未重跑独立source-only干净构建，上一轮904秒结果不转移到新proof身份。**

已逐路径／大小／SHA确认后清理86个本轮新产品（3,903,947字节）及2个一次性开发源副本（21,562字节）；源码副本原字节保留为日志快照。838个基线产品路径全部保留，不声称缓存字节保持。规范门禁临时树也由脚本逐路径核对清理。清理后源码追加、其他164源、八项受保护输入、HEAD、规范门禁及Python输入保持；原始记录和汇总见`audit/logs/stage26-task-prio-generic-update/`。

下一步补完整参数／任务guard、self处理与表读取，连接临界区退出／OSRunning／调度／返回，再完成等待／ready共享关系、全API／环境／初始化、源码级GOOD_OS及同程序K1–K4。正式覆盖仍94／1／1／1／1／0，uC/OS-III未启动。中文教学见[把坐标计算接成通用优先级迁移](docs/开发中/把坐标计算接成通用优先级迁移.md)。
<!-- generic-update-checkpoint-end -->

<!-- coordinates-checkpoint-start -->
## 前一局部检查点：实际计算四个新坐标，再接连续迁移

以下为166／5441行旧源码身份的历史记录；该183项门禁和独立干净构建不代表当前5711行proof已重放。

本步保持旧源码字节前缀，在程序145行后追加21行，在proof5118行后追加323行，当前分别166／5441行；固定C、配置、分析端口、框架、正式函数证据／覆盖和其他163个活动源保持。活动源仍165个，HEAD不变，工作树未提交。

`V293_task_prio_coordinates_execution`从newprio真实读取、四局部绑定／写权限和充分分离，构造源码110／111／116／117行的四次实际赋值，不要求旧目的值正确，不以成功store／中间执行／出口结果为前提。导出Y／X／BitY／BitX、源保持和四地址外byte／permission frame。0..12的有限算术另核对有符号／逻辑右移相等；固定13槽容量仍不代替完整API的newprio<12 guard。

四旧局部均255的物理入口经实际四赋值恢复旧后缀入口，逐地址证明恢复等式，再接同一表／TCB读／ready／非空事件／五写后缀，实际连续执行配置后110–166行。最终同一内存检查13槽、位图、五字段、pevent／ptcb、内部EventPtr和TCB未写字节。通用接口仅四赋值；连续见证固定8→6、非空事件，不冒称任意参数通用整函数、合法完整共享状态或初始化可达。等待例子ready仍16／0，修改优先级不会收到消息。

当前实现coqc退出0，新增8项Python退出0；局部190项退出1（两项旧全文件哈希断言失败），完整690项退出1（255失败、1错误）。256个诊断块中254含旧正式证据身份拒绝，另两项明确为NULL／NONNULL frame历史测试冻结整个145行程序，与本次追加冲突。原测试、失败日志和旧报告均保留，不缩小断言、不删不利结果。默认make audit仍退出2；范围／冻结审计、增量构建和13个旧探针实际类型重编退出0。旧探针完整负控及补充权限探针coqchk未重放，不授予该信用。

规范门禁`run-20261028-182707/result.json`实际退出0：14项检查、四根手写字面接口、三次coqchk、同环境正控和四项单头负控。删写权限、删源隔离、程序谎称skip、X索引谎称掩码，均保留完整原proof后缀并在指定声明5189–5281内拒绝，全部downstream_credit=false；不据早拒绝授予下游信用、不声称分离最弱。183项输入保持；实际假设并集仅classic与functional_extensionality_dep，算术根闭合。**本检查点165源独立source-only干净构建实际退出0，生成165个.vo，耗时904.12秒，168项输入结束时哈希保持。** 只复制活动源和三个构建入口，不带既有产品／audit探针／参考材料，不把局部门禁的预编译依赖闭包冒充干净构建。已逐路径／大小／SHA确认后清理80个新探针产品（3,370,413字节）和4个一次性副本／新cache（73,313字节，三份开发源码保留为原字节日志快照）；827个基线产品路径全部保留，不声称cache字节不变。规范门禁树24文件／16,701,726字节、源码定位树19文件／664,994字节、独立构建树998文件／162,506,709字节均已逐路径核对清理。最终汇总脚本实际退出0；清理后两源追加、其他163源、八项受保护输入、HEAD、183项门禁输入、168项构建输入及Python输入全部保持，见本目录`final-validation-summary.json`与`post-cleanup-integrity.json`。前瞻协议、开发失败、实际测试见`audit/logs/stage26-task-prio-coordinates/`；入门见[从新优先级实际算出坐标](docs/开发中/从新优先级实际算出坐标.md)。

仍须补完整参数／任务guard、通用连续组合、临界区入口／退出、OSRunning／调度／返回、等待／ready共享关系、全API／函数环境／初始化、源码级GOOD_OS及同程序K1–K4。正式覆盖仍94／1／1／1／1／0，uC/OS-III未启动。
<!-- coordinates-checkpoint-end -->

## 前一局部检查点：非空连续路径显式保持内部 EventPtr 和未写 TCB 字节

以下为上一源码身份的历史检查点；其中“本步／当前”均指当时，不表示其182项门禁或测试报告适用于最新166／5441行源码。

本步只在既有proof的4814行后追加304行，当前5118行；程序AST保持145行及原字节，其他164个活动源、八项受保护输入、HEAD、固定C／配置／分析端口／框架／正式证据／覆盖保持。仍为62个V293和103个通用活动源，工作树未提交；重新定位完整冻结函数、事件读取／独立if／五赋值的Clang AST和布局。

`V293_task_prio_prefix_event_update_preserves` 入口与旧非空连续接口完全相同，从实际前缀和五写的frame导出最终同一Mh中：TCB内部EventPtr仍为原非空指针，50..54以外每个byte与入口相同，同时保留原13槽、ready、事件、五字段、pevent／ptcb及权限后置。内部字段不是从局部pevent反推，不引入中间执行／成功store／出口资源oracle。实际DelReq偏移55属于泛用保持范围，但本夹具未新增带值DelReq哨兵，不冒称单独实例检查。

强化见证复用完全相同的旧物理入口，四组实际执行覆盖ready假／真、事件旧行非空、高位保持。8→6五字段仍6／0／6／1／64；等待ready16／0保持，不因改优先级唤醒。这些是物理资源可满足性，不是合法完整共享状态或初始化可达；ready真／假还改变行和组，不当作单因素消融。旧接口／证明和既有测试未改写。

规范门禁 `audit/logs/stage26-task-prio-nonnull-frame/run-20261028-175413/result.json` 已退出0：14条实际检查、三根手写字面接口／实际假设、三次`coqchk`、同环境正向重编及四项单头负控。删除TCB／事件块隔离、内部EventPtr谎称NULL、frame错误包含Prio写字节、连续程序谎称只有五写，均保留完整原proof后缀，并在指定声明4817–4980内拒绝；全部downstream_credit=false，不据早拒绝给下游信用，也不声称块分离最弱。182项门禁输入保持，实际假设并集仅classic与functional_extensionality_dep；字面探针不是独立C翻译器，人工源码对应的信任边界仍保留。

182项局部Python退出0；全套实际执行682项，253失败、1错误，退出1。254个诊断块均含旧正式证据身份拒绝，不给被遮蔽的下游断言信用。项目范围审计／冻结默认只读复核退出0，默认`make audit`仍退出2，增量构建退出0。12个旧探针在本次源码上重编均退出0，仅记类型兼容；未重放各自完整负控，旧物理权限消融探针也未重放其补充`coqchk`。未刷新正式证据或覆盖，不沿用前轮报告输入身份。

**本检查点165源的独立source-only隔离干净构建退出0，实际生成165个 `.vo`，耗时902.79秒，168项输入结束时哈希保持。** 只复制活动源及三个构建入口，不带既有编译产品、audit探针或参考材料；这次实际运行独立于局部门禁的预编译依赖闭包。

逐路径／大小／SHA核对后，删除65个新探针产品（2,639,821字节），保留全部827个既有产品路径，不声称缓存字节不变。规范门禁临时树24文件／15,567,949字节、源码定位临时树19文件／664,994字节、独立构建临时树998文件／162,175,475字节均已核对清理；本步实现使用stdin，没有另行落地需删除的一次性拼接脚本。源文件、旧快照、可复用依赖、用户材料及全部成功／失败日志保留。清理后确认proof仅追加、其他164源、八项受保护输入、HEAD、182项门禁输入、168项构建输入和Python输入保持；实际汇总见本目录 `final-validation-summary.json`，不是完整API或整核验收。

下一步连接新坐标的实际四次计算／赋值，再处理完整参数／任务guard、临界区退出／OSRunning判断／调度／返回、等待／ready共享关系、全API／环境／初始化、源码级`GOOD_OS`及同程序K1–K4。13槽片段不代替完整API的`<12` guard；正式覆盖仍 `94 / 1 / 1 / 1 / 1 / 0`，uC/OS-III未启动。前瞻协议、对抗复核和原始日志见 `audit/logs/stage26-task-prio-nonnull-frame/`；中文入门见[非空路径也要保留TCB内部字段](docs/开发中/非空路径也要保留TCB内部字段.md)。

## 前一局部检查点：同一程序的空事件路径接通五字段并保持未写 TCB 字节

以下为前一源码身份的历史检查点；其中“当前／本轮”均指当时，不表示该182项输入报告已在本轮新proof上重放。

活动程序AST保持145行且字节不变，仅在既有proof的4510行后追加304行，当前4814行；其他164个活动源、八项受保护输入、HEAD保持。固定C／配置／分析端口／框架／正式函数证据／覆盖均未改动，仍为62个V293和103个通用活动源，工作树未提交。重新定位同一完整函数，取得事件读取及独立`!=`条件、五赋值的实际Clang AST和TCB布局；源码定位的首次条件筛选失败与后续成功日志均保留。

稳定接口 `V293_task_prio_prefix_null_update_execution` 从同一入口连续执行配置后119–166行的空事件路径。执行的仍是既有 `V293_task_prio_prefix_event_update`，不是专为NULL改造的skip：真实if为假而跳过原非空体，其后五字段照常写回。旧前缀仅在Mf导出操作数，新证明通过实际pevent存储的frame运输到Me，并从入口运输newprio、X索引、指针及权限；不接受中间执行／成功store／出口资源oracle。最终同一Mh同时检查13槽、旧槽空／新槽原指针、ready位图、TCB五字段、pevent=NULL、TCB内部EventPtr仍NULL，以及TCB偏移50..54以外全部byte保持。后两项不是从局部pevent反推，且**只给本新NULL接口信用**；旧非空连续接口的内部TCB保持后置仍开放。

`V293_null_update_entry_delta` 证明新夹具只在原非空入口覆盖EventPtr四字节编码，其他地址完全相同；固定live=false的NULL／非空对照执行完全同一程序。NULL出口整个物理事件块72逐字节不变，非空对照仍实际迁移事件0／1→64／0；TCB五字段均为6／0／6／1／64，X索引6不是BitX掩码64。NULL两条实际见证涵盖ready假／真：16／0保持16／0，或迁移为80／0。ready真／假入口还改变行和组，不当作单因素消融；夹具只证明资源可满足，不声称完整共享状态合法、初始化可达，NULL等待用例也不声称正在某个具体事件上等待。改优先级没有收到消息，不能据此宣布任务解除等待。

规范门禁 `audit/logs/stage26-task-prio-null-update/run-20261028-173430/result.json` 退出0：14条实际检查、四根手写字面接口／实际假设、三次`coqchk`、同环境正向重编及四项单头负控。删除入口EventPtr=NULL读取、删除指针局部／TCB块隔离、连续程序谎称只有五写、最终pevent谎称非空，均保留完整原proof后缀，并在指定声明4514–4666内拒绝；全部downstream_credit=false，不据早拒绝给下游信用，也不声称粗块分离最弱。182项输入保持，实际假设并集仍仅经典逻辑与依赖函数外延性。字面探针不是第二套独立C前端，人工建模信任边界保留。

174项局部Python退出0；全套实际执行674项，253失败、1错误，退出1。254个诊断块均包含旧正式证据身份拒绝，不授予被遮蔽的下游断言信用。项目范围审计／冻结默认只读复核退出0，默认`make audit`仍退出2，增量构建退出0。旧11个探针在当前源码重编全部退出0，只记类型兼容；未重放各自完整负控，其中旧物理权限消融探针也未重放其补充`coqchk`。开发失败和完整测试失败日志均保留，不刷新正式证据或覆盖。

**当前165源的独立source-only隔离干净构建已退出0，实际生成165个 `.vo`，耗时901.16秒，168项输入结束时哈希保持。** 只复制活动源与三个构建入口，不带既有编译产品、audit探针或参考材料；不沿用前一轮身份，也不将局部门禁的预编译依赖闭包当作干净构建。

逐路径／大小／SHA核对后，删除60个新探针产品（2,326,240字节），保留全部827个既有产品路径，不声称缓存字节不变。规范门禁专属临时树24文件／14,440,960字节；最后一次成功源码定位的临时树19文件／664,994字节；隔离构建临时树998文件／161,900,523字节，均已核对清理；一次性实现拼接工具也已清除。源文件、旧快照、可复用依赖、用户材料及全部成功／失败日志保留。清理后确认proof追加、程序AST与其他164源、八项受保护输入、HEAD、182项门禁输入、168项干净构建输入及Python输入保持；机器汇总见本轮 `final-validation-summary.json`。

下一步补非空连续接口的内部TCB保持，再处理完整参数／任务guard、新坐标实际计算、临界区退出／调度／返回、等待／ready共享关系、全API／环境／初始化、源码级`GOOD_OS`和同程序K1–K4。13槽片段容量不代替完整API的`<12` guard。覆盖仍为 `94 / 1 / 1 / 1 / 1 / 0`，uC/OS-III未启动。前瞻协议、对抗复核及原始日志见 `audit/logs/stage26-task-prio-null-update/`；中文入门见[空事件路径仍要写回TCB](docs/开发中/空事件路径仍要写回TCB.md)。

## 前一局部检查点：非空事件连续前缀接通 TCB 五字段写回

以下保留该源码身份的历史记录；其中“本轮／当前”指当时检查点，不表示其181项输入报告已在本轮新源码上重放。

本轮在既有 code 的130行后追加15行、proof的4023行后追加487行，分别为145／4510行；原字节前缀保留，其他163个活动源、八项受保护输入及HEAD不变。固定C／配置／分析端口／框架／正式函数证据／覆盖未修改，工作树未提交。仍为62个V293、103个通用活动源。重新从同一授权修复后的冻结源码取得完整函数身份、实际Clang五赋值AST及TCB布局。

`V293_task_prio_tcb_update_execution` 从真实指针、操作数读取和五个目的字节写权限构造源码162–166行的顺序写入：Prio／Y／X／BitY／BitX，对应偏移50／52／51／54／53。旧目的值无需预先正确，也不以成功store或后缀执行为前提。`xi` 是位索引，`xn` 是位掩码；8→6的最终字段分别为6／0／6／1／64，不能把X写成64。五写接口导出50..54之外的细粒度byte frame。

`V293_task_prio_prefix_event_update_execution` 从同一入口资源连续执行119–166行的配置后非空路径：两表写→三旧局部读取→ready判断→事件读取及非空迁移→五字段。新增索引、newprio、TCB指针与权限从入口通过实际frame运输，不接受中间出口资源oracle；最终在五写后的同一Mh检查完整13槽、旧槽空／新槽原指针、ready／事件位图和TCB五字段。Multi-Pend已关闭，143与162之间没有配置后语句。连续接口当前只导出TCB整块外的粗frame，**尚未显式导出TCB内部EventPtr等全部未写字段的保持后置**，不能用pevent局部读回代替它。

同一物理入口含五个旧字段8／1／0／2／1及新索引6、掩码64。四组真实执行覆盖等待、ready真支、旧事件行非空、高位保持。等待用例ready16／0始终16／0，事件0／1→64／0；迁移不会收到消息或唤醒任务。ready真用例只说明物理资源可满足，不声称完整等待／ready抽象状态合法或初始化可达；真／假入口也改变组值，不当作单因素消融。

规范门禁 `audit/logs/stage26-task-prio-tcb-update/run-20261028-170910/result.json` 退出0：14条实际检查、四个手写字面根接口／实际假设、三次 `coqchk`、同环境正向重编及四项单头负控。去写权限、去操作数／TCB隔离、程序谎称skip、最终X额外谎称掩码，均保留完整proof后缀并在指定声明4105–4188内拒绝，全部downstream_credit=false；不声称粗块分离必要或最弱。181项输入保持，假设并集仍仅经典逻辑与依赖函数外延性。字面探针不是独立C翻译器，人工建模信任边界保留。

另行检查一个物理消融：只把第一目的字节的permission从true改为false，旧Byte8及其余地址不变，同一个真实byte store由Some变为None；补充探针的coqc／coqchk退出0。它不是五写小步执行或整函数反例，不计入规范四根／四负控。

166项局部Python退出0；全套实际执行666项，253失败、1错误，退出1。254个诊断块均含旧正式输入身份拒绝，不授予被遮蔽的下游断言信用。范围审计、冻结默认只读复核退出0；默认 `make audit` 仍退出2。旧九探针在当前源码重编全部退出0，未重放各自完整负控；增量构建退出0。原始失败／成功日志均保留，不刷新正式证据或覆盖。

**当前165源的独立隔离干净构建已退出0，实际生成165个 `.vo`，168项输入结束时哈希保持。** 只复制活动源与三个构建入口，不带既有产品、audit探针或参考资料；见本轮 `clean-build-result.json`。不沿用前一轮身份，也不将局部门禁的预编译依赖闭包算成干净构建。

逐路径／大小／SHA确认后删除55个本轮新探针产品、2,010,517字节，全部827个既有产品路径保留，不声称缓存字节不变。规范门禁专属树清理24文件／12,797,967字节；源码定位树19文件／664,994字节；隔离构建树998文件／161,506,573字节；一次性实现拼接脚本已清除，源与旧快照保留。所有开发失败、负控拒绝、完整测试失败日志及用户材料保留。最终汇总脚本最初把“未声称缓存字节不变=false”的报告字段误当成必须为true的完整性检查，已精确排除此声明并单独断言其为false；实际失败日志保留，未改任何证明门禁或不利结果。清理后确认两源追加、其他163源、八项受保护输入、HEAD、181项规范输入、168项干净构建输入和补充／Python输入保持；机器汇总为本轮 `final-validation-summary.json`。

下一步先连接空事件前缀与五写，再补TCB内部未写字段保持性、完整参数／任务guard与新坐标计算、临界区退出／调度／返回、等待／ready抽象共享关系、全API／函数环境／初始化、源码级 `GOOD_OS` 及同程序K1–K4。13槽片段范围不代替完整API的`<12` guard。覆盖仍为 `94 / 1 / 1 / 1 / 1 / 0`，uC/OS-III未启动。前瞻协议、对抗复核及机器汇总见 `audit/logs/stage26-task-prio-tcb-update/`；中文入门见[把TCB五字段接到连续优先级迁移](docs/开发中/把TCB五字段接到连续优先级迁移.md)。

## 前一局部检查点：表写／TCB读取／ready／非空事件已接成同一次执行

本轮仅在既有 `V293TaskPrioRekey.v` 的3712行后追加311行，当前4023行；其他164个活动源（含真实程序AST）、八项受保护输入、固定C／配置／分析端口／框架／正式函数证据／覆盖均不变。仍为62个V293和103个通用活动源，HEAD及未提交开发态保留。再次重建授权修复后的固定源码并定位同一完整函数、Clang事件AST和布局，没有换版本或把其他修复纳入范围。

稳定接口 `V293_task_prio_prefix_event_nonnull_execution` 连续执行119–143行：入口M → 两次表写M1/M2 → 三旧局部读取Mr → ready分支Mf → 事件指针赋值Me → 非空字段更新Mg。事件字节、目的四字节权限和TCB字段经前缀frame运输到实际Mf；六局部由真实前缀输出取得。没有中间成功store／后缀执行／出口读回前提。最终 **Mg** 同时观察完整13槽、旧槽空／新槽TCB指针、ready和事件两行／组、六局部、pevent及范围外frame，不再把两个各自正确的片段当作已连接。

同一物理入口见证包含13槽、真实TCB指针和旧字段、初值255的旧目的局部、三个新局部、ready／事件位图及错误pevent初值。四组真实连续执行都将8改为6：等待入口ready16/0保持16/0，事件0/1→64/0；ready真入口16/1→80/0且事件同样迁移；等待入口事件16/3→80/2；未操作高位0/129→64/128。事件等待位迁移不表示收到消息或被唤醒。ready真用例只证明程序资源可满足，不声称合法等待／ready共享状态或初始化可达；真／假入口还改变ready组，不冒称单因素消融。

规范门禁 `audit/logs/stage26-task-prio-event-prefix/run-20261028-163530/result.json` 退出0：14条实际检查、三个手写字面根接口／真实假设、三次 `coqchk`、同环境正向重编和四项单头负控。分别删事件写权限、删事件／ready行块隔离、连续程序谎称只有事件后缀、最终旧表槽谎称仍有指针，完整原proof后缀均保留，并在指定声明内拒绝，全部downstream_credit=false。181项输入哈希全程保持；假设并集仍仅经典逻辑与依赖函数外延性。负控只显示当前证明依赖，不证明粗块分离必要／最弱；字面探针也不是独立C翻译器。

158项局部Python通过；完整实际运行658项，253失败、1错误。254个诊断块均包含旧正式证据身份拒绝，不授予被遮蔽的下游检查信用。项目范围审计和冻结默认只读复核退出0；默认 `make audit` 仍退出2，未刷新正式证据或覆盖。旧八探针在当前源码实际重编均退出0，未重放各自完整负控，历史报告不继承新身份。增量构建退出0。

**当前165源的独立隔离干净构建已退出0，实际生成165个 `.vo`，168项输入哈希保持。** 仅复制活动源码和三个构建入口，不带既有编译产物、audit探针或参考资料；见本轮 `clean-build-result.json`。这是单独实际运行，不沿用前一轮身份，也不把局部门禁的预编译依赖闭包当成干净构建。

逐路径／大小／SHA核对后，删除45个本轮新探针产品（1,643,934字节），保留全部827个基线产品路径，不声称缓存字节不变。规范门禁专属临时树已清理24文件／11,412,474字节；源码定位临时树19文件／664,994字节；隔离构建临时树998文件／160,864,289字节。源文件、用户数据、可复用依赖及全部成功／失败日志保留，无来源基线的缓存不推测删除。清理后再次确认3712行原前缀、其他164源、八项受保护输入、HEAD、181项门禁输入和168项干净构建输入保持；没有新增禁用证明占位。机器汇总见本轮 `final-validation-summary.json`，不是完整函数或最终整核报告。

完整函数仍开放：TCB五个物理字段162–166行尚未写入，此刻不是API返回点，不能宣布共享不变量恢复；13槽片段容量不代替完整guard的`<12`范围。随后还有guard、临界区／调度、等待／ready抽象共享不变量、全API／环境／初始化、源码级`GOOD_OS`与同程序K1–K4。覆盖保持 `94 / 1 / 1 / 1 / 1 / 0`，uC/OS-III未启动。前瞻协议、对抗复核和原始成功／失败日志见本轮目录；中文教学见[把等待分支接到同一次优先级迁移](docs/开发中/把等待分支接到同一次优先级迁移.md)。

## 前一局部检查点：真实非空事件字段写入，接通读取／if／THEN

本步只在既有 `V293TaskPrioRekey.v` 追加；前 3049 行字节保留，其他 164 个活动源（含已存在的真实事件 AST）、八项受保护输入、固定 C／配置／端口／框架／正式函数证据／覆盖均未修改。仍为 62 个 V293 和 103 个通用活动源，工作树未提交。重新重建授权修复后的配置源码，核对同一完整函数记录及 Clang 字段、if AST 和布局，没有更换源版本。

`V293_task_prio_event_then_execution` 从真实 pevent 指针、事件基址、Grp／两行入口读取、三个字节写权限和六局部操作数，构造实际字段地址及顺序小步执行：清旧行 → 根据刚写出的行决定是否清旧组 → 置新组 → 置新行。出口证明行组一致、指针及局部读取保持，以及事件基址+10..12以外的逐字节frame。真实字段数组不是全局 ready 表；不假设成功中间执行／存储或出口读回。

稳定接口 `V293_task_prio_event_nonnull_execution` 连接第135–143行的实际 TCB事件指针读取、四字节目的赋值、typed-null非空判断和字段THEN。事件资源与局部从同一实际中间内存Me通过frame导出，不接受后缀执行oracle。前面的两表写／TCB读取／ready前缀到本非空片段的总连接**仍开放**；此前连续空路径不受修改，但两个独立接口并不自动合成整函数。

同一具体入口同时具有真实指针编码、事件行组及权限、六操作数和ready表。事件指针基址5，Grp偏移15、两行16／17；pevent目的初始值故意为另一指针块71偏移3，执行后读回块72偏移5。四组实际执行涵盖跨行 `0/1→64/0`、同行 `0/1→0/4`、旧行非空 `20/0→80/0`、未操作高位 `0/129→64/128`，同时ready行组始终16／0／1。等待记录迁移不表示收到消息或变为ready。它们是边界用例，不冒称任意两项只改变一个物理字节的消融，也不是完整结构分配／初始化可达性。

规范门禁 `audit/logs/stage26-task-prio-event-body/run-20261028-161206/result.json` 退出0：14条实际检查、七根静态字面接口／真实假设、三次 `coqchk`、同环境正向重编和四项单头部负控。删除写权限、真实行地址11谎称10、真实THEN谎称skip、跨行出口旧位谎称仍置位，均保留原证明后缀并在指定声明内拒绝；不授予下游信用。182项输入在门禁及清理后哈希不变，假设并集仍仅经典逻辑与依赖函数外延性。字面探针不是独立C前端，人工建模信任边界保留。

原始指针首字节覆盖控制仅证明“任意写地址”的泛用frame缺少限制时会失败，**不是实际事件字段写入的反例**。真实字段偏移至少10，和指针局部0..3可在同块而不重叠；本接口仍用足够的块隔离，不宣称其必要或最弱。验收前已在 `SCOPE_REFINEMENT.md` 限定这一主张。旧null静态测试原先禁止整个文件存在未来非空定理，现只检查其自身null控制范围；没有改动旧Coq接口或旧负控来制造通过。

152项局部Python通过；完整实际运行652项，253失败、1错误，全部254个诊断块包含旧正式证据身份拒绝，不给被遮蔽的下游检查信用。项目范围审计、冻结源码默认只读复核退出0，默认 `make audit` 仍退出2。旧七探针（表写、值级、物理THEN、TCB、读取／ready、连续前缀、事件空路径）在当前源实际重编全部退出0，但未重跑其完整负控门禁，旧报告不自动继承当前身份。增量构建退出0，无待编译项。

**当前165源已另行完成隔离干净构建，退出0，实际生成165个 `.vo`。** 只复制活动源码及三个构建入口，不复制既有产品、参考材料或audit探针；168项输入结束时哈希一致。见本目录 `clean-build-result.json`。这与使用预编译依赖闭包的局部门禁分开记录，不刷新正式身份，也不是整函数或 `GOOD_OS` 通过。

逐路径／大小／SHA确认后，已删除40个新生成的探针编译产物、1,374,789字节，全部827个既有产品路径保留。规范门禁临时树清理24文件／9,966,800字节，源码定位临时树清理19文件／664,994字节，隔离干净构建临时树清理998文件／160,454,944字节。源文件、可复用依赖、用户材料及全部成功／开发失败日志保留；无来源基线的其他缓存不推测删除。

六阶段覆盖仍为 `94 / 1 / 1 / 1 / 1 / 0`。下一步连接整个前缀的非空事件路径，再处理物理TCB五字段、完整guard、临界区／调度、等待／ready共享不变量、全API／环境／初始化及源码级 `GOOD_OS` 与同程序K1–K4；uC/OS-III未启动。前瞻协议、对抗复核与机器汇总保存在 `audit/logs/stage26-task-prio-event-body/`；中文入门见[非空事件分支的真实位图写入](docs/开发中/非空事件分支的真实位图写入.md)。

## 前一局部检查点：读取事件指针，连接实际空路径（当时 165 源干净构建通过）

只在既有 `V293OSTaskChangePrio.v`、`V293TaskPrioRekey.v` 追加，原字节前缀保留，其他 163 个活动源及八项受保护输入不变。仍为 62 个 V293 和 103 个通用活动源；冻结 C／配置、端口、框架、正式函数证据和覆盖未修改，工作树未提交。

重新重建两项授权修复后的配置源码，核对完整函数记录与冻结身份，保存实际 Clang 事件字段、独立 if AST 和布局。TCB 的 `OSTCBEventPtr` 是偏移 28 的 `Tcom_ptr 411`；局部 pevent 为完整事件指针，复用框架现有兼容赋值和四字节编码。非空判断保留真实 typed-null cast，不修改框架。事件布局大小 16、Grp 偏移 10、两行 Tbl 偏移 11；只是固定分析布局对应，不声称 ABI 或编译器正确性。

稳定接口 `V293_task_prio_event_read_execution` 从实际指针、字段读取、目的四字节权限构造存储、实际小步执行、读回和条件求值，不接受成功 store 或后半段执行为前提。`V293_task_prio_prefix_event_null_execution` 从同一个入口 M 连接两次表写、三次 TCB 读取、ready 分支、实际事件读取和独立 if 假支。最后 Me 中确认完整 13 槽、旧槽空／新槽指针、位图读回及范围外 frame；不是只观察旧 Mf。实际非空 THEN 使用 `pevent->OSEventTbl`／`OSEventGrp` 字段 lvalue，空路径因真实条件为假而跳过，未偷换成 skip。

同一物理入口实例同时含表、任务指针／旧字段、位图、新旧局部、事件字段与目的权限。两条组合 ready 路径均执行 119–143 空路径；在固定 live 时，另有只改变事件字段值的 null／nonnull read 控制，目的初值同为另一非空指针。非空控制仅证明读取与条件，**不含非空体执行**；两条 ready 组合入口还改变高行／组，不当作单因素 ready 消融。pevent 可与其他局部发生物理混叠，所以六局部只承诺在 Mf 观察，未虚构 Me 中全部局部保持。

规范门禁 `audit/logs/stage26-task-prio-event/run-20261028-152804/result.json` 退出 0：14 条检查、八根静态字面接口／实际根假设、三次 `coqchk`、同环境正向重编和四项单头部负控。删除目的权限、偏移 28 谎称 24、反转条件、空出口谎称非空，均保留完整证明后缀并在指定声明内拒绝，均不给下游信用。181 个输入哈希全程及清理后不变，实际假设并集仍仅经典逻辑和依赖函数外延性。字面探针不是第二套独立 C 前端，人工建模信任边界保留。

144 项局部 Python 通过；完整实际执行 644 项，253 失败、1 错误，全部 254 个诊断块含旧正式证据身份拒绝，不给被遮蔽的下游测试信用。项目范围审计、冻结源码默认只读复核退出 0，默认 `make audit` 仍退出 2。旧六探针（表写、值级、物理 THEN、TCB、读取／ready、连续前缀）在当前源码下实际重编均退出 0，但未重跑其完整负控门禁；历史报告不自动获得当前输入信用。增量构建退出 0，无待编译项。

**另外完成当前 165 源的隔离干净构建，退出 0，实际生成 165 个 `.vo`。** 只复制活动源码及三个构建入口，不复制既有产品、参考材料或 audit 探针，168 项输入哈希结束时一致。见 `audit/logs/stage26-task-prio-event/clean-build-result.json`。这与使用预编译闭包的局部门禁分开记录，不是完整函数门禁或 `GOOD_OS` 通过。

逐路径／大小／SHA 确认后，删除 35 个本轮探针编译产物（1,174,034 字节），保留全部 827 个既有产品。基线最初遗漏 `.nia.cache` 的枚举错误由补充清单明确纠正，原基线和协议保留不改写。删除一次性拼接脚本，完整字节副本保留溯源。源码定位临时树清理 19 文件／664,994 字节；规范门禁临时树清理 24 文件／7,806,742 字节；干净构建临时树清理 998 文件／159,810,770 字节。源文件、可复用依赖、用户材料及所有成功／失败日志保留，无来源基线的 Python 缓存不推测删除。

非空事件体及等待事件不变量尚未连接，物理 TCB 五字段尚未更新；本步不表示等待任务成为 ready 或最终共享不变量恢复。具体入口不是完整结构分配／初始化可达性；13 槽容量不代替完整 API 的 `<12` guard。六阶段覆盖仍为 `94 / 1 / 1 / 1 / 1 / 0`。下一步证明非空事件 THEN 的真实字段数组写入，再连接 TCB 更新、完整入口 guard、临界区／调度、全 API／环境／初始化、源码级 `GOOD_OS` 与同程序 K1–K4；uC/OS-III 未启动。

前瞻协议、对抗性复核和最终汇总见 `audit/logs/stage26-task-prio-event/`；中文入门见[读取事件指针并跳过空事件分支](docs/开发中/读取事件指针并跳过空事件分支.md)。

## 前一局部检查点：两次表写接读取与 ready 分支（165 源干净构建通过）

本步仅在既有 `V293OSTaskChangePrio.v`、`V293TaskPrioRekey.v` 追加，原字节前缀保留，其他 163 个活动源及八项受保护输入不变；没有修改冻结 C／配置、端口、框架、正式函数证据或覆盖。仍为 62 个 V293 和 103 个通用活动源，工作树未提交。

稳定接口 `V293_task_prio_prefix_execution` 将固定配置函数第 119–130 行的两次优先级表写、三次 TCB 读取和实际 ready 条件／分支串成同一次执行。从入口实际读取、槽位／字节权限和块隔离构造两次成功存储，利用其 frame 推导同一 `M2` 中后半段的资源，再接 `Mr`、`Mf`；不假设成功 store、后半段执行或出口读取。最后在 **Mf 而非仅 M2** 证明完整 13 槽表读取、旧槽为空、新槽为目标指针、位图读回和范围外 frame。

本步新增同一物理入口的完整 13 槽实例，包含非零基址指针、TCB 三字段、位图／组、局部操作数及权限。`V293_prefix_combined_witness` 同时建立该入口的表／任务／位图关系和真实连续执行，不再只使用稀疏两槽实例。具体任务从 `8→6`，另一个 ready 任务在优先级 4：真支低／高行 `16/1→80/0`、组 `3→1`；假支 `16/0→16/0`、组保持 1；两支最终表槽均正确。**两入口还改变组摘要和抽象任务状态，只作一致路径见证，不冒称单因素消融。** 假支仍已执行表写和三次读取，只跳过 ready 更新；后面的事件 `if` 独立。

规范门禁 `audit/logs/stage26-task-prio-prefix/run-20261028-145549/result.json` 退出 0：14 条检查、七根静态字面接口／实际根假设、三次 `coqchk`、同环境正向重编和四项单头部负控。去掉表／TCB 隔离、去掉新局部／表隔离、整段谎称省略表写、最终旧槽谎称仍为指针，均保留完整证明后缀并在指定声明内拒绝，不给下游信用。179 个输入哈希全程及清理后不变，实际假设并集仍仅经典逻辑和依赖函数外延性。静态探针不是第二套独立 C 前端，人工源码建模信任边界仍保留。

136 项局部 Python 通过；完整实际运行 636 项，253 失败、1 错误，全部 254 个诊断块均包含旧正式证据身份拒绝，不给遮蔽的下游测试信用。范围审计、冻结源码默认只读复核退出 0，默认 `make audit` 仍退出 2。旧五探针（表写、值级、物理 THEN、TCB、读取／ready）在当前源码下实际重编均退出 0，但没有重跑其完整负控门禁，旧规范报告保留各自历史身份。

**另行完成当前 165 源的隔离干净构建，退出 0，实际生成 165 个 `.vo`。** 仅复制活动源码和三个构建入口，不带既有编译产品或参考材料；输入哈希结束时一致。见 `audit/logs/stage26-task-prio-prefix/clean-build-result.json`。这与使用预编译闭包的局部门禁分开记录，不刷新默认正式证据，也不表示完整函数门禁或 `GOOD_OS` 通过。增量构建亦退出 0。

逐路径／大小／SHA 确认后删除 30 个本轮探针编译产物、895,249 字节，保留全部 827 个既有产品；规范门禁专属临时树清理 24 文件／6,565,801 字节，干净构建专属目录清理 998 文件／159,347,585 字节。另确认删除一个一次性探针整理脚本，完整副本保留作开发溯源。源码、可复用依赖、用户资料和所有正负／开发失败日志保留；无来源基线的 Python 缓存不推测删除。

入口 TCB 坐标仍是显式前提，实例不是完整 TCB 分配或初始化可达性。物理 TCB 五字段尚未更新，入口抽象关系不等于最终共享不变量恢复；13 槽容量不代替完整 API 新优先级 `<12` guard。六阶段覆盖仍为 `94 / 1 / 1 / 1 / 1 / 0`。下一步读取实际 `OSTCBEventPtr` 并连接独立事件分支，随后完成 TCB 更新、入口 guard、临界区／调度、完整 API／环境／初始化、源码级 `GOOD_OS` 和同程序 K1–K4；uC/OS-III 未启动。

前瞻协议、失败／成功日志、对抗性复核和最终汇总均保留于 `audit/logs/stage26-task-prio-prefix/`。中文入门见[从两次表写串起 ready 更新](docs/开发中/从两次表写串起ready更新.md)。

## 前一局部检查点：TCB 读取接实际 ready 条件与分支（165 文件）

本步仅在既有 `V293OSTaskChangePrio.v`、`V293TaskPrioRekey.v` 追加代码／证明。固定配置后函数身份及实际 Clang 条件 AST 已重新核对；冻结 C／配置、端口、框架、正式函数证据和覆盖均不改写。仍为 62 个 V293 和 103 个通用活动源。

稳定接口 `V293_task_prio_read_ready_execution` 将第 121–123 行三次 TCB 读取接到第 124–130 行 ready 判断及真实 THEN／跳过。入口只提供三个新局部值、真实指针／字段及读取／写权限；三个旧局部值从执行得到。新局部和位图资源经同一实际中间内存 `Mr` 保持，再求值条件并构造分支执行，不假设成功存储、出口读取或后半段执行。假支保持的是 `Mr`，不是三次赋值前的入口内存。

条件保留字节提升、按位与、与零相等再取反；2048 个行字节／比特组合经 Coq 内核检查，连接到标准 `Nat.testbit`。实际 C 的 `0u` 引入 unsigned 相等比较，零相等只依赖比特；不扩张为大小比较或 ABI 等价性。**后续 `OSTCBEventPtr` 读取及事件 `if` 独立于 ready 条件，不是它的 else。** 条件为假仅跳过 ready 位图更新，不是整个 API 返回。

同状态稀疏入口含非零基址指针、TCB 三字段、位图及权限、新局部和初值为 255 的三个旧目的字节；通用见证消去这些入口条件。两条实际执行控制均为 `2→6`，只把低行 20 的旧 ready 位清为 16：真支出口低行 80，假支 16，高行均 0、组值均 1。控制同时观察实际 `cstepstar`、条件和最终内存读取。入口 TCB 坐标正确性仍是显式前提，夹具不是完整 TCB 分配／初始化可达性；`<13` 的片段范围不代替完整 API `<12` guard。

规范门禁 `audit/logs/stage26-task-prio-guard/run-20261028-143256/result.json` 退出 0：14 条检查、七根独立字面接口／实际假设、三次 `coqchk`、同环境正向重编和四项单头部负控；179 个输入哈希验收期间一致。反转条件、假支虚假更新、遗漏新旧局部块隔离、连续片段谎称省略读取均在指定声明内拒绝，原证明后缀不变，均不给下游信用。实际假设并集仍仅经典逻辑及依赖函数外延性。

128 项局部 Python 通过；完整实际执行 628 项，253 失败、1 错误，全部 254 个诊断块包含旧正式证据身份拒绝。项目范围审计通过；默认 `make audit` 仍退出 2。冻结源码复核首次误传不存在的 `--check` 参数而退出 2；改用工具默认只读模式后退出 0，原失败保留，没有记录新冻结身份。该局部门禁使用预编译依赖闭包，不是当前 165 源干净全量验收。旧四规范门禁报告仍只适用于各自历史身份，不自动延续到本步。

旧四探针（表写、值级、物理 THEN、TCB）在新源码下实际重编均退出 0，但未重跑其完整负控门禁。增量构建退出 0、无待编译项；这不是干净全量重建。逐路径／大小／SHA 确认后删除 25 个本轮探针编译产物、657,735 字节，保留全部 827 个既有缓存；规范门禁和源码定位的专属临时树分别清理 24 文件／5,426,778 字节及 19 文件／664,994 字节。179 个验收输入清理后哈希仍一致，两个活动源保留原字节前缀，其他 163 源及八项受保护输入均不变。

开发失败、全部正负日志、前瞻协议和对抗性复核保留在 `audit/logs/stage26-task-prio-guard/`；最终汇总见该目录 `final-validation-summary.json`。源文件、可复用依赖和用户数据保留；工作树未提交。

六阶段覆盖仍为 `94 / 1 / 1 / 1 / 1 / 0`。下一步连接此前两表写与本连续片段，随后处理真实事件指针／独立事件分支和 TCB 更新。完整表／任务／位图组合入口、抽象不变量到字段坐标、完整 API／环境／初始化、源码级 `GOOD_OS` 及同程序 K1–K4 都仍开放；uC/OS-III 未启动。入门见[从 TCB 读取连接 ready 判断](docs/开发中/从TCB读取连接ready判断.md)。

## 前一局部检查点：三次 TCB 字段的真实读取（165 文件）

本步只在既有 `V293OSTaskChangePrio.v`、`V293TaskPrioRekey.v` 追加实现／证明，原前缀保留，其他 163 个活动源码不变。仍为 62 个 V293 和 103 个通用文件；八项受保护输入、固定 C／配置／分析端口／框架／正式函数证据／覆盖均不变。冻结身份仍为 `74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da`。

从固定配置实际 AST 核对全部 21 个 TCB 字段。`OS_FLAGS` 是 16 位，`OSTCBFlagsRdy` 后有两字节填充；框架不会自动补齐，故完整类型在准确位置显式表示该填充，不以错误的 32 位 Flags 凑长度。Coq 检查结构长度 56，Y／BitY／BitX 偏移分别为 52／54／53；独立字面探针与源码结构比较覆盖全部字段。只建立固定分析类型／布局的源码对应，不宣称 ABI、编译器或硬件正确性。

`V293_task_prio_read_old_execution` 按固定 C 第 121–123 行执行 `y_old=ptcb->OSTCBY; bity_old=ptcb->OSTCBBitY; bitx_old=ptcb->OSTCBBitX`。每句从实际字段读取并赋值到局部字节，成功存储由目的权限构造；第二、三句在真实中间内存中重新读取 `ptcb`，不是调用方提供成功执行。出口推导三个实际局部读取、原指针／TCB 字段保持和其他块的逐字节 frame。要求三个局部目的块互异且与指针／TCB 块分离。

同状态稀疏入口同时放入四字节指针、三个字段、三个目的权限和四个局部绑定，基址为非零的 8；通用见证覆盖任意合法三字节的真实执行，具体控制把初值 255 改为 1／2／4。独立实际混叠控制把指针首字节写坏，真实指针读取返回 `Vundef`。这不是完整 TCB 分配／初始化或合法 API 反例；入口坐标尚未从抽象任务不变量推出，也未构造完整 13 槽表／任务／位图组合见证。

规范 TCB 子门禁 `audit/logs/stage26-task-prio-tcb/run-20261028-140244/result.json` 退出 0：14 条检查、七根独立字面接口／实际假设、三次 `coqchk`、同环境正向副本重编、四项单头部负控。权限、指针块隔离、Y 偏移 52 谎称 50、BitY 出口 2 谎称 4 均在指定声明内拒绝，保留完整原证明后缀，不给下游信用。180 个输入哈希全程及清理后不变，实际假设并集仅经典逻辑与依赖函数外延性。

BitY 负控最初因未固定 `apply` 的参数而耗时数分钟，但原完整运行仍在 600 秒上限内正常拒绝并通过；不能误报原门禁超时。最小复现中透明和仅 opaque 的错误版本均 15 秒超时，未保留无改善的 opaque；显式固定 P／ks／1／2／4 后，正确约 0.87 秒通过、错误约 0.90 秒拒绝。先红后绿的结构性回归及完整重跑保留；本轮最终四项 TCB 负控含全前缀编译各约 7–8 秒，不改头部、错误结论、存储算法或信任边界。原运行、提前导入拒绝和全部开发失败均保留。

旧三门禁也在当前输入重放通过：物理 THEN `audit/logs/stage26-task-prio-physical/run-20261028-140700/result.json`（14 条／七根／173 输入）、值级 `audit/logs/stage26-task-prio-bitmap/run-20261028-141151/result.json`（14 条／八根／173 输入）、两表写 `audit/logs/stage26-task-prio-rekey/run-20261028-141554/result.json`（14 条／六根／172 输入）；各有四项指定负控和三次 `coqchk`。不将它们并列当成整个 C 函数的连续执行。

120 项局部 Python 通过；全套实际执行 620 项，仍有 253 失败、1 错误，全部 254 个诊断块包含旧正式证据身份拒绝，不给遮蔽的下游测试信用。项目范围审计和冻结源码重放退出 0，默认 `make audit` 仍退出 2。增量构建退出 0，不等于当前 165 文件的隔离干净全量验收。

逐路径／大小／SHA 核对后删除 20 个本轮探针编译产物、452,656 字节；全部 827 个既有缓存保留。源码定位、性能复现和各门禁临时树分别按清单核对后清理，源文件、可复用依赖及成功／失败交付证据均保留。工作树未提交；完整汇总见 `audit/logs/stage26-task-prio-tcb/final-validation-summary.json`。

六阶段覆盖仍为 `94 / 1 / 1 / 1 / 1 / 0`。外层 ready 条件、本步与 THEN／此前表写的同内存连续连接、waiting／事件、物理 TCB 五字段更新、完整 API／函数环境／初始化、源码级 `GOOD_OS` 和同程序 K1–K4 都仍开放，uC/OS-III 未启动。原较大前瞻协议包含外层条件，**TCB 子门禁通过不表示该协议全部完成**。下一步使用本步实际读出的局部值验证 `(OSRdyTbl[y_old] & bitx_old) != 0u` 的真／假分支。教学见[三次 TCB 读取](docs/开发中/改优先级前的三次TCB读取.md)。

## 前一局部检查点：ready THEN 的真实位图写入（165 文件）

本步在既有 `V293OSTaskChangePrio.v`、`V293TaskPrioRekey.v` 末尾追加代码／证明，原前缀保留，其他 163 个活动源码不变。仍为 62 个 V293、103 个通用文件。冻结 C、配置、端口、框架、正式函数证据和覆盖 JSON 不变；冻结身份仍为 `74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da`。源码冻结只读重放退出 0，94 定义、16 声明边界不变；不声称新增完整 C→Coq 翻译。

`V293_task_prio_ready_then_execution` 从入口实际两行／组值、字节写权限和六个局部操作数读取，构造固定 C ready THEN 内部的顺序执行：清旧行、根据刚写的行决定是否清组、置新组、置新行。推导真实 `cstepstar`、出口两行／组读回、权限／局部读取保持及位图块以外的逐字节 frame，不把成功存储或出口读取当作前提。同一行和跨行均覆盖，保留未使用高位；`old=new` 未被片段接口排除，数组容量 13 不代替完整 API 新优先级 `<12` guard。

通用同状态入口见证同时构造两行／组读取、三字节权限和六个局部操作数；通用执行见证消去这些物理入口条件。四个实际内存控制分别验证 `8→6`、同高行 `8→10`、同低行 `2→6` 以及 `hi=129` 保留高位、group 为 3。另有实际 store/load 的混叠控制，说明局部操作数不混叠的作用，不冒称合法 API 反例。

`V293_task_prio_ready_then_correspondence` 在物理表已重索引的入口上，连接本步真实位图执行、抽象任务／表关系和最终实际表读取／最高就绪选择。尚未新增同时实例化完整 13 槽表＋任务关系＋位图全部入口的组合见证；片段见证不替该更大接口授信。三次 TCB 读取和外层 ready 判断尚未连接，所以不能将此前两次表写与本步冒称为连续执行；物理 TCB 五字段也尚未更新。

规范物理门禁 `audit/logs/stage26-task-prio-physical/run-20261028-132121/result.json` 退出 0：14 条检查包括两源实际重编、七根独立字面接口／真实假设输出、三次 `coqchk`、同环境两源及探针正向重编、四项单头部负控。四负控保留全部原证明，分别省略权限、移除写块限制、把同一行出口错误恢复旧位、把真实 THEN 冒称 noop；均在指定声明内退出 1，不给下游信用。实际假设并集仅经典逻辑及依赖函数外延性，173 个验收输入哈希全程一致。权限／块限制／noop 的证明消费拒绝不自动构成完整语义反例，另有独立真实混叠控制。旧值级门禁 `audit/logs/stage26-task-prio-bitmap/run-20261028-132604/result.json` 也在当前身份退出 0（14 条检查、八根、四负控、173 个输入）；旧表写门禁 `audit/logs/stage26-task-prio-rekey/run-20261028-133003/result.json` 亦退出 0（14 条检查、六根、四负控、172 个输入），不是复用旧身份。

111 项局部 Python 通过；完整实际执行 611 项，253 失败、1 错误，全部 254 个诊断块含旧正式证据身份过期拒绝，不给被遮蔽的下游条件信用。范围审计退出 0，增量构建退出 0 且无待编译项；新两源的实际重编由局部门禁承担。本步没有当前 165 源的干净全量构建。默认 `make audit` 仍退出 2，没有删除不利结果或重写冻结证据。

开发中整内存 `vm_compute` 引发资源增长后主动终止；`-time` 定位到具体控制而非已闭合的通用执行，随后改用已证通用执行实例，预期不变。探针局部不透明有限映射 set 只控制转换展开，不新增公理；最初取样误判与最终定位更正均保留，未宣称严格单因素性能归因。失败／终止日志、对抗性核对见 `audit/logs/stage26-task-prio-physical/`。

逐路径／大小／SHA 复核后，删除本轮新增 15 个探针编译产物、332,413 字节；827 个既有产品全部保留，其中两模块的六个派生产物与 `.lia.cache` 正常更新，继续作活动验证依赖。三套门禁的专属临时树分别为 24 文件／3,127,840 字节、24 文件／2,290,799 字节、24 文件／1,872,928 字节（以各 result.json 实际记录为准），按各清单核对后清理；保留全部探针源码、失败／成功日志、负控候选和用户资料。清理后验收输入身份再次核对，八项受保护输入一致；末次增量构建退出 0、无待编译项，仍不是干净全量验收。工作树未提交。汇总见 `audit/logs/stage26-task-prio-physical/final-validation-summary.json`。

八项受保护输入不变，六阶段覆盖仍为 `94 / 1 / 1 / 1 / 1 / 0`。三次 TCB 读取、外层判定、waiting／事件、物理 TCB 更新、临界区与调度、完整 API／函数环境／初始化、源码级 `GOOD_OS` 与同程序 K1–K4 仍开放，uC/OS-III 未启动。下一步沿固定 C 接三次 TCB 读取与外层判定，而不是再新增位图抽象。中文教学见[真实位图写入](docs/开发中/改优先级ready分支的真实位图写入.md)。

## 前一局部检查点：ready 改优先级的值级对应（仍为 165 文件）

在既有 `V293OSTaskChangePrio.v`、`V293TaskPrioRekey.v` 末尾追加两个 RHS 与证明，原字节前缀保留，其他 163 个活动源码不变，不新增 Coq 源码文件。精确重建两项修复后的固定 C；冻结身份仍为 `74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da`，配置后 `OSTaskChangePrio` 函数体哈希 `9d6cfd0b9d357d4ef09589569926a22cb5999fe4dca38ad03236a791793b9db1`。记录第 121–138 行及准确配置后函数体，不以未配置源码替代。

对 256 字节 × 8 位置的整数 AND／补码／位移／模转换／OR 与标准清位置位作内核检查，推出任意合法字节的结果及范围。两个 RHS 真实 `evaltype/evalval` 定理保留 C 提升、显式 `OS_PRIO` 补码窄化及最终字节转换；掩码值仍是操作数条件，并未从物理 TCB 字段推导。顺序更新证明覆盖同一行和跨行，不重复使用旧行值；高行第 5 位及以上保持，未增加“未使用位全零”限制。组位图以入口两行的非零摘要为初值，按实际条件清位／置位顺序证明等于更新后的非零行摘要；尚未证明真实内存入口组位值等于该初值。`hi=129` 控制明确保持组位为 3。

稳定接口 `V293_task_prio_rekey_ready_correspondence` 从入口表／任务／位图关系、旧 ready 任务、新槽空值及两次真实表存储，**推导**出口三种对应、组位图、物理表读取、旧槽为空与最高就绪选择。不再把出口对应当作前提。两个辅助保持接口删除不必要的新旧不同条件；主接口要求旧槽为空，仍保留该条件。范围是 ready 分支的**值级变换加真实表存储对应**，没有位图／TCB 写入的 `cstepstar`，不声称 M2 的物理 ready 不变量恢复，不跳过表写后紧接的三次 TCB 读取来伪造连续执行。13 是数组容量，不替代完整 API 的 `<12` 新优先级 guard。本轮没有同时实例化新组合接口全部入口关系／完整 13 槽读取的同状态物理见证；旧稀疏两槽实例不自动授予这个信用。

规范检查复用 `scripts/check-v293-task-prio-rekey.py --bitmap`，没有复制新验证器。`audit/logs/stage26-task-prio-bitmap/run-20261028-124713/result.json` 退出 0：14 条外部检查包括两源重编、八根独立字面接口／真实假设、三次 `coqchk`、同环境两源及探针正向重编、四项单头部负控。实际假设并集仅经典逻辑及依赖函数外延性，173 个验收输入哈希全程一致。四负控保留原证明，分别在字节算术、成员关系、入口空槽消费、具体组位控制的指定声明内退出 1，均不给下游信用；省略空槽的提前拒绝不独立检验其后存储／任务选择。开发阶段失败日志全部保留，未弱化信任集合。

103 项局部 Python 通过；完整实际执行 603 项，253 失败、1 错误，全部 254 个诊断块包含旧正式函数证据身份拒绝，不给遮蔽的下游检查信用。范围审计及冻结源码只读重放退出 0，默认 `make audit` 仍退出 2。没有本轮 165 源的干净全量构建，不继承旧快照身份。

旧表写入完整局部门禁在当前输入下也退出 0：`audit/logs/stage26-task-prio-rekey/run-20261028-125139/result.json` 的 14 条检查／六根接口／四负控通过，172 个输入身份保持。增量构建两次退出 0，首次实际补编六个既有模块，末次无待编译项；新增两源由两套规范检查分别实际重编。不等于本轮干净全量验收。

逐路径／大小／SHA 复核后删除 10 个本轮探针编译产物、181,140 字节；源码、所有成功／失败日志及候选负控保留。790 个既有缓存全部保留，仅 `.lia.cache` 正常更新；初始 glob 漏记的 `.nia.cache` 用补充清单与前轮哈希核对，没有改写初始清单。另保留 40 个本轮工程模块编译产物、5,891,101 字节，作为后续活动目标的可复用验证依赖，避免反复重建，并逐项记录保留理由。新／旧门禁临时树分别 24 文件／1,600,776 字节和 24 文件／1,182,905 字节，源码定位临时树 19 文件／664,994 字节，均按清单复核后清理。清理后两套 173／172 个验收输入身份及八项受保护输入仍一致，工作树未提交；汇总见 `audit/logs/stage26-task-prio-bitmap/final-validation-summary.json`。

八项受保护输入不变；不改冻结 C、配置、分析端口、框架、正式函数证据、覆盖 JSON。六阶段覆盖仍 `94 / 1 / 1 / 1 / 1 / 0`。物理位图／TCB／事件、waiting 分支、临界区与调度调用、函数环境、初始化、最终源码级 `GOOD_OS` 及同程序 K1–K4 仍开放，uC/OS-III 未启动。中文入门与边界见[就绪位图对应](docs/开发中/改优先级后的就绪位图对应.md)。

## 前一局部检查点：优先级表两次真实写入（165 文件）

新增 `V293OSTaskChangePrio.v` 与 `V293TaskPrioRekey.v` 并登记 `_CoqProject`；原 163 个活动 Coq 源码哈希全部不变。当前为 165 文件（62 个 V293、103 个通用文件）。精确重建两项授权修复后的源码并核对冻结身份，定位 `Source/os_task.c` 第 119–120 行；只手工建模这两条表写，不声称完整 C→Coq 翻译器或整函数对应。

稳定接口 `V293_OSTaskChangePrio_table_execution` 从实际环境、局部操作数读取及两槽各四字节写权限，**构造**两次成功存储，交付真实 `cstepstar`、最终旧槽空值／新槽目标指针，以及两写入区间之外的逐字节保持。局部操作数块与数组块不混叠，第二次赋值从中间内存重读索引和指针。全表 `load` 视图经真实两次写入传递到列表更新；条件 ready 选择接口仍显式要求更新后位图／任务表／优先级表对应，未凭空证明位图、TCB 或事件更新。

无开放前提的具体实例执行 `8 → 6`，入口旧槽为指针、新槽为空，出口相反；只构造两个触及槽和三个操作数，不是完整 13 槽／物理 TCB／ready／初始化可达性见证。另有真实内存语义消融：仅令新旧索引相同，第二次存储覆盖第一次，最终为指针而非空；这说明槽位不同条件必要，不把完整 API 较早会拒绝的索引相等情况当成合法 API 反例。

规范门禁 `audit/logs/stage26-task-prio-rekey/run-20261028-122703/result.json` 退出 0：14 条外部检查包括两源真实重编、六根独立字面接口／真实假设、三次 `coqchk`、同环境两源及探针正向重编、四项保留全部原证明的单头部负控。四负控均退出 1、严格命中各指定声明，均不给下游信用；其中权限／任务对应缺失在接口消费处提前拒绝，不据此声称后续存储或选择机制得到独立检验。实际假设并集仍仅经典逻辑和依赖函数外延性，172 个输入哈希全程一致。本步依赖预编译闭包，没有当前 165 文件的新干净全量构建，也没有重放旧正式完整函数门禁。

95 项局部 Python 通过；完整 Python 实际执行 595 项，253 次失败、1 次错误，254 个诊断块全部包含正式函数证据身份过期拒绝，不给被遮蔽的下游检查授信用。项目范围审计、冻结源码只读重放退出 0；默认 `make audit` 仍退出 2。开发时真实失败、一次因资源增长主动终止及一次 45 秒超时完整保留；快速试编不替代规范验收。编译中间偏移的失败来自 `simpl` 展开常数乘法为匹配表达式，改用保持乘法结构的数值边界后 `lia` 闭合；没有弱化范围前提或信任允许集合。

增量构建两次均退出 0：首次实际补编两个既有依赖模块，最后一次无待编译项；新两源实际重编另由规范门禁承担。逐路径／大小／SHA 复核后清理 45 个本轮新增非交付 Coq 派生产物、5,786,070 字节，790 个基线缓存全部保留，仅 `.Makefile.coq.d` 与 `.lia.cache` 正常更新。规范门禁临时树 24 文件／892,374 字节、源码重建临时树 16 文件／548,924 字节也已清单复核清理；源码、可复用依赖、用户材料及所有成功／失败／超时日志保留。清理后 172 个验收输入哈希仍一致，工作树未提交。

八项受保护输入不变：不改冻结 C、配置、分析端口、框架、正式函数证据或覆盖 JSON。六阶段覆盖仍为 `94 / 1 / 1 / 1 / 1 / 0`。完整 `OSTaskChangePrio`、物理位图／TCB／事件关系、临界区、源码切换对应、函数环境、初始化、最终源码级 `GOOD_OS` 和同程序 K1–K4 仍开放；uC/OS-III 未启动。中文说明见[两次真实写入](docs/开发中/任务优先级表两次真实写入.md)，本轮汇总见 `audit/logs/stage26-task-prio-rekey/final-validation-summary.json`。

## 前一局部检查点：空缓存槽分支与同指针计数轨迹（163 文件）

在已有 `V293OSSchedStorageConnect.v`、`V293SwitchPriorityBoundary.v` 末尾追加证明，两份旧源保持逐字前缀，其余 161 个活动源码不变。`V293_rekey_vacates_cache` 证明清旧槽／填不同新槽的纯列表效应，不是两条 C 写入的小步执行。新稳定接口 `V293_ready_OSSched_vacated_cache` 从同一 ready 位图、任务表和优先级表的空缓存槽导出原字节条件成立，连接真实内部调用／目标赋值、UINT32 模递增、普通框架切换和两层 guard；不要求缓存准确或当前／目标不同。启用时消费 `sched` 并恢复同一关系，禁止时保留 pending 调度。该接口不含实际临界区进出，不继承其他候选程序的临界区或源码端口信用。

独立原始内存夹具实际执行原条件及赋值：cache=8、high=6、同指针、counter=17，执行到切换调用入口时 counter=18，缓存仍为 8；仅换候选指针条件则跳过分支、保持 17。不越过调用边界，不把夹具当成完整 ready 入口、物理 TCB 或初始化可达性。完整 `OSTaskChangePrio` 的位图、事件表、TCB 五字段、临界区与调度调用仍须纵向连接；不能用纯列表引理代替这些义务。

本次规范门禁 `audit/logs/stage26-cache-lag-branch/run-20261028-114121/result.json` 退出 0：**17 条外部检查**包含三源真实完整重编、八根独立字面接口／真实假设、四次 `coqchk`、同环境三源及探针正向副本和四项负控。负控只改单个头部前提或结论，保留原证明；全部退出 1 且严格命中指定声明，均不给下游信用。其中省去递增语句的负控在规范化阶段提前拒绝，不能据此单独验证后续递增／切换机制。实际假设并集仅经典逻辑和依赖函数外延性，170 个输入哈希在验收及清理后相同。首次门禁因探针漏直接导入退出 1；仅补导入后从头重跑，原失败保留。性能诊断中的失败、超时及资源终止全部保留，快速尾部试验不当作完整源码验收。

87 项局部 Python 通过；完整 Python 实际执行 **587 项，253 次失败、1 次错误**，全部 254 个诊断块包含旧正式函数证据身份过期拒绝，不给被遮蔽的下游检查授信用。默认 `make audit` 仍退出 2。范围审计、冻结源码只读重放、最后增量构建均退出 0；两个旧探针回归编译也退出 0，但未重放旧门禁的全部负控。本轮没有当前 163 文件的新干净全量构建，前一检查点的干净构建只保留历史身份。

八项受保护输入不变；不改冻结 C、配置、分析端口、框架、信任允许集合、正式函数证据或覆盖 JSON。六阶段覆盖仍为 `94 / 1 / 1 / 1 / 1 / 0`，完整 API／函数环境／初始化、源码级 `GOOD_OS`、同程序 K1–K4 仍未完成，uC/OS-III 未启动。

逐路径／大小／SHA 复核后清理 **45 个本轮新增非交付 Coq 产物、5,680,119 字节**；790 个基线缓存全部保留，仅 `.Makefile.coq.d` 更新。规范门禁临时树 30 文件、7,298,719 字节及尾部诊断树 12 文件、952,304 字节均按清单复核清理；其他诊断临时树的清理记录一并保留。源码、依赖、用户材料及全部成功／失败日志保留，工作树未提交。详见[中文接口及边界](docs/开发中/同一ready关系的指针条件分支.md)与 `audit/logs/stage26-cache-lag-branch/final-validation-summary.json`。

## 前一局部检查点：两内存缓存对应与真实 API 边界（163 文件）

在已有 `V293OSSchedPointerCompare.v`、`V293SwitchPriorityBoundary.v` 末尾追加局部证明，两个旧文件均保持逐字前缀，其余 161 个活动源码不变。源码内存与表示内存仅允许一个缓存地址不同；证明非缓存块实际读取相同、从表示端成功写入构造源码端同一写入，以及源码另行显式同步缓存后的条件性对应。比较接口从同一任务表／位图和实际读取证明源码优先级条件等于表示端候选指针条件，同时保留源码缓存变量的真实观察。小型夹具实际实例化通用定理，并证明直接保留陈旧字节比较会产生相反决定。它不是端口实现、完整 ready 轨迹或整程序缓存消去；源码端两指针读取及物理 TCB 对应也没有凭空得到。

进一步从精确重建的修复后固定配置 Clang AST 定位五处 `OSPrioCur` 直接名称引用；该清点不证明别名／外部操作完备性。冻结 `OSTaskChangePrio` 的受控 C 执行发现关键边界：相同初始状态中，仅把 `oldprio` 从另一任务改为自任务，原优先级 guard 均为 1、计数均从 17 增至 18，但自任务支的指针 guard 为 0，缓存仍为 8、当前 TCB 已改为 6。GCC／Clang，各 `-O0`／`-O2`，共四次编译、八次执行均通过精确观察；首次误用 idle 优先级的夹具创建失败完整保留、不给下游信用。这不是 C 缺陷，却说明不能将“缓存在调度入口总是准确”当成通用调用者事实。**下一步先形式化这条 API 路径及同指针切换／计数行为，再连接允许的源码切换边界；仅补切换后缓存同步不够。**

独立局部门禁 `audit/logs/stage26-cache-correspondence/run-20261028-102629/result.json` 退出 0，14 条外部检查包含两源实际重编、六根字面接口／真实假设、三次 `coqchk`、同环境正向副本和四项保留原证明的单头部负控；四项负控均退出 1、严格命中指定声明，不授予下游信用。假设并集仍仅经典逻辑与依赖函数外延性。另在不复制任何旧 Coq 产物的隔离树干净构建当前 **163 文件（60 个 V293、103 个通用文件）**，构建约 619 秒；新六根探针和三个旧探针全部编译通过，两源与新探针三次 `coqchk` 全部退出 0，170 个构建／探针输入身份从开始到结束一致。该闭包验收不是完整函数门禁重放，不更新旧 162 文件正式报告。

79 项局部 Python 通过；完整 Python 实际执行 579 项，253 次失败、1 次错误，全部 254 个失败／错误块包含旧正式函数证据身份过期的提前拒绝，不据此断言被遮蔽的下游检查有效。增量构建、范围审计及冻结源码只读重放退出 0；默认 `make audit` 仍退出 2。C、配置、端口、框架、信任集合、正式函数报告与覆盖 JSON 均未改，八个受保护输入一致。六阶段覆盖仍为 `94 / 1 / 1 / 1 / 1 / 0`；整函数连接、相关 ISR／API、初始化、最终 `GOOD_OS` 及同程序 K1–K4 仍开放，uC/OS-III 未启动。

按逐项路径／大小／SHA 清单确认后清理 35 个本轮新增非交付 Coq 产物、4,912,169 字节；790 个既有缓存／构建文件保留，仅依赖文件和 `.lia.cache` 正常更新。干净验证临时树 1,010 文件、157,055,263 字节及局部正负检查、诊断、源码定位、C 试验临时树均按清单清理；源文件、依赖、用户材料及全部成功／失败记录保留，工作树未提交。详见[中文解释与边界](docs/开发中/同一ready关系的指针条件分支.md)及该目录的 `final-validation-summary.json`。

## 前一局部检查点：实际 ready 不变量的缓存反例（163 文件）

在既有 `V293SwitchPriorityBoundary.v` 末尾构造完整共享存储夹具，原文件保持逐字不变前缀，其余 162 个活动源码不变。`V293_ready_boundary_entry` 直接证明实际 ready 不变量接受缓存为 4 且准确的入口；`V293_ready_boundary_pointer_only` 给出真实指针存储成功、抽象当前任务更新后的存在状态：新任务优先级为 12 且是最高就绪任务，旧任务仍为成员，同一 ready 不变量成立，但缓存仍读出 4，准确性不成立；`V293_ready_boundary_no_cache_entailment` 因而排除实际 ready 关系蕴含准确缓存。三项结果均无“某不变量接受入口”的开放前提，不再只有旧小夹具的条件性障碍。实例尾部为计数器 `13`／缓存 `12`，没有 guard `14`／`15`；目标槽未执行赋值前缀，不声称 `switch 107` 的完整小步轨迹，检验的是 `GoodI` 第三项的存储保持要求。

构造复用现有数组／全写权限布局；实际 `V293_ready_store` 完成同一 ready 不变量的保持，空间资源通过实际 `load` 观察缓存。**这是当前模型的反例，不是初始化可达性、完整 `OS_Sched` 轨迹、冻结 C 或 CPU 端口缺陷证明。** 不新增缓存同步写入，不把额外动作归给普通框架切换；不改 C、配置、框架、端口、信任集合、正式函数报告和覆盖 JSON。此结果不能凭空给真实优先级临界区提供准确性前提；下一步是明确源码切换调用与已接受抽象边界的状态对应及缓存义务，并处理后续真实读取，不继续堆叠无来源的准确性假设。

当前仍为 163 个活动 Coq 文件（60 个 V293、103 个通用文件），六阶段覆盖 `94 / 1 / 1 / 1 / 1 / 0`。源码切换对应、相关 ISR／API、完整物理不变量、延期规格、函数环境、初始化、最终 `GOOD_OS` 及同程序 K1–K4 仍开放；uC/OS-III 未启动。详见[中文反例与下一步接口](docs/开发中/同一ready关系的指针条件分支.md)。

新协议 `audit/logs/stage26-ready-cache-counterexample/result.json` 退出 0：11 条检查，三根独立字面接口与真实假设、源／探针两模块 `coqchk`、同环境正向副本通过；四项只改单个头部结论的负控均退出 1、严格命中指定新声明，保留原证明与严格拒绝解析，不当作独立语义反例。假设仍仅经典逻辑和依赖函数外延性。首次探针漏直接导入的失败及其报告完整保留，补齐后从头重跑。旧边界门禁 `run-20261028-095555` 在当前输入下退出 0，5 个旧根／3 项指定负控通过；不据此声称旧门禁检查了新增三根。

71 项局部 Python 通过；完整 Python 执行 571 项，253 次失败、1 次错误，全部 254 个失败／错误块包含旧正式证据身份过期拒绝，不给被遮蔽的下游机制授信用。依赖补建与随后增量构建退出 0，新源／探针由协议实际重编；没有当前 163 文件的干净全量验收。范围审计与冻结源码正确参数下的只读重放退出 0，首次不支持参数的 usage 失败日志保留；默认 `make audit` 仍退出 2，正式报告与覆盖 JSON 未改，8 个受保护输入不变。

清单复核后清理 40 个本轮新增非交付 Coq 产物、4,659,312 字节；前瞻记录的 788 个既有缓存保留，仅 `.Makefile.coq.d` 随新增导入更新，既有两份构建文件保留。新／旧协议临时树分别 18 文件、873,093 字节和 15 文件、494,533 字节，均按清单清理。源码、依赖和全部成功／失败证据保留；清理后两个当前局部报告输入身份及受保护输入再次核对一致，工作树未提交。详见本轮目录的 `final-validation-summary.json`。

## 前一局部检查点：真实优先级条件与两层 guard 接入 ready 关系（163 文件）

在既有 `V293OSSchedStorageConnect.v` 末尾追加 `V293_ready_priority_guarded_skip` 和 `V293_ready_OSSched_priority_guarded`，原文件为逐字不变前缀，其余 162 个活动源码不变。主体采用冻结 C 的优先级比较，不使用候选指针比较：两个 guard 均为零才执行真实内部调用／目标赋值及优先级条件，切换分支实际 UINT32 递增并使用框架普通切换，相等分支由同一任务表完成抽象自调度；两个启用分支消费 `sched`。禁止调度时不执行主体，忘却共享观察、恢复同一个 ready 不变量并保留 `sched;;aop`。不改 C、配置、端口、框架、信任集合、正式函数报告或覆盖 JSON。

准确当前缓存仍是关中断后显式前提；新接口没有实际 `encrit/excrit`，不继承候选指针临界区的证明，也没有获得 `OSCtxSw` 源码对应或缓存保持性。本次未新增该尾部排列的同状态完整入口见证，旧候选布局见证不自动为本接口授信用。源码缓存／切换对应、相关 ISR／API、上层延期规格、完整函数环境、初始化、最终源码级 `GOOD_OS` 与同程序 K1–K4 仍开放。六阶段覆盖仍为 `94 / 1 / 1 / 1 / 1 / 0`，uC/OS-III 未启动。

独立字面探针 `audit/probes/V293ReadyPriorityGuardsProbe.v` 已实际编译，检查完整优先级 guard 主体和禁止分支 pending 关闭两根接口；不以候选入口／恢复断言别名决定接口。前瞻协议与全部日志在 `audit/logs/stage26-ready-priority-guards/`。新协议退出 0：两根实际接口／假设、源及探针两模块 `coqchk`、同环境正向副本全部通过；四项只改新增定理头部的单因素负控均退出 1，严格命中指定新定理，原严格拒绝解析不变。实际假设并集仍仅经典逻辑与依赖函数外延性。原连接门禁 `audit/logs/stage26-connect/run-20261028-092831/result.json` 在当前输入下退出 0，25 根接口与 21 项指定负控通过，不继承旧报告的身份信用。

67 项局部 Python 测试通过；完整 Python 回归执行 567 项，253 次失败、1 次错误，全部 254 个失败／错误块均包含正式证据身份过期拒绝，不给被遮蔽的下游机制授予通过信用。增量 `make build` 退出 0，实际重编优先级边界文件；不是当前 163 文件的干净全量门禁。项目范围审计及冻结源码只读重放退出 0，默认 `make audit` 仍退出 2；8 个受保护输入不变，正式报告与覆盖 JSON 保持原样。

逐路径／大小／SHA-256 确认后清理 40 个本轮新增非交付 Coq 派生文件，共 4,960,957 字节；790 个既有产物全部保留、哈希不变。新协议临时树 18 文件、5,790,375 字节及旧门禁临时树均经清单复核清理，全部日志与源码保留。清理后两个当前报告输入身份及受保护输入再次核对一致，工作树未提交。最终汇总为该目录 `final-validation-summary.json`。详见[中文程序与准确性边界](docs/开发中/同一ready关系的指针条件分支.md)。

## 前一局部检查点：新 guard 布局的同状态完整入口见证（163 文件）

在 `V293OSSchedStorageConnectWitness.v` 末尾增加 `V293_ready_guard_entry_witness`，既有声明与证明保持逐字不变前缀。两种当前任务模式、任意合法 guard 字节和 UINT32 计数器在**同一状态**满足完整 ready 快照入口；同时观察两个 guard、准确当前优先级缓存、精确计数器和指定任务／事件／时间字段，局部环境为空，中断栈／临界区栈取 `nil`，不声称从实际 `encrit` 产生该栈。私有 frame 只有绑定和无遮蔽事实，不持有这些共享字节。仅改变一个活动源码，其他 162 个文件不变，不改 C、配置、端口、框架或信任集合。

本次是关中断入口的局部非空洞见证，不是 `OSStart` 初始化可达性、完整物理 TCB、切换后的缓存准确性或开启中断入口的新鲜状态证明。候选指针程序没有替代冻结 C 的优先级比较。源码缓存／切换对应、相关 ISR／API 保持性、上层延期规格、完整函数环境、初始化、最终源码级 `GOOD_OS` 与同程序 K1–K4 仍开放；六阶段覆盖仍为 `94 / 1 / 1 / 1 / 1 / 0`，uC/OS-III 未启动。

自审曾复现新增结构测试对 Git 忽略的 `audit/logs/` 脚本的依赖；已改为只检查交付源码，保留同样的四项单观察／证明不变断言。模拟缺失日志文件的测试由错误转为通过，未实际移走运行中的脚本。该修正改变测试身份，旧结果不沿用，相关门禁重新执行；原始失败和成功日志均保留。

当前输入下，新协议退出 0：独立字面完整入口、同状态四个实际 `load`／两个 guard 表达式与私有 frame 共 3 根接口，真实假设检查、源／见证／探针 3 模块 `coqchk`、同环境正向副本全部通过；4 项只改单个头部观察的负控均退出 1，严格命中新增指定声明，原严格拒绝解析和信任集合不变。实际假设并集仍仅经典逻辑与依赖函数外延性。既有新鲜 guard 探针的 4 根在当前输入下重编通过。旧连接门禁 `audit/logs/stage26-connect/run-20261028-085914/result.json` 退出 0：25 根接口／假设、`coqchk`、正向副本和 21 项指定负控符合预期。自审修正前的首次新协议在最终输入身份检查退出 1，历史检查结果保留在 `attempt-01-before-portability-fix/`，不冒称当前整条门禁成功；旧连接门禁也在修正后重跑，不继承修正前报告。

63 项局部 Python 测试通过；完整 Python 回归实际执行 563 项，253 次失败、1 次错误，全部 254 个失败／错误块都包含正式证据身份过期拒绝，不授予被遮蔽的下游机制通过信用。增量 `make build` 退出 0，实际重编优先级边界文件；不是当前 163 文件的干净全量门禁。项目范围审计及冻结源码只读重放退出 0，默认 `make audit` 仍退出 2，正式报告／覆盖 JSON 未改，8 个受保护输入不变。

逐路径／大小／SHA-256 确认后，清理 45 个本轮新增非交付 Coq 派生文件和 3 个一次性构造缓冲，共 48 文件、5,071,568 字节；790 个既有产物全部保留且大小／哈希均不变。两次新协议临时树各 18 文件，两个旧连接门禁临时树各 99 文件均已清单复核清理，全部成功／失败日志、源码、用户材料和依赖保留。清理后再次核实两个最终报告输入身份和受保护输入一致；工作树未提交。前瞻协议及最终结果见 `audit/logs/stage26-ready-guard-entry/PROTOCOL.txt`、`final-validation-summary.json`。详见[中文入口资源表与边界](docs/开发中/同一ready关系的指针条件分支.md)。

## 前一局部检查点：新鲜两层 guard、pending 调度与真实临界区（163 文件）

在已有 `V293OSSchedStorageConnect.v` 增加六个引理／定理，将两层实际 guard 接入同一 ready 关系的候选指针临界区。实际 `encrit` 后，才从该不变量共享存储尾部的完整有类型字节取得两个合法观察；frame 只保留环境绑定、无遮蔽与私有资源，不带旧 guard 值或读权限跨任务切换。两个观察都为零才执行已有主体并消费抽象 `sched`；任一非零则跳过主体、关闭同一 ready 不变量，保留 `sched;;aop`。返回路径实际 `excrit`；已删除当前线程的切换不返回，不声称其执行退出原语。

`V293_ready_OSSched_pointer_guards_observed` 给出固定关中断后观察的精确分支 continuation；`_guards_fresh` 和 `_guarded_critical` 的后置隐藏这些观察。**存在式后置不是共享字节返回后仍等于旧值，也不是完整上层延期／执行轨迹规格。** 开启中断入口不固定 guard、任务表、位图、目标或计数器。原 43 个声明头、精确增量整个声明／证明及另外 162 个活动源码保持不变；仍为 60 个 V293、103 个通用文件，不改冻结 C、配置、框架、端口或允许假设集合。

本轮前瞻协议实际通过：4 个独立字面接口及真实假设检查，源／见证／探针三模块 `coqchk`，同环境正向副本；5 项单因素负控均退出 1、严格命中指定声明。负控分别只省略外／内 guard、错误消费 disabled 分支的 `sched`、省略实际 `encrit` 或 `excrit`；信用是保留证明对该改动的指定拒绝，不冒称独立语义反例。实际假设并集仍仅经典逻辑和依赖函数外延性，原严格拒绝解析不变。旧指针分支的 5 根、旧指针临界区的 4 根均在当前输入重编通过。原连接门禁 `audit/logs/stage26-connect/run-20261028-082639/result.json` 退出 0：25 根接口／假设、`coqchk`、正向副本及 21 项指定负控全部符合预期。

局部 Python 测试 59 项通过；完整 Python 回归实际执行 559 项，253 次失败、1 次错误，全部 254 个失败／错误块均包含正式证据身份过期拒绝，不能给被遮蔽的下游机制授信用。增量 `make build` 退出 0，实际重编优先级边界文件；源／见证／探针的实际重编由前述协议承担。**没有执行当前 163 文件的干净全量门禁。** 项目范围审计与冻结源码只读重放退出 0，默认 `make audit` 仍退出 2，正式报告与覆盖 JSON 未改，八项受保护输入不变；全部成功及开发期失败日志保留。

逐路径／大小／SHA-256 确认后，清理本轮 50 个非交付 Coq 派生产物和 3 个一次性构造缓冲，共 53 文件、5,063,356 字节；790 个既有产物均保留，仅 `.Makefile.coq.d` 和 `.lia.cache` 随实际构建更新。新协议临时树 27 文件、5,536,360 字节及旧连接门禁临时树 99 文件、20,618,368 字节也已清单复核清理。源码、用户材料、依赖与成功／失败证据保留，两个当前报告的输入身份在清理后再次核对一致，工作树未提交。详见 `audit/logs/stage26-ready-guards/final-validation-summary.json` 及[中文程序／边界说明](docs/开发中/同一ready关系的指针条件分支.md)。

**仍是候选指针程序，冻结 C 仍比较优先级，没有被替换。** 尚未增加含本轮 guard 布局的完整物理入口／初始化可达性见证。准确缓存与冻结源码比较的对应、源码切换对应、ISR／API 保持性、上层延期规格、完整函数环境、初始化、最终源码级 `GOOD_OS` 及同程序 K1–K4 仍开放；六阶段覆盖仍为 `94 / 1 / 1 / 1 / 1 / 0`，uC/OS-III 未启动。

## 前一局部检查点：候选指针条件已接真实临界区与新鲜快照（163 文件）

在已有 `V293OSSchedStorageConnect.v` 增加 `V293_ready_OSSched_pointer_critical`：实际 `encrit` 后才绑定新鲜任务表、位图、优先级表、目标与 UINT32 计数器观察，再执行真实调用／目标赋值、指针条件与递增／切换；返回路径实际 `excrit`，恢复同一个 ready 不变量与 enabled OS 状态并消费抽象 `sched`。开启中断入口不固定上述共享值。

补齐了此前不能从 ready 不变量推出的 current 成员边界：普通成员使用 `switch_rule`，已删除 current 使用 `switchdead_rule` 得到 **`Afalse`（该线程不返回）** 后才弱化统一恢复后置，不暗加 `indom tasks tid`。`_total` 仅指成员情况完备，不声称终止性；删除路径不声称执行退出临界区。旧 **36 个引理／定理声明头**和精确增量整个声明／证明不变，抽取共同切换前置并复用同一分支实现。活动文件仍 **163（60 个 V293、103 个通用文件）**，仅这一个活动源码改变，其余 162 个哈希不变；新增 7 个引理／定理，不改冻结 C、框架或端口。

**仍是候选指针程序，冻结 C 仍按优先级比较。** 新鲜两层 guard／禁止调度的延期规格、准确缓存与源码切换对应、ISR／API 保持性、完整函数环境、初始化、源码级最终 `GOOD_OS` 和同程序 K1–K4 仍开放，uC/OS-III 未启动。没有新增 enabled 入口或删除任务的完整物理可达性见证；旧两模式局部入口见证不因此升级为初始化证明。六阶段覆盖仍为 `94 / 1 / 1 / 1 / 1 / 0`。

独立探针实际书写不返回切换、成员情况完备的指针分支、新鲜主体与临界区往返四项字面接口；前瞻协议检查实际编译／假设、`coqchk`、同环境正向副本和四项单因素负控，不放宽原严格拒绝解析与允许假设集合。新协议已退出 0：四根实际接口／假设检查、源／见证／探针三模块 `coqchk` 及同环境正向副本通过；四项负控均退出 1 并严格命中指定声明。假设并集仍仅经典逻辑和依赖函数外延性。上一轮指针探针的五根也在当前输入下实际重编通过。55 项局部 Python 测试通过；完整 Python 回归实际执行 555 项，253 次失败、1 次错误，全部 254 个失败／错误块均包含正式证据身份过期的拒绝，不给被提前拒绝的下游机制授信用。旧连接门禁 `audit/logs/stage26-connect/run-20261028-075351/result.json` 在当前输入下通过：25 根接口／假设、`coqchk`、同环境正向副本和 21 项指定负控，外层退出 0。增量 `make` 退出 0（更新依赖、无需重编），实际源／见证／探针重编由上述协议承担；不是当前 163 文件的干净全量验证。详见[指针条件与真实临界区](docs/开发中/同一ready关系的指针条件分支.md)及 `audit/logs/stage26-pointer-critical/`。

项目范围与冻结源码只读重放退出 0；默认 `make audit` 仍因正式证据身份过期退出 2，正式报告及覆盖 JSON 未改，八项受保护输入哈希不变。逐文件路径／大小／SHA-256 确认后，清理 47 个本轮新增非交付 Coq 派生产物、4,637,923 字节；790 个既有产物全部保留且大小／哈希均不变。新协议临时树 24 文件、4,038,118 字节及旧门禁临时树 99 文件、17,867,956 字节也已清单复核清理。源码、用户材料和全部成功／失败日志保留，两个当前报告输入在清理后再次核对一致；工作树仍未提交。详见 `final-validation-summary.json` 与 `cleanup-result.json`。

## 前一局部检查点：同一 ready 关系的候选指针条件链（163 文件）

在已有两个连接文件中提取共用前缀，并证明 `V293_ready_OSSched_pointer_conditional`：真实内部调用／目标赋值后，由同一空间尾状态读取目标与当前任务指针；相等时消费抽象自调度，不同时执行真实 UINT32 递增和普通切换。两个分支恢复同一个 ready 关系，恢复后不固定旧目标、任务表或计数器。活动源码仍为 **163（60 个 V293、103 个通用文件）**；另 161 个活动源码哈希未变。

**这是候选指针程序，不是冻结 C 的完整对应。** 冻结 C 仍比较优先级；准确缓存、源码切换对应和相关 ISR／API 保持义务没有消失。新接口显式要求私有 frame 排除 `OSTCBCur` 的局部遮蔽；该事实不能只由全局单元推出。两个既有入口的公开接口不变，单一物理见证提取为保留空局部环境的辅助引理，新探针在同一状态同时取得无遮蔽 frame、完整 ready 入口及任意 UINT32 计数器观察；覆盖自身就绪／当前等待两种模式，不代表完整物理 TCB 或初始化可达性。

原连接文件 **31 个声明头部及精确递增的整个声明／证明逐字不变**。第一次局部 Python 回归有 1 项文本测试失败：它仍在公开包装定理中寻找已提取的物理构造。修正后所有原同状态／计数器／ready 关闭断言仍在，改为检查实际辅助证明，并补查公开包装只丢弃空局部环境事实；另新增字面指针分支探针检查。原失败日志保留，不通过复制证明或删除不利断言制造通过。

本次检查结果见下方本轮验收记录。详见[指针条件的程序、证明与边界](docs/开发中/同一ready关系的指针条件分支.md)和 `audit/logs/stage26-pointer-branch/`。两层 guard／完整临界区、冻结源码对应、完整函数环境、初始化、源码级最终 `GOOD_OS` 和同程序 K1–K4 仍开放，uC/OS-III 未启动。六阶段覆盖仍为 `94 / 1 / 1 / 1 / 1 / 0`。

### 本轮验收与清理

新独立探针的 **三个字面接口、同状态入口和 frame 共五根**实际通过编译／假设检查；源、见证和探针三模块的 `coqchk`、同环境正向副本均退出 0。**四项单因素负控均退出 1，并在各指定声明被拒绝**；实际假设并集仍只有经典逻辑与依赖函数外延性，允许集合及严格拒绝解析不变。新协议外层退出 0。

原连接门禁在测试重构前、后各实际通过一次；后一次 `audit/logs/stage26-connect/run-20261028-072446/result.json` 固定当前输入，**25 根接口／假设、`coqchk`、正向副本及 21 项指定负控通过**，外层退出 0。两次历史结果分别保留，不把它们累计成更多独立控制。局部 Python 回归 **52 项通过**；Coq 增量构建退出 0（无需重编），实际源／见证／探针重编由上述门禁承担。当前 163 文件没有执行干净全量门禁或完整 Python 回归，不继承 162 文件历史快照的全量信用。

项目范围与冻结源码只读重放退出 0，八项受保护输入哈希不变；原工作树默认 `make audit` 仍因正式函数证据身份过期退出 2，未覆盖正式报告和覆盖 JSON。新一次性局部协议不是正式函数门禁的新验收机制。完整记录见 `audit/logs/stage26-pointer-branch/final-validation-summary.json`。

逐项复核路径、大小和 SHA-256 后，清理 **40 个新增非交付 Coq 派生产物，共 4,262,645 字节**；790 个既有派生文件全部保留，仅 `.Makefile.coq.d` 随实际依赖更新而改变。新协议临时树 24 文件、3,416,939 字节及两次旧门禁各 99 文件、15,175,905 字节均已按清单复核清理。源码、用户材料和全部成功／失败日志保留，两个当前局部报告的输入身份在清理后再次核实一致。第一次清理后的核对因报告相对路径写错退出 1；删除前的清单检查已完成，未重试删除，改用根相对路径后核对退出 0，失败记录保留。工作树仍未提交。

## 前一局部检查点：比较读取等价及单字节消融（163 文件）

新增 `V293OSSchedPointerCompare.v` 并登记到 `_CoqProject`，活动文件为 **163（60 个 V293、103 个通用文件）**。在同一任务表／位图／优先级表、准确当前任务关系及真实环境／内存读取前提下，证明优先级判断与任务指针判断具有相同的 `evalval` 和 `Tint32` 类型。当前任务允许等待；这是局部表达式对应，不是完整 C 程序模拟或已经采用的新切换实现。

独立探针检查三项字面接口，另有真实四块内存的单字节对照及同表任务关系实例，共 **5 个根**。保持目标和当前指针不变，仅把缓存由 4 改为 12，真实优先级判断由真变假，而指针判断仍为真；因此不能无条件擦除缓存准确性。实例不是完整物理 TCB 或初始化可达性证明。

本次源／探针编译、两模块 `coqchk`、同环境正向副本及探针均退出 0；**3 项单因素负控全部退出 1，并命中指定声明**，严格拒绝规则不变。实际假设并集仅经典逻辑和依赖函数外延性，允许集合未扩大。51 项既有局部 Python 测试通过，Coq 增量构建退出 0；这不是当前 163 文件的干净全量重放，也未重新执行完整 Python 测试。该一次性协议不是正式函数门禁新增的检查器。

项目范围审计退出 0；原工作树 `make audit` 仍因正式报告输入身份过期退出 2。冻结身份、正式报告、覆盖 JSON 和框架／端口关键输入未改，六阶段覆盖仍为 `94 / 1 / 1 / 1 / 1 / 0`。上一轮 162 文件完整验证已成为历史快照，其报告及哈希原样保留，不能给新增输入授予全量信用。

详见[调度比较的局部对应](docs/开发中/调度比较的局部对应.md)及 `audit/logs/stage26-pointer-compare/result.json`。下一步把指针条件连接到同一 ready 关系的条件分支，并证明所需源码状态对应；准确缓存的入口／切换返回义务、完整 `OS_Sched`、最终 `GOOD_OS`、同程序 K1–K4 均仍开放，uC/OS-III 尚未启动。

逐项复核路径、大小和 SHA-256 后，清理 35 个本轮新增非交付 Coq 派生文件、共 3,721,002 字节；另已核对并清理负控临时树 15 文件、230,712 字节。790 个既有派生文件全部保留，仅 `.Makefile.coq.d` 和 `.lia.cache` 内容随实际构建／证明更新并如实记录。源码和全部成功／失败日志保留，工作树仍未提交；详见本次 `final-validation-summary.json` 与清理清单。

## 最近完整验证的历史检查点：162 文件干净构建及证据隔离回归通过

在当时 162 文件源码不变的条件下，原样执行完整既有函数门禁的 `inspect` 和 `validate_record`：**162 个活动 Coq 文件隔离干净构建退出 0，354 条检查记录通过原验证器，17 次 `coqchk` 全部退出 0**。全程 395 个外部命令的输出与退出码均已记录，外层退出 0；最后核对的 198 项输入身份全部一致。没有拷贝原工作树的 Coq 编译产物。

随后只在隔离副本中使用这次真实生成的当前报告，并同步 `OSVersion` 覆盖行的报告哈希；全部源码、测试定义、阶段布尔值和拒绝规则不变。副本的 **`make audit` 退出 0，全部 551 项 Python 测试通过**。这次实际执行了此前被过期报告提前拒绝的下游测试，而不是推定它们通过。

**原工作树的默认审计仍指向过期的 stage25 报告；未覆盖旧报告、未修改覆盖 JSON，也未把隔离副本通过宣称为原工作树默认门禁通过。** 当时的机器可读报告另存为 `audit/function-evidence-stage26-replay.json`，仅是本次重放的交付副本，尚未切换默认报告路径。新局部文件进入了干净构建，不因此自动成为原门禁新增的独立接口或负控。

详见[本次完整重放报告](audit/STAGE26_CURRENT_REPLAY.md)。两次验证的临时树均在逐文件路径／大小／SHA-256 清单复核后清理，源码、既有依赖及全部成功／失败日志保留。整函数证明与覆盖没有升级：仍为 `94 / 1 / 1 / 1 / 1 / 0`，准确当前优先级同步、完整 `OS_Sched`、最终 `GOOD_OS` 及同程序 K1–K4 仍开放，uC/OS-III 未启动。以下失败数字保留为这次重放前的历史观测。

## 前一工作树检查点：已定位当前优先级同步边界，尚未补齐完整调度链

在下述关系条件检查点之后新增 `V293SwitchPriorityBoundary.v`，当时活动文件数为 **162（59 个 V293、103 个通用文件）**。最小物理实例证明：旧当前任务优先级 4、最高就绪目标优先级 12 时，真实指针写入及抽象当前任务更新后，独立优先级字节仍为 4，准确当前优先级关系被破坏；仅增加一次真实字节同步写入 12 后，该关系恢复。没有修改冻结 C、端口或框架，也没有采用额外同步实现。

有界 `GoodI` 障碍定理保留两个明确前提：候选不变量接纳此入口，以及它蕴含准确字节关系。**尚未证明完整 ready 不变量接纳此最小实例**；不能据此推翻原 ready 不变量的 `GoodI`，也不能认定真实 C 存在第三项漏洞。详见[任务切换与当前优先级边界](docs/开发中/任务切换与当前优先级边界.md)。

本次局部门禁通过：**5 个独立字面根、实际假设检查、`coqchk`、同环境正向副本及 3 项指定声明负控**；假设并集仅经典逻辑与依赖函数外延性。51 项局部 Python 测试通过，Coq 8.18 增量构建退出 0（实际重编此前清理的 4 个关系连接文件，新边界文件在局部门禁中已实际重编）；不是干净全量构建。

完整 Python 测试 **551 项，253 次失败、1 次错误**；254 个失败／错误块均包含旧正式证据输入身份过期的拒绝，没有其它失败块。项目范围审计与冻结源码只读重放退出 0；`make audit` 仍因过期证据退出 2。冻结 C、正式 JSON、端口及框架关键输入哈希保持不变，不给被提前拒绝的下游机制授信用。

本次检查结果及清理记录见 `audit/logs/stage26-current-priority/`，局部门禁报告为 `run-20261028-054343/result.json`。下述 25 根／21 项、17 根／11 项及 544 项测试数字是前一个输入身份下的历史检查点，不给新文件自动授予验收信用。新增局部门禁同样不刷新正式函数证据；最终 `GOOD_OS` 和同程序 K1–K4 仍开放，uC/OS-III 尚未启动。

逐项复核路径、大小和 SHA-256 后，清理 30 个本轮新增非交付 Coq 派生文件，共 3,475,276 字节；保留源码、可复用检查器、依赖及全部成功／失败证据。790 个既有派生文件均保留，其中仅 `.Makefile.coq.d` 随新活动文件更新，其余哈希不变。仍为未提交开发态，详见本次 `final-validation-summary.json` 和 `cleanup-result.json`。

## 前一局部检查点：同一关系已接真实条件双分支

stage25 之后新增共享数组前缀、关闭入口及 `V293OSSchedStorageConnect{,Witness}.v`，登记到 `_CoqProject`；活动文件数为 161（58 个 V293、103 个通用文件）。旧两层 guard 组合仍使用类型存储不变量。

新关系不变量联系物理就绪位图、实际 13 槽优先级表与唯一共享任务槽中的 `tasks`，已有实际具体／抽象当前指针更新保持性及 `GoodI`。此前已有实际 `encrit`／调用／赋值／归还同一关系／实际 `excrit` 的局部闭合程序。本轮在同一物理布局上接入真实优先级条件：不同分支调用／目标赋值后实际 UINT32 模递增并普通切换，相同分支从同一任务表证明当前任务最高就绪并消费抽象 `sched`；两支恢复的是同一个 ready 关系，不擦除为旧类型不变量。恢复后不固定旧共享观察、计数器或目标。

**准确当前优先级仍是明确的局部前提，不是已闭合的整函数不变量。** 当前 ready 关系不含 `OSPrioCur = 当前任务优先级`，普通 `switch_rule` 只更新当前指针和抽象当前任务，不能自动保持该字节关系。本轮 `V293_ready_OSSched_conditional` 显式要求关闭中断后这个入口状态的 `V293_current_task tasks tid nc`，并从同一物理布局读取准确 `nc`；不把它冒充为由实际 `encrit` 自动取得的事实，不添加隐式同步、不改框架或冻结 C／端口。

抽象自调度执行提取为单份 `V293_self_schedule_consume`，旧 typed 和新 ready finisher 共同复用；旧 30 个组合／见证引理和定理头部不变，实际模递增执行证明体逐字不变。新条件入口见证复用同一个实际物理状态，同时保留准确当前字节与任意 UINT32 计数器观察，覆盖当前任务就绪／等待及任意事件表／时间／continuation；不是初始化可达性证明。

**两层 guard 和完整临界区尚未接入这条关系条件链。** 源码／port 对应、`OSPrioCur` 同步、相关 ISR／API 保持性、完整物理 TCB／事件布局、完整函数环境与初始化仍开放。详见[当前检查点、单因素验收及边界](docs/开发中/同一共享布局的两层调度判断.md)。

本次局部验收：新组合 25 根独立字面接口、实际假设、`coqchk`、同环境正向副本通过，21 项负控全部命中指定声明；原临界区前缀复核 17 根／11 项指定负控通过。两项门禁分别通过仍不等于完整函数已组合。实际假设并集仍为经典逻辑和依赖函数外延性，允许集合未扩大；44 项局部 Python 测试通过。Coq 8.18 最终增量构建退出 0、无需重编，不是干净全量构建；本轮源文件、见证、探针在局部门禁中已实际重编。

新增四项控制分别只省略新条件分支递增、只省略切换、只擦除实际当前字节观察、只取消准确当前任务前提；原自调度消耗控制移至真正执行机制，严格拒绝解析不变。恢复规格不固定计数器，省略递增控制仅说明保留证明对程序敏感，精确计数性质来自独立 `_under` 接口，不夸成恢复规格排除所有不计数实现。全部编译／探针失败日志保留，不给失败运行的下游授予信用。

**全量仍未通过。** 完整 Python 测试 544 项，253 次失败、1 次错误；254 个失败／错误块均包含旧正式函数证据输入身份过期的提前拒绝，其他失败块为空。项目范围审计与冻结源码只读重放通过；`make audit` 覆盖子门因同一身份过期退出 2。旧正式 JSON、冻结源码、补丁和账面六阶段覆盖 `94 / 1 / 1 / 1 / 1 / 0` 未改，不用历史 stage25 报告或本次局部门禁冒充当前完整函数验收。

本次保持未提交开发态。按逐项路径、大小和 SHA-256 复核后清理 30 个本轮新增 Coq 派生文件、共 3,952,463 字节，既有 785 个编译文件与全部成功／失败证据保留；详见 `audit/logs/stage26-ready-conditional/final-validation-summary.json`、`cleanup-plan.json` 和 `cleanup-result.json`。前缀检查器原工具／shell 句柄丢失时子进程仍实际运行，未重复启动；其最终报告、PASS 输出与各实际子命令退出码完整保留，外层退出码未捕获，不推定为 0。组合门禁外层退出 0 已捕获。

源码级 `GOOD_OS`、同程序 K1–K4 尚未完成，uC/OS-III 未启动；以下历史阶段保留当时的验收语境。

当前状态：**源码身份已冻结，框架内存修复已通过完整验收，首个真实函数已完成翻译、局部证明与单函数 API 组件连接，具体源码级整核验证仍未闭合**。

第五阶段已实际从原 `MemoryNotFull` 公理与允许的全满函数推出 `False`。第六阶段将块标识上界封装到内存类型，删除错误公理并恢复原分配与 soundness 证明链；109 文件干净构建和完整门禁通过，剩余逻辑假设如实列出。完整验收结果见[第六阶段报告](audit/STAGE06_FRAMEWORK_REPAIR.md)。历史失败证据保持不变，不用局部通过代替最终门禁。

## 已具备的基础

- 当前活动内核专用证明树仅为 `certiucos/v293/`。
- 保留版本无关的 `framework/` 与 `tactics/`。
- 上游提交及 15 个 `Source/` 文件的 SHA-256 身份已记录。
- 固定配置已记录；范围外可选功能保持关闭。
- 已有等待结果、嵌套互斥锁优先级重算、调度锁定自删除拒绝行为的小模型和性质证明。
- 已保留针对新版嵌套互斥锁问题的上游执行证据，作为后续审计输入。
- 两项授权修复已有可重放的完整 C 补丁，已在锁定源码副本中集成并完成受控边界回归；原始 checkout 不变。

以上为现有基础，不代表源码对应关系已被证明。

## 尚未完成

- 修复后的源码身份及完整位置清单已冻结；`OSVersion` 有完整的受限 AST 检查翻译，`OS_SchedNew` 有分离资源、两次赋值及 void 返回的函数体 Hoare 检查点；完整 C 到 CoqImp 对应仍未完成。
- 其余 93 个函数尚未完成函数级六门覆盖；其中 `OS_SchedNew` 已有数学选择性质、实际读取、两次赋值执行、函数体 Hoare，以及构造器资源交接和参数化单函数 `WFFunEnv` 检查点。另有调用方前两句顺序 Hoare、两层条件、优先级比较和计数器模加一的组合、调用方预留另一半当前指针后的完整 `SWPRE_NDEAD` 及整个前置可满足见证。非空共享核心现已证明实际指针／抽象更新保持、`GoodI` 和等待／已删除两种同状态见证；唯一共享任务表已借给真实调用与目标赋值再归还，完整入口在两种当前任务模式下可满足。新的共享数组、计数器及准确当前优先级布局已连接真实前缀、比较、模递增／普通切换与抽象自调度，两层 guard 也已接回且完整入口同状态可满足，但该 guard 主体尚未接入新的关系临界区链；新增关系前缀闭合片段不能替代它，完整物理 TCB／就绪结构不变量仍缺；准确全局布局和完整调用方仍未完成，资源交接不等于新增具体分配／释放执行轨迹。
- 仅 `OSVersion` 接入单函数 API 单元；完整 API 表及整体程序连接仍未完成。
- `V293_low_level_os_code`、`V293_os_spec`、`V293_ucos_init` 及最终 `GOOD_OS` 证明尚未完成。

`audit/coverage.json` 当前有完整 94 行，六阶段统计为 `94 / 1 / 1 / 1 / 1 / 0`。`OSVersion` 到达单函数单元的 `component_linked`，其余仅 `located`；不能据此计算整核证明完成百分比。原上游清单仍保留 92 个定义。

## 第一阶段：基础检查恢复

截至 2026-10-26，本机已从 Coq 8.20.1 降到指定的 8.18.0。已修复证明文件的直接导入与参数引入问题，未修改模型、规格或 C 行为。

- 审计和版本回归：14 个测试通过。
- `make audit`：通过。历史资料不再被误当活动输入，真实旧目标／归档构建路径和证明洞的反向测试仍保持拒绝。
- 六文件隔离检查：通过；三个小模型根定理均无全局假设，相应模块 `coqchk` 通过。
- 上游源码与配置哈希：通过；源码位于本机忽略目录，可重新获取。
- Coq 8.18.0 干净全量构建：通过。107 个活动 `.v` 均从源文件编译，不复制旧产物或归档资料，不使用栈／GC 包装器。

详细证据与静态检查边界见 [第一阶段报告](audit/STAGE01_BASELINE.md)，入门解释见 [第一阶段教学](docs/阶段/01-Coq818与基础检查.md)。

[初始基线报告](audit/BASELINE_REPORT.md) 保留修复前失败，不回写为成功。原始 `work-prompt.md` 声称的后期状态仍缺少相应实物；不采纳其七项修复或函数数。

## 第二阶段：实际源码清点

固定配置上游由 Clang 实际预处理并解析得到 92 个 C 定义（65 public／27 internal），GCC 独立预处理和语法检查一致；16 个声明级 CPU／切换／临界区边界单独记录。Ctags 全分支源码索引另有 34 个未进入当前配置的定义，不代表全配置都得到验证。

清单 `audit/source-inventory.json` 明确为修复前上游，不能计入修复后的函数覆盖。当时新增 12 项源码集成与反向检查，合计 26 项测试。范围、命令结果与局限见 [第二阶段记录](audit/STAGE02_SOURCE_INVENTORY.md)，逐步解释见 [第二阶段教学](docs/阶段/02-源码配置与函数清单.md)。

## 第三阶段：两项 C 修复与真实反例回归

两份完整补丁分别只改 `os_mutex.c` 和 `os_task.c`。互斥锁补丁保存基础优先级、保留剩余贡献，并保持重定位时的就绪／等待成员关系；自删除保护在首次状态修改前返回已有错误码 50。旧算法片段已由补丁替代，不新增公共 API 或 TCB 字段。

- 23 个场景，四种补丁组合，GCC／Clang 与 `-O0`／`-O2`：368 次执行符合矩阵预期。
- 两项都接入的 92 次执行全部通过；原上游及单补丁版本的 112 次预期失败完整保留，不算成内核通过。
- K1、K2 的指定路径在原上游就通过，未为它们增加补丁。
- 11 项逐机制消融／故障注入命中各自的指定断言，防止把上游某个早期失败误当成下游机制得到检验。
- 2 项边界测试确认配置漂移不被覆盖，补丁不能修改第三个源码文件。测试总数现为 40。

执行使用 32 位无 libc 程序和显式模拟 CPU 边界，不是真实任务栈或异步中断执行证明。补丁产物哈希见 [JSON 证据](audit/c-regressions.json)；具体结果、首次夹具错误与局限见 [第三阶段报告](audit/STAGE03_C_REPAIRS.md)，学习入口见 [第三阶段教学](docs/阶段/03-真实C回归与授权修复.md)。最终修复后清单、源码冻结、共享不变量、源码翻译与整体证明仍开放；覆盖仍为 0。

## 第四阶段：修复后源码冻结与完整位置证据

- 从锁定上游重放两项补丁，全部输出文件与第三阶段 C 报告身份相同；不改原 checkout、补丁或既有证据。
- 修复后实际预处理清点 94 个定义（65 public／29 internal）、16 个声明边界、34 个未配置目录索引定义。
- 仅两个静态 helper 新增、六个既有函数内容改变；已有函数接口、生效配置与边界不变。
- `FROZEN_SOURCE.json` 绑定源码／配置／端口与清单，`source-freeze-check` 只读重放比较。
- 覆盖清单 94 行全部只完成 `located`；严格审计拒绝错位置、缺函数、跳级与没有检查器的后阶段完成声明。
- 新增 22 项正反测试，全套 62 项；Coq 文件未改变，全部源码对应及函数／整体证明仍开放。

详见 [第四阶段报告](audit/STAGE04_SOURCE_FREEZE.md) 与 [第四阶段教学](docs/阶段/04-源码冻结与真实函数定位.md)。此前各阶段记录保留其当时状态，不改写为后来的完成结果。

## 第五阶段：内存信任失败证据与显式边界接口

- 在隔离模块重编原内存源码，构造全满函数并实际得到 `False`；只删除 `MemoryNotFull` 的单因素对照仍接受满内存见证，拒绝同一矛盾证明。
- 新增 `memory_bound.v` 的 11 个接口，证明空内存可满足边界、边界推出 fresh，以及更新／分配／释放保持或扩大边界。
- 新接口的假设闭包不含 `MemoryNotFull`，仍含经典逻辑与依赖函数外延性；对应对象通过 `coqchk`。不声称完全无公理。
- 原内存表示、公理和两处无条件 fresh 引理未修改；尚需迁移初始化、共享／分片内存、操作语义和 soundness。
- 专门门禁 `check-framework-trust` 明确失败；正向 `check-memory-bound` 仅检查新接口，不替代全框架门禁。
- 解析回归新增 3 项，全套 65 项；C 源码、冻结身份和六阶段覆盖保持不变。

已发布的真实诊断见 [JSON 证据](audit/memory-trust.json)，详细验收见 [第五阶段报告](audit/STAGE05_MEMORY_TRUST.md)，逐步学习见 [第五阶段教学](docs/阶段/05-内存假设审计与有界分配接口.md)。历史记录保留当时结论，不反向改写。

## 第六阶段：框架内存表示与完整证明链修复

- 合法内存携带块标识严格上界，各原语证明闭包；`memory_has_fresh_block` 与 `memory_not_full` 由此推导，两处 `fresh_exist` 不再使用错误公理。
- 保留 11 个边界根，新增 20 个独立 raw 算法对应／可满足根；包括 `join` 双向对应、任意长度分配／写入／释放、满映射不可表示及具体成功／拒绝见证。
- 13 个真实框架根覆盖分配存在性、任务步进、`RuleSound`、`verified_os'` 与 `Soundness`。完整门禁和依赖闭包 `coqchk` 通过；源码输入 SHA-256 保存在新报告中，原失败 JSON 不变。
- 新边界／表示根实际假设并集为经典逻辑与依赖函数外延性；框架根另使用 `Eqdep.Eq_rect_eq.eq_rect_eq`。公共库和映射模块的重复外延性公理已改为同规格证明，不扩大允许列表。
- 实际全满构造器拒绝、仅中和边界的单因素对照、三个指定定理处的算法故障，以及旧逻辑路径的公理移除对照均符合预定结果。未知 Unicode 假设的真实漏检已修复。
- 109 个活动 Coq 文件从无旧产物／参考资料的目录完整构建通过；全套 73 项 Python 测试、静态／覆盖审计、冻结身份复核、368 次 C 对照和六文件小模型检查均通过。
- 本次没有修改 C 源码、授权补丁、固定配置、函数位置或覆盖；仍为 `94 / 0 / 0 / 0 / 0 / 0`，具体初始化和最终 `GOOD_OS` 仍开放。

机器可读结果见[框架修复 JSON](audit/framework-memory-repair.json)，完整命令与边界见[第六阶段报告](audit/STAGE06_FRAMEWORK_REPAIR.md)，学习见[第六阶段教学](docs/阶段/06-修复框架内存表示与证明链.md)。

## 第七阶段：首个真实函数的源码翻译与局部证明

- 重放冻结源码及 Clang／GCC 预处理，确认 `OSVersion` 实际常量为 29300，保留无符号 32 → 16 位返回转换；不因发行版名称而猜成 29301。
- 受限 AST 生成器拒绝额外语句／参数／属性、错类型或漏转换；与提交的 CoqImp 程序逐字比较。
- 独立规格与 `V293_OSVersion_local_hoare` 保证精确返回值并保留任意 frame；另有后置提取和有限步执行／内存不变根。
- 专用检查隔离干净构建全部 112 个活动文件；三个根的独立接口类型、实际假设与依赖闭包 `coqchk` 通过。假设并集为经典逻辑与依赖函数外延性，未扩大框架允许列表。
- 常量变异失败于指定结果证明；`False` 前置条件的空洞定理先编译成功，再被独立接口拒绝。新增 13 项 AST 测试和 5 项覆盖／证据反向测试，全套 91 项。
- 新报告绑定当前活动源码和工具身份；静态覆盖审计只据专用报告计入前三个后续阶段，不允许组件／整核阶段偷跑。
- C 前端与小型生成器仍是受信任对应工具；没有完整 C 编译器正确性定理。最终具体程序、规格、初始化、API 组件及 K1–K4 源码级连接仍开放。

详见[第七阶段报告](audit/STAGE07_FIRST_FUNCTION.md)、[机器证据](audit/function-evidence.json)和[第七阶段教学](docs/阶段/07-首个真实函数的局部证明.md)。第六阶段报告继续保留其 109 文件历史快照，不以新结果回写。

## 第八阶段：首个真实 API 组件

- `V293_OSVersion_api_contract` 连接任意包含准确函数的 API 表与框架生成的调用前后置，复用原稳定局部接口。
- `V293_OSVersion_api_rule` 建立真实 `APIRule` 和定义域／参数／返回类型对应；空参数构建器确实返回 `Some`。
- 113 文件隔离干净构建、六个实际根的假设与依赖闭包 `coqchk` 通过；假设并集仍为经典逻辑与依赖函数外延性。
- 独立探针固定非空函数表与精确返回规格；原两项局部控制保留，新增错 API 结果、删除入口两项指定语义拒绝。
- 全套 95 项 Python 回归通过，包括过期组件、冒领覆盖、组件失败和缺失指定负控制的反向测试。
- 只提升 `OSVersion` 的组件阶段，不提升整体阶段，也不让其他函数借用覆盖。旧阶段报告和冻结 C 身份不变。
- 已实际核对后续 `OS_SchedNew` 的 AST 和 256 项查表初始化器；65,528 个状态的消融排除了局部决定不需要的高位清零限制。此有限实验不是 Coq 证明，不提高该函数覆盖。

见[第八阶段报告](audit/STAGE08_API_COMPONENT.md)、[本轮证据](audit/function-evidence-stage08.json)及[教学](docs/阶段/08-从局部证明连接API组件.md)。两个阶段总目标仍活动，uC/OS-III 尚未启动。

## 第九阶段：调度器源码绑定的读／写执行检查点

- 对实际 `OS_SchedNew` AST、局部声明、类型转换、引用身份及 256 项查表定义进行受限检查；GCC／Clang 预处理一致，并与 Coq 程序和数据逐字比较。
- `Nat.testbit` 独立规定就绪性，Coq 全称证明选择结果就绪、最小且在 0–12 范围；不要求局部清除 13–15 位。
- 真实 `evalval`／`evaltype` 从数组地址及字节读取计算结果；`cstepstar` 执行两次赋值，除两个精确字节地址外内存保持。只读输入与可写输出有实际可满足见证。
- 118 个活动文件隔离干净构建；十个根、独立接口和依赖闭包 `coqchk` 通过。实际假设并集仍为经典逻辑与依赖函数外延性。
- 五项指定语义控制分别检验查表、移位、组一致性、非空及写权限；原 `OSVersion` 的六个根与四项控制继续通过。
- 本轮不是函数 `InfRules`／Hoare 证明：局部变量生命周期、共享分离资源、关闭中断不变量和内部组件仍开放。六门覆盖保持 `94 / 1 / 1 / 1 / 1 / 0`，不借辅助定理提升覆盖。

见[第九阶段报告](audit/STAGE09_SCHEDULER_UPDATES.md)、[新机器证据](audit/function-evidence-stage09.json)及[实际内存教学](docs/阶段/10-调度器真实内存读取与两次赋值.md)。uC/OS-III 仍未启动，总目标保持活动。

## 如何更新进度

每个配置后函数必须依次获得真实证据：

`located → modeled → specified → local_hoare → component_linked → full_target_linked`

新增辅助引理或独立模型不自动提升函数覆盖。只有连接到当前冻结源码与最终程序的证据才能计入对应阶段。

## 第十阶段：分离资源与函数体 Hoare

新增 `V293OSSchedNewHoare.v` 与 `V293OSSchedNewWitness.v`：实际只读表／行／组资源推出真实读取，两个可写字节经 `assign_rule` 依次更新，再由返回规则连接完整函数体。主接口保留任意调用方的 `CurLINV` 与 frame；另有具体有界内存证明空间前置可满足，避免仅以互相可能冲突的读取等式当见证。

完整验收范围和实测结果见[第十阶段报告](audit/STAGE10_SCHEDULER_BODY_HOARE.md)。新检查器另写预期资源和实际函数体类型，并检查删除输入资源、去掉局部写权限、错误输出后置以及额外 `False` 前提四项控制；不以早期拒绝冒充下游义务。旧阶段九五项语义控制及 `OSVersion` 根／组件控制全部保留。

120 个活动 Coq 文件空目录重编通过；调度器十五根与原六个函数／组件根的独立接口、假设及 `coqchk` 通过，实际假设并集仍仅含经典逻辑与依赖函数外延性。143 项 Python 回归、静态审计、源码冻结、368 次 C 矩阵重放比较及小模型检查均通过；新记录为 [function-evidence-stage10.json](audit/function-evidence-stage10.json)。

这是**函数体检查点而非完整内部函数证据**，覆盖仍为 `94 / 1 / 1 / 1 / 1 / 0`。下一步在同一个函数上连接 `BuildPreI`／`BuildRetI`／`WFFunEnv`、局部变量生命周期和真实共享不变量，最终 `GOOD_OS` 仍未闭合。阶段七／八／九 JSON 保留历史，不回写；新证据使用 stage10 文件。

## 第十一阶段：内部构造器与参数化单函数环境

新增 `V293OSSchedNewInternal.v` 与 `V293OSSchedNewInternalWitness.v`：对外 `funasrt` 不包含局部地址，以动态逻辑参数关联两行快照与抽象操作；由准确局部定义域证明无全局遮蔽，连接真实 `BuildPreI`／`BuildRetI`，返回时交还局部可写字节与绑定。四个稳定根覆盖内部契约、非空单函数 `WFFunEnv`、构造器成功以及整个入口前置的实际可满足性。

122 个活动文件空目录重编、四根独立接口／选择器／假设和 `coqchk`、五项指定单因素控制全部通过。额外 `False` 前提和全 `Afalse` 选择器的变异先编译成功，再由独立探针拒绝；同样隔离的原版先通过，不借下游早期失败充数。原调度器十五根／九项控制及 `OSVersion` 六根／四项控制完整保留并通过。实际新增根假设并集仍为经典逻辑和依赖函数外延性。

158 项 Python 回归、静态审计、源码冻结、368 次 C 矩阵重放比较及小模型检查全部通过。新建 [function-evidence-stage11.json](audit/function-evidence-stage11.json)，旧阶段记录不回写；六门布尔值和函数定位不变，仍为 `94 / 1 / 1 / 1 / 1 / 0`。报告见[第十一阶段验收](audit/STAGE11_SCHEDULER_INTERNAL.md)，入门见[第十二课](docs/阶段/12-内部函数构造器与WFFunEnv.md)。

这只是**构造器资源交接与参数化内部组件检查点**，不是新增具体分配／释放轨迹，也不是实际内核组件已完成覆盖。真正的共享不变量、准确布局、`OS_Sched` 调用和 TCB／优先级表关系仍开放；下一步继续同一调用链。最终源码级 `GOOD_OS` 及同程序 K1–K4 尚未闭合，uC/OS-III 未启动，总目标保持活动。

## 第十二阶段：内部调用规则与真实任务指针读取

继续同一 `OS_Sched` 调度链：精确核对整个调用方的配置后 AST，只发射未锁定分支最前面的内部调用和指针赋值。新增真实 `call_rule` 实例、全称位图／抽象任务／优先级表关系、`GoodSched`、13 项指针表分离读取与实际可满足见证。读取结果连接的是同一状态中的抽象 TCB 表，不是另给一张与状态无关的表。

127 个活动 Coq 文件正式空目录重编通过；五个新增根的独立接口、实际假设、依赖闭包 `coqchk` 与五项指定单因素控制全部通过。原调度器十五根／九项控制、内部组件四根／五项控制和 `OSVersion` 六根／四项控制均保留并通过。新增根实际假设并集仍为经典逻辑与依赖函数外延性；191 项 Python 回归、工程／覆盖审计、源码冻结、368 次 C 矩阵证据重放及小模型检查均通过。新证据为 [function-evidence-stage12.json](audit/function-evidence-stage12.json)，旧 JSON 不回写。

当前是**调用规则与表达式读取检查点**，不是这两句已组合的 Hoare；指针赋值、临界区令牌和实际 TCB 状态／共享不变量仍开放。正式结果见[第十二阶段报告](audit/STAGE12_SCHEDULER_CALLER.md)，逐步入门见[第十三课](docs/阶段/13-内部调用与最高就绪任务表读取.md)。不提高任何函数覆盖，仍为 `94 / 1 / 1 / 1 / 1 / 0`；下一步继续两句的资源交接与顺序 Hoare。最终 `GOOD_OS` 及同程序 K1–K4 仍未闭合，uC/OS-III 尚未开始，总目标保持活动。


## 第十三阶段：内部调用与指针赋值的顺序组合

`V293_OSSched_unlocked_prefix_hoare` 用框架真实调用／赋值／顺序规则，连接 `OS_SchedNew();` 与 `OSTCBHighRdy = OSTCBPrioTbl[OSPrioHighRdy];`。从内部调用后置直接推出优先级实际读取，再从同一状态的表资源计算指针并写入；后置保留抽象任务表、调用方资源及最高就绪任务性质。另有指针赋值稳定接口，以及把全部输入、当前任务、任务表和两个可写输出放在同一状态的完整前置见证。

129 个活动文件空目录重编、三根独立接口／假设审计／`coqchk` 及四项指定控制全部通过；旧阶段全部根和控制保留并通过。210 项 Python 回归、工程／覆盖审计、源码冻结、368 次 C 矩阵证据重放及小模型检查也通过。新建 [stage13 机器证据](audit/function-evidence-stage13.json)，旧记录不覆写。结果见[检查点报告](audit/STAGE13_SCHEDULER_PREFIX.md)；中文学习见[第十四课](docs/阶段/14-把内部调用与指针赋值接起来.md)。四项指定控制检查桥接读取、输出写权限、语句顺序及额外 `False` 前提；不会以早期拒绝替代下游检查。

覆盖不增加，仍为 `94 / 1 / 1 / 1 / 1 / 0`。此检查点没有包含两层 guard、计数器、切换、临界区令牌或真实 TCB 字段；共享不变量、完整内部环境、初始化、`GOOD_OS` 与同程序 K1–K4 仍开放。uC/OS-III 未启动，总目标保持活动。


## 第十四阶段：两层调度条件与开放后续语句

`V293_OSSched_interrupt_skip` 证明外层中断嵌套非零时无需锁读取或主体契约；`V293_OSSched_guards_rule` 证明仅两个字节均为零才进入主体，其余路径保持完整前置。组合根接已有两句顺序 Hoare，后续 `suffix` 的 Hoare 仍作为显式开放义务，未冒充计数器／切换已完成。新见证对任意两个合法字节值构造同一状态中的整个新前置；旧见证内部 helper 保守泛化环境，旧稳定根类型不变。

132 个活动文件空目录重编、四个新根的独立接口／假设／`coqchk` 和四项指定控制全部通过；旧 33 根及 27 项控制保留并通过。正式记录 202 条命令、31 次预定拒绝。新增根实际假设并集仍仅为经典逻辑和依赖函数外延性。230 项 Python 回归、静态／覆盖审计、冻结身份、368 次 C 矩阵和六文件小模型检查通过。

新记录 [function-evidence-stage14.json](audit/function-evidence-stage14.json)，旧 JSON 不覆写。完整边界及修正过的同名命令标签问题见[第十四阶段报告](audit/STAGE14_SCHEDULER_GUARDS.md)，学习见[第十五课](docs/阶段/15-调度条件与短路分支.md)。覆盖仍为 `94 / 1 / 1 / 1 / 1 / 0`。接下来继续优先级比较、计数器、切换、临界区和真实共享不变量；最终 `GOOD_OS` 与同程序 K1–K4 仍开放，uC/OS-III 未开始，总目标保持活动。


## 第十五阶段：优先级比较与无符号计数器

继续同一 `OS_Sched`：从真实字节资源读取最高就绪优先级和当前优先级，证明 `!=` 的逻辑非相等规范化；用真实赋值规则证明 32 位无符号计数器模加一，并接入已有内部调用、指针赋值与两层 guard。相同优先级不递增，后置保留此前指针赋值；不同优先级先递增，真正切换仍是显式 continuation 义务。最大值加一为零，没有“不溢出”前提；该源码对应仍是受信任受限 AST 检查，不是已验证编译器。

135 个活动文件空目录重编、七个新增根的独立接口／假设／`coqchk` 及六项指定控制全部通过；旧 37 根和 31 项控制保留并通过。正式记录 223 条命令，其中 37 次预定拒绝。两个额外前提控制（排除最大值、增加 `False`）均先通过三个新模块含见证，再由固定接口拒绝。新增根实际假设并集仍仅为经典逻辑和依赖函数外延性。257 项 Python 回归、静态／覆盖审计、冻结身份、368 次 C 矩阵及六文件小模型检查均通过。

新建 [stage15 机器证据](audit/function-evidence-stage15.json)，旧 JSON 不覆写；完整边界见[第十五阶段报告](audit/STAGE15_SCHEDULER_CHANGE.md)，中文续步见[第十六课](docs/阶段/16-优先级比较与切换计数器.md)。整个新空间前置对任意三个合法字节和任意计数器可满足，但当前优先级尚未与当前 TCB 对应，不能将见证当作完整合法运行态不变量。

六门覆盖仍为 `94 / 1 / 1 / 1 / 1 / 0`。下一步继续真实切换所需当前任务成员／优先级／权限、目标调度关系和共享不变量，然后处理临界区与程序连接。最终 `GOOD_OS`、同程序 K1–K4 和后续 uC/OS-III 总目标仍开放。

## 第十六阶段：当前任务关系与空间切换目标

新增 `V293_OSSched_current_target`，以同一任务表／优先级表证明选中指针等于当前指针，当且仅当选中优先级等于当前优先级；当前任务允许已进入等待。`V293_OSSched_current_tail_entails` 从原实际后置提取当前成员、不同目标、`AHprio` 与完整可写全局目标指针。最终前缀接口将这些资源交给仍开放的真实切换 continuation，不增加整段切换 oracle。

完整前置见证同时覆盖相同目标和当前任务等待时的不同目标；任意合法两个 guard 字节和任意计数器均可共同存在。137 个活动文件正式空目录重编通过；四根固定独立接口、实际假设、`coqchk` 和五项新增控制通过，旧 44 根／37 项控制完整保留。正式 235 条命令中 193 次成功、42 次预定拒绝，无非预期失败。实际新增根假设并集仍仅为经典逻辑与依赖函数外延性；新建 [stage16 机器证据](audit/function-evidence-stage16.json)，旧 JSON 不回写。278 项 Python 回归、工程／覆盖审计、冻结身份复核、368 次 C 矩阵证据重放及六文件小模型检查均通过。

`SWPRE_NDEAD` 的中断清理与当前指针写权限、`SWINVt`、真实 TCB 字段／共享不变量和抽象动作仍开放。合法自删除后的当前任务可能已不在表中，必须后续单独连接 `SWPRE_DEAD`／`switchdead_rule`；本轮成员前提不适用于该路径。函数覆盖不增加，最终 `GOOD_OS`、同程序 K1–K4 及后续 uC/OS-III 总目标保持活动。中文续步见[第十七课](docs/阶段/17-当前任务与切换目标.md)，完整边界见[本轮报告](audit/STAGE16_SCHEDULER_CURRENT.md)。


## 第十七阶段：内部调用保留切换不变量与动态栈

由同一 `OS_SchedNew` 的真实两次赋值与返回，证明 `SWINV I ** (Ais stack ** Acs critical)` 在内部契约内保持。动态快照作为每次调用的逻辑参数；使用 `BuildPreI`／`BuildRetI`、非空单函数 `WFFunEnv` 和真实 `call_rule`，接回原两层 guard、目标指针赋值、优先级比较与计数器前缀。仅普通外部 frame 要求 `GoodFrm`，不对中断／临界区资源强加不可能满足的 frame 前提。

新完整前置在空不变量／空栈 fixture 中可满足，并保留相同目标和当前任务已等待的不同目标两种场景；它不是实际初始化、非空临界区栈可达性或真实共享不变量见证。切换 continuation 仍显式开放。

139 个活动 Coq 文件空目录重编、7 根独立接口／选择器／实际假设及 `coqchk`、5 项新增指定单因素控制全部通过；旧 48 根／42 项控制保留。后三项控制先编译核心及见证，再由独立探针拒绝忽略临界区快照、额外 `False` 前提或非法 frame 前提。正式共 250 条命令：203 次成功、47 次预定拒绝。实际新根假设并集仍仅为经典逻辑和依赖函数外延性。

298 项 Python 回归、工程／覆盖审计、冻结源码复核、368 次 C 矩阵重放及六文件小模型检查通过。覆盖记录引用更新时的字段笔误已修复并保留首轮失败日志，未回写正式证明结果。新证据为 [function-evidence-stage17.json](audit/function-evidence-stage17.json)，SHA-256 `f9bc7264766bc728934178064e0b9c9e23039b86c5e01f78f00385fbd31e487e`；旧 stage16 记录不变，六门覆盖仍为 `94 / 1 / 1 / 1 / 1 / 0`。

当前指针完整写权限、真实 TCB／共享不变量、临界区入口／出口、实际切换、完整函数环境与初始化、最终 `GOOD_OS` 和同程序 K1–K4 仍开放；自删除后的当前任务须单独接 `SWPRE_DEAD`。uC/OS-III 未启动，两阶段总目标继续活动。详见[本轮审计](audit/STAGE17_SCHEDULER_CRITICAL.md)及[第十八课](docs/阶段/18-让中断与临界区资源穿过内部调用.md)。本轮确认后清理 60 个任务构建产物和 5 个一次性文件，源码、证据、日志及既有依赖保留。


## 第十八阶段：当前指针完整权限与实际切换前置

同一全局环境保证两个当前指针半权限的存在类型一致，再由框架权限合并得到完整写权限。调用方显式预留第二半并让其穿过已有内部调用、两层 guard、目标赋值、比较和计数器更新；从实际尾部资源推出完整 `SWPRE_NDEAD`，没有把它作为新的外部 oracle。最终接口交付原后置与切换前置的同状态合取，仍保留显式 suffix Hoare 义务。

新完整入口见证从一个可写当前单元分出两半，同时覆盖相同目标、当前任务等待时的不同目标，允许任意两个合法 guard 字节和任意计数器。见证仍是空不变量／空栈 fixture，不是实际初始化或 `GoodI`。任务表尚在现有 `SWINV` 之外，不能未经资源归属重组就套用真实切换规则。

141 个活动 Coq 文件空目录重编、4 个新根的固定独立接口／实际假设／`coqchk`、4 项新增指定控制全部通过；旧 55 根及 47 项控制保留。正式 261 条命令：210 次成功、51 次预定拒绝，无非预期失败。新根实际假设并集仍仅为经典逻辑与依赖函数外延性。316 项 Python 回归、工程／覆盖审计、冻结源码复核、368 次 C 矩阵及六文件小模型检查均通过。

新证据为 [function-evidence-stage18.json](audit/function-evidence-stage18.json)，SHA-256 `40de7b9ef037c57f02c20fb78b4b817b3fdbc8bee75a03d0335fc62f789b8fe6`。旧 stage17／stage16 记录未回写；函数覆盖仍为 `94 / 1 / 1 / 1 / 1 / 0`。经逐项确认后已清理本轮 70 个定向编译产物和两个一次性脚本，源码、日志、证据与既有依赖保留。

下一步连接真实共享不变量、`GoodI`、切换共享／局部资源分离与抽象调度动作；随后完成临界区入口／出口、完整函数环境与初始化。合法自删除路径须单独接 `SWPRE_DEAD`。最终 `GOOD_OS`、同程序 K1–K4 仍开放，uC/OS-III 未启动，两阶段总目标继续活动。详见[本轮报告](audit/STAGE18_SCHEDULER_SWITCH_PRE.md)与[第十九课](docs/阶段/19-补齐当前指针写权限与切换前置.md)。

## 第十九阶段：非空共享核心与 `GoodI`

`V293_shared_core` 拥有真实当前指针的一半权限和四个抽象槽位，构造精确、ISR 稳定的非空 `Inv`。打开／关闭 `SWINV`、合并另一半当前指针、实际 `store` 与抽象 `curtid` 同步更新的保持证明均闭合；由此证明框架四项 `GoodI` 条件。当前任务可以仍在表中或已被删除，删除分支明确只针对空 `LocalInv`。

任意任务表／事件表／时间值的实际写入可满足见证，以及当前任务时间等待／当前任务已删除的两个具体场景均通过；两个场景在同一状态都有最高就绪目标 `AHprio` 与真实 store。它们不是实际初始化或可达性证明。就绪位图、优先级数组和物理 TCB／ECB 关系尚未纳入，也没有把旧前缀的外部任务表重新归入共享资源；完整内核不变量、真正切换及调用方仍开放。

143 个活动文件空目录重编、6 个新增根的固定独立接口／实际假设／`coqchk`、4 项新增单因素控制全部通过；旧 59 根、51 项控制完整保留。正式共 272 条命令：217 次成功、55 次预定拒绝，无非预期失败。新增根实际假设并集仍仅为经典逻辑和依赖函数外延性。两次预检因移除 time 后参数类型推断失败而未被计作控制通过，补全正常参数类型后才命中指定义务；失败日志保留，未放宽门禁。

341 项 Python 测试、工程／覆盖审计、冻结源码复核、368 次 C 矩阵及六文件小模型检查通过。新证据为 [function-evidence-stage19.json](audit/function-evidence-stage19.json)，SHA-256 `81ffb61a98695fa4652fef5e50c652dfefc29d83c1cf536a9bd57568db7af574`；旧 stage18／stage17 和冻结源码记录未改写。覆盖仍为 `94 / 1 / 1 / 1 / 1 / 0`，辅助六根不冒领函数覆盖。

逐项确认并复核身份后，清理 80 个任务编译产物、8 个临时探索文件、两个一次性预检脚本及一个空目录；源码、正式证据、失败日志和既有依赖保留。下一步继续真实物理资源关联与前缀资源归属重组，并明确 `OSCtxSw`／`OSPrioCur` 的同步边界；再接两类实际切换和临界区。最终 `GOOD_OS`、同程序 K1–K4 和后续 uC/OS-III 总目标仍活动。见[本轮审计](audit/STAGE19_SHARED_STATE.md)与[第二十课](docs/阶段/20-从空不变量到非空共享核心.md)。


## 第二十阶段：唯一共享任务表接回真实调用与赋值

原前缀在 `SWINV` 外持有任务表，直接套入 stage19 非空核心会重复占有独占槽位。本轮以同状态 snapshot 观察核心值，打开同一份共享资源，把唯一任务表借给原内部调用和目标指针赋值，再按原值封装归还。资源参数 `I` 与规则参数 `RI` 仅在四个必要内部接口分离；实际规则仍使用非空 `V293_shared_inv`，旧五个公共根类型不变，未保留未使用的额外 guarded 泛化。

新稳定根 `V293_OSSched_shared_prefix` 没有 suffix oracle，执行仍是冻结源码的两句前缀。完整新前置有同状态可满足见证：同一可写当前指针分成两半，唯一任务表与另外三个抽象槽位不相交组合，同时满足实际位图／优先级表关系；覆盖相同目标和当前任务等待的不同目标，允许任意事件表与时间。见证不是初始化／可达性，也未把合法自删除接回新前缀。

145 个活动 Coq 文件正式空目录重编通过；5 个新根的固定独立接口、实际假设、`coqchk` 和 4 项新增指定单因素控制通过，旧 65 根／55 项控制保留。正式 283 条命令：224 次成功、59 次预定拒绝，无非预期失败。新根实际假设并集仍仅为经典逻辑与依赖函数外延性。365 项 Python 回归、工程／覆盖审计、冻结源码复核、368 次 C 矩阵证据重放和六文件小模型检查均通过。

新证据为 [function-evidence-stage20.json](audit/function-evidence-stage20.json)，SHA-256 `ea439e20198e5bf65152fdfda6da3f3c6cd081551509890200f53863d9d049c6`；旧 stage19／stage18 和冻结源码记录未改写。两次探针导入失败预检，以及首次完整 Python 测试检出的旧证据哈希引用，均保留失败日志；补齐准确导入／更新引用后重新验收，没有修改正式 JSON 或放宽门禁。六门覆盖仍为 `94 / 1 / 1 / 1 / 1 / 0`。

逐项确认及身份复核后清理 90 个本轮 Coq 产物、1 个本轮 Python 字节码与 6 个一次性文件，保留 639 个既有构建路径和全部源码、证据、日志及既有依赖。下一步按新资源归属接回两层 guard、比较、计数器与切换前置，继续真实物理 TCB／ECB 关系和 `OSCtxSw`／`OSPrioCur` 同步边界，再完成实际两类切换、临界区、函数环境与初始化。最终 `GOOD_OS`、同程序 K1–K4 未闭合，uC/OS-III 未启动，两阶段总目标继续活动。见[本轮审计](audit/STAGE20_SCHEDULER_SHARED.md)和[第二十一课](docs/阶段/21-共享任务表借给真实调度前缀再归还.md)。


## 第二十一阶段：共享目标单元与实际普通切换规则

核对真实规则发现旧核心没有占有目标指针：`SWPRE` 只看共享部分，不能从局部 frame 借入；非 affine 逻辑也不能在后置丢弃该单元。因此先以一个类型正确的完整目标指针扩展共享核心，证明其精确性、实际 store／抽象当前任务同步保持及四项 `GoodI`。同状态 snapshot 打开／关闭完整资源，以第二半当前指针推出普通切换前置，并真正应用 `switch_rule`，不是只证明前置或引入 suffix oracle。

稳定根 `V293_shared_normal_switch` 的入口动作从 `sched;;aop` 消耗为 `aop`，后置描述原线程恢复执行；不冻结共享表、事件、时间或目标值。完整 pending 入口在同一状态可满足，覆盖当前 ready／目标相同和当前时间等待／目标不同，事件表、时间与后续动作均任意。相同目标见证不表示 C 相同优先级分支执行切换。空栈 fixture 也不是初始化、可达性或完整物理内核证明。

148 个活动 Coq 文件正式空目录重编通过；8 个新根的独立接口、实际假设及 `coqchk`、5 项新增指定单因素控制全部通过。旧 70 根与 59 项控制完整保留；正式 300 条命令：236 次成功、64 次预定拒绝，无非预期失败。新根实际假设并集仍仅为经典逻辑与依赖函数外延性。389 项 Python 回归、工程／覆盖审计、冻结身份、368 次 C 矩阵证据重放及六文件小模型检查均通过。

新证据为 [function-evidence-stage21.json](audit/function-evidence-stage21.json)，SHA-256 `afca5fd2efc416d62fff5c3deacf869edcfdc287b2189b105a7dc06abc5ff77b`；旧 stage20／stage19／stage18 及冻结源码记录未改写。首次预检的导入失败日志保留，不计作指定负控；原拟 counter／guard 控制在负控前明确延后，没有计作通过。完整边界与实测结果见[本轮审计](audit/STAGE21_SCHEDULER_SWITCH.md)，中文入门见[第二十二课](docs/阶段/22-真正应用切换规则与恢复原线程.md)。函数覆盖不增加，仍为 `94 / 1 / 1 / 1 / 1 / 0`。

逐项确认并复核路径、类别、大小与哈希后，清理 105 个本轮构建产物和 9 个一次性文件，保留全部 646 个既有构建路径及源码、正式证据、失败日志、依赖和用户数据。stage20 真实调用／赋值前缀仍用旧核心，尚未连接到本轮含目标单元的新 `Inv`；下一步先重组借还，再接 guard、比较、计数器和实际切换。`OSCtxSw` 对应／`OSPrioCur` 同步、合法自删除、物理 TCB／ECB、临界区、函数环境与初始化、最终 `GOOD_OS` 和同程序 K1–K4 仍开放。uC/OS-III 未启动，两阶段总目标保持活动。

## 第二十二阶段：共享目标接回真实前缀与两层条件

stage20 前缀和 stage21 实际切换曾使用不同的共享核心，不能直接拼接。本轮将唯一任务表和同一个目标单元一并借给真实 `OS_SchedNew()` 调用／目标赋值，再归还 stage21 的 `V293_dispatch_inv`；外层规则始终使用该非空核心，被调契约只占有打开后的空核心。入口允许任意类型正确的目标，执行后才观察实际最高就绪者，并保留同一任务表／事件表／时间。两层真实字节条件也接入：仅两个字节皆零执行前缀，其余分支保持完整原入口。

完整前缀入口可满足见证复用原状态，将同一个目标单元移入新核心，覆盖当前 ready／同目标和当前时间等待／不同目标，事件表与时间任意。该见证只实例化 `spec_done None`、`Aemp` 和空栈；不是 pending 动作、完整 guarded 状态、初始化或可达性证明。前缀规则对任意合法动作和动态栈参数化，不因此扩大见证范围。

150 个活动 Coq 文件正式空目录重编通过；5 个新增稳定根的固定独立接口、实际假设及 `coqchk` 通过，6 项新增单因素控制命中指定义务。旧 78 根／64 项控制保留，累计 83 根／70 项控制。正式 313 条命令：243 次成功、70 次预定拒绝，无非预期失败。新增根实际假设并集仍仅为经典逻辑与依赖函数外延性。415 项 Python 回归、工程／覆盖审计、冻结身份、368 次 C 矩阵证据重放及六文件小模型检查全部通过。

新证据为 [function-evidence-stage22.json](audit/function-evidence-stage22.json)，SHA-256 `91eef4d4f1bcd12208a8ac40d5f8208397eac0e38257ceac6b6b666dc999d128`；所有旧正式 JSON 及冻结源码记录未回写。定向证明失败日志和负控前澄清的前瞻协议保留，不把探索失败或较早拒绝记作下游通过。函数覆盖不增加，六门仍为 `94 / 1 / 1 / 1 / 1 / 0`。

逐项确认及身份复核后清理 115 个本轮 Coq 产物与 5 个一次性文件，保留全部 646 个既有构建路径、源码、正式证据、失败日志、依赖和用户数据。下一步在同一共享核心下连接优先级比较、计数器、第二半当前指针和实际切换的局部资源保留；`OSCtxSw` 对应／`OSPrioCur` 同步、合法自删除、物理 TCB／ECB、临界区、函数环境与初始化、最终 `GOOD_OS` 及同程序 K1–K4 仍开放。uC/OS-III 未启动，两阶段总目标继续活动。详见[本轮审计](audit/STAGE22_SCHEDULER_DISPATCH_SHARED.md)和[第二十三课](docs/阶段/23-把共享目标接回真实调用与条件分支.md)。


## 第二十三阶段：比较、计数器与实际普通切换顺序连接

在同一个含目标的 `V293_dispatch_inv` 下，由 stage22 实际调用／目标赋值后置连接优先级比较、真实 32 位模递增和 stage21 真正普通 `switch_rule`，再接两层 guard，不再假设后半段正确。原 `CurLINV` 的第二半当前指针真正交给切换规则，剩余 `Atrue` 保留；恢复后置不冻结原共享任务表、事件、时间或目标。禁止调度及相等优先级分支仍保留 `sched;;aop`，不能冒称所有分支已统一收尾。

完整入口见证在同一个状态中包含真正 pending 动作、两个任意合法 guard 字节、任意计数器及全部片段物理／抽象资源，覆盖当前 ready／同目标和当前时间等待／不同目标，事件、时间与后续动作任意。见证只用空栈，不是初始化、可达性、完整物理 `GoodI` 或合法自删除证明。位图、数组、当前优先级、计数器等仍按片段局部资源保留；其他任务可改变这些真实全局资源，完整程序必须重新归入共享不变量，不能直接继承当前恢复后置的局部稳定性。

152 个活动 Coq 文件正式空目录重编通过；9 个新根的固定独立接口、实际假设及 `coqchk`、6 项新增指定单因素控制通过。第二半权限移除控制有相同定义展开但恢复权限的正向基线，核心／见证／探针三步全部成功，排除了展开干扰。旧 83 根／70 项控制保留，累计 92 根／76 项控制；正式 329 条命令中 253 次成功、76 次预定拒绝，无非预期失败。新增根实际假设并集仍仅为经典逻辑与依赖函数外延性。

443 项 Python 回归、工程／覆盖审计、冻结源码复核、368 次 C 矩阵证据重放和六文件小模型检查全部通过。新证据为 [function-evidence-stage23.json](audit/function-evidence-stage23.json)，SHA-256 `8f4fcac337647f5dfaa9c1603949c021f6fc02608bacc48ed0888d4b084c5b82`。旧正式 JSON 和冻结 C／配置／补丁／框架／策略不变，六门覆盖仍为 `94 / 1 / 1 / 1 / 1 / 0`。定向失败、两次展开基线失败及前瞻澄清均保留，不计作指定控制或下游通过；没有弱化契约或门禁。

逐项登记及身份复核后清理 130 个任务 Coq 产物、7 个任务 Python 字节码和 5 个一次性文件，共 4,767,913 字节；全部 646 个既有构建路径、源码、正式证据、成功／失败日志、依赖和用户数据保留。下一步连接 `OSCtxSw`／`OSPrioCur` 源码级边界、未切换分支动作、临界区及真实全局资源共享，随后处理合法自删除、其余函数、完整环境与初始化。完整 `OS_Sched`、最终 `GOOD_OS` 和同程序 K1–K4 尚未闭合，uC/OS-III 未启动，两阶段总目标继续活动。详见[本轮报告](audit/STAGE23_SCHEDULER_DISPATCH_TAIL.md)和[第二十四课](docs/阶段/24-串起比较计数器与真正普通切换.md)。

## 第二十四阶段：相等分支自调度与禁止调度的边界

不修改同一规范化调度 AST：从原位图／任务表、唯一优先级表、当前任务关系及实际比较结果，推导选出的目标就是当前任务，再从同一资源观察 `sched_self`，真正消耗相等分支的抽象 `sched`。调用／赋值、比较／递增／普通切换和两层 guard 重新连接；两个 enabled 分支具有相同的 `aop`／`SWINVt`／动态栈／完整 locals 后置形状，计数器依条件保持或模加一。资源不丢弃，没有最高就绪或后半段 oracle。

禁止调度仍保持完整 pending 入口。新增同状态完整锁定入口反例：当前任务优先级 4 且时间等待，另一优先级 12 任务 ready，中断嵌套 0、调度锁 1，因此 `sched_self` 不成立。它只说明当前片段入口不足以无条件自调度，不证明初始化可达或真实内核有错；不能为统一后置修改 scheduler。真实全局位图、数组、优先级、计数器等仍须重新纳入物理共享不变量，不能将当前片段局部 frame 的稳定性推广到其他线程执行后的全局状态。

154 个活动 Coq 文件正式空目录重编通过；六个新根的固定独立接口、实际假设、`coqchk` 及四项新增指定单因素控制通过。旧 92 根／76 项控制保留，累计 98 根／80 项控制；339 条正式命令：259 次成功、80 次预定拒绝，无非预期失败。新根实际假设并集仍仅为经典逻辑与依赖函数外延性。equal 控制实测为后置蕴含未闭合引发后续 bullet 拒绝，不声称该变更规格不可证明，也不给未执行的下游义务信用。

471 项 Python 回归、工程／覆盖审计、冻结源码复核、368 次 C 矩阵证据重放及六文件小模型检查通过。新证据为 [function-evidence-stage24.json](audit/function-evidence-stage24.json)，SHA-256 `bc5e87ba36676072c0c9d6075b4430839aa451d04b8389e03ffae6525401a375`。旧正式 JSON、冻结 C／配置／补丁／框架／策略未改写；覆盖只更新证据引用，六门仍为 `94 / 1 / 1 / 1 / 1 / 0`。

逐项登记与身份复核后移除 135 个本轮 Coq 产物和一个一次性预检脚本，共 4,710,935 字节；全部 650 个既有构建／缓存路径、源码、正式证据、成功／失败日志、依赖和用户数据保留。下一步继续 `OSCtxSw`／`OSPrioCur` 源码级边界、全局物理共享归属、临界区与禁止调度的上层延期规格，再处理合法自删除、其余函数、完整环境与初始化。完整 `OS_Sched`、最终 `GOOD_OS` 和同程序 K1–K4 未闭合，uC/OS-III 未启动，两阶段总目标继续活动。详见[本轮报告](audit/STAGE24_SCHEDULER_DISPATCH_FINISH.md)和[第二十五课](docs/阶段/25-不切换也要完成抽象调度.md)。


## 第二十五阶段：物理存储归还共享核心，再实际切换

针对原完整片段将计数器等真实全局资源作为局部 frame 的限制，本轮先建立最小共享尾部闭环。固定地址／类型的完整物理存储纳入同一新 `V293_storage_inv`，精确性、打开／关闭、真实当前指针 store／抽象 `curtid` 同步保持及框架 `GoodI` 全部闭合。真正计数器递增后，中间值精确为 32 位模加一；切换前把计数器／额外列表归还共享核心，再真正应用普通 `switch_rule`。恢复后仅保留存在值的共享存储和合法私有 frame，不冻结旧 `c+1`，没有 suffix oracle。

完整 pending 尾部入口有同状态见证：当前 ready／同目标和当前时间等待／不同目标，任意计数器、事件表、时间和后续动作。具体见证的额外列表为空，不是所有全局布局、完整前缀入口、初始化或可达性。上一轮完整前缀仍用旧不变量，尚未接回本轮新物理核心；物理位图／数组／TCB／ECB 与抽象任务表的关系也未建立，不能冒称完整内核不变量。

157 个活动 Coq 文件空目录重编通过；六个新固定独立接口、实际根假设、`coqchk` 及四项新增指定单因素控制通过。累计 104 根／84 项控制；354 条正式命令：270 次成功、84 次指定拒绝，无非预期失败。新增实际假设并集仍仅为经典逻辑与依赖函数外延性。恢复后额外索要旧 `c+1` 单元的控制同时涉及重复所有权，只算非法后置的契约敏感性，不算“只固定数值”的独立消融或不可证性结论。

完整 500 项 Python 回归、工程／覆盖审计、冻结源码复核、368 次 C 矩阵证据重放及六文件小模型检查通过。新证据为 [function-evidence-stage25.json](audit/function-evidence-stage25.json)，SHA-256 `1c71c9ca2cbab96c2f1aae5ddee276e5d4912cd397e00bafa7375c0272005e46`。旧 JSON、冻结 C／配置／补丁／框架／策略保持不变，覆盖仅更新证据引用，六门仍为 `94 / 1 / 1 / 1 / 1 / 0`。定向证明及前三次字面探针预检失败、一次正式记录生成前的提前测试失败均保留；修正后完整重跑，不放宽门禁或排除测试。

逐项登记及身份复核后清理 100 个任务 Coq 产物、2,209 个一次性预检副本／输出和一个驱动，共 2,310 文件、50,540,253 字节及 68 个任务目录；保留本轮开始登记的全部 635 个既有构建路径、源码、正式证据、全部日志、既有缓存／依赖和用户数据。下一步将完整前缀的真实全局资源借还接入同一新不变量，补物理数据关系与 `OSCtxSw`／`OSPrioCur` 源码边界，再处理 guard 延期规格、临界区、合法自删除、其他函数、完整环境与初始化。完整 `OS_Sched`、最终 `GOOD_OS` 和同程序 K1–K4 未闭合，uC/OS-III 未启动，两阶段总目标继续活动。详见[本轮报告](audit/STAGE25_SCHEDULER_STORAGE.md)与[第二十六课](docs/阶段/26-把共享计数器归还后再切换.md)。
