# 第60步：OS_TCBInit 的连续任务发布片段

## 固定对象与接口

仍为固定uC/OS-II V2.93.01、上游`0c4a48e6fbc6e915714e816196619a5481accf0c`及两类授权修复。配置后源码身份`74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da`；新鲜重建94项定义全部一致。精确函数、前后边界及片段见`audit/logs/stage60-tcb-publish/source-connection.json`及source快照。新生产模块`V293OSTCBPublish.v`／`V293TCBPublish.v`，独立见证`audit/probes/V293TCBPublishProbe.v`。

稳定接口`V293_OS_TCBInit_publication_execution`：从OSTaskCreateHook之后、第三次归一化enter之前，连续执行Next／Prev、真实NULL判断及可选旧头Prev、全局链头、group OR、row OR、counter++、trace空语句、exit；停到return0之前。NULL分支6次实际写入，非空7次。同一Mf保留任意frame可写所有权，原IE及已有si／ci恢复。入口无中间内存／求值／执行结果假设；旧links可为Vundef。泛型字节边界y<2、x<8、g/r<256、n<255，基址满足unsigned界。

## 只证明什么

只拥有局部指针、若干TCB字段、全局head／group／所选行／计数及条件旧头Prev，不等于完整TCB分配、整条链合法或链无环。冻结protocol中的live／allocated措辞过强，本报告明确收窄且不改原协议。entry要求Y/BitY/BitX相干，未拥有priority字段，不证明与它或全局ready集合的关系。n=255的wrap未涵盖。

前置OSTCBInitHook、优先级表写入、OSTaskCreateHook不在片段中，也没有假设Hook无操作。第59步前缀到本片段的连接仍开放；本片段未接第57步七调用的实际内存。端口栈初始化／函数地址表示、OSTaskCreateExt、return／局部释放仍开放。按ADR0005手工归一化critical宏，擦除CPU_SR字节效应，不是raw port函数执行、C前端或ABI验证。任意P中的存在性无交错轨迹，不是local Hoare、所有执行safety或完整94函数实例。

## 独立入口与单因素实验

p12／p11 ×旧头非空／NULL四份独立物理内存，新TCB base8、旧头base16；NULL无需旧TCB任何存储。初始group1／row2／counter4，另行85和保护字77。真实执行后group3、row18／10、counter5，other85／77保持。四个独立内存每份12或13项同Mf typed-load；初始IE任意bool，共8参数实例、100项typed-load实例，不是8次独立coqc，不是两任务共存。

前瞻协议先冻结，**仅将所选ready行赋值改为sskip**，其他语句、入口与读回全不改：只有该行保持2，其余NULL11／非空12项及IE／si／ci不变。不授链表／group／counter／critical各机制独立消融信用。

ablation01因删除唯一rows使用后未能推断binder类型失败；02仅标注rows:var，因证明M6别名rewrite失败；03只在证明中消除别名，泛型定理通过而具体算术scope失败，不计整实验通过；04只给两处算术tactic加%Z后整文件通过。每次修正均在执行前单独冻结计划，所有Theorem陈述逐字不变，失败日志／快照保留。原protocol不重写。

positive通过后，四负控各只改最终row／counter／old-head.Prev／IE一处，证明体逐字相同，分别在39／41／42／38行拒绝。不同位置的拒绝只支持相应接口敏感性，不自动支持未做的机制消融。

## 信任、回归与交付

219活动源增量构建通过，复用1085旧产物，非source-only冷构建。52信任根Print Assumptions与四模块coqchk通过；只接受既有框架allowlist，无新增公理。开发中code／proof／probe失败全部保留，不删不利证据。

完整回归、395fail＋1error的396条旧诊断逐ID比较、缓存精确恢复和临时目录清理，见`audit/logs/stage60-tcb-publish/final-report.json`及非自引用`final-evidence-manifest.json`。旧C、Coq、配置、修复、测试、证据和1085旧产物保持；只向_CoqProject追加两源并前插README／VERIFICATION_STATUS、追加教学。默认审计仍有过期旧证据身份等未解决失败，不调低门槛、不宣称全绿。无Git提交／推送。

正式六门仍`94/1/1/1/1/0`。完整OS_TCBInit／OSInit、源码级GOOD_OS和同程序K1–K4未闭合，uCOS3未开始，总目标保持active。下一工作应纵向连接Hook／优先级表／返回与任务创建，而不是用更多独立片段替代整函数连接。
