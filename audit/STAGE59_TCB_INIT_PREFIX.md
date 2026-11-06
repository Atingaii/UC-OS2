# 第59步：OS_TCBInit 空闲链前缀与18条字段赋值连续执行

## 对象、改变与不变项

目标仍是固定uC/OS-II V2.93.01、上游`0c4a48e6fbc6e915714e816196619a5481accf0c`及两类授权修复，源码身份`74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da`。新鲜重建配置后C，94项定义身份全部一致；位置、函数体、Clang布局及原始快照见`audit/logs/stage59-tcb-init-prefix/source/`。Next偏移20，TCB大小56；不是ABI／编译器证明。

只新增`V293OSTCBInitPrefix.v`／`V293TCBInitPrefix.v`及独立probe，复用第58步字段赋值接口。旧C、Coq、配置、两修复、测试及冻结证据不改；仅追加_CoqProject并新增中文检查点／教学。没有Git写操作。

## 可调用接口

- `V293_OS_TCBInit_prefix_execution`：在已存在局部／参数的内存，从第一次归一化enter之前执行读取head、真实非空if、更新head、exit、18条赋值；同一Mf提供字段、8输入、head／Next及任意frame的可写所有权，停在任意传入suffix之前。
- `V293_OS_TCBInit_empty_prefix_execution`：head=NULL，只需ptcb与head两项存储（加任意frame），不需要任何TCB字段／Next／其他参数存储；真实走false分支并exit，停在`return66`语句之前，不授return/free执行信用。

入口没有中间内存、求值或执行结果前提；18旧字段和ptcb旧值任意。非空入口需要可写分离所有权及typed Next；不要求Next非空／新鲜／区别于当前head，因此**不是无环性或节点唯一分配证明**。泛型base满足unsigned边界，独立见证base8。

源码保留ifthen加外部失败exit/return的原顺序；不是重写成提前返回的玩具程序。真实成功后缀由上层提供，后缀与外部失败分支均保留在continuation；本步没有执行该后缀。中断状态和已有保存栈均为泛型参数，enter/exit后恢复。

## 手工前端与开放边界

按ADR0005将端口宏标记显式映射为框架encrit/excrit，**CPU_SR字节效应擦除**；函数声明不是函数体，不能把本定理叫作raw port calls的执行／仿真。局部分配和CPU_SR初始化在入口之外。函数调用Hook、优先级表／任务链／ready位图发布、计数器、完整返回尚未执行。

任意P上的无调用片段存在性轨迹，不是完整94函数程序实例，不是local Hoare或所有交错safety；未接入第57步七调用实际Mf，也不证明OSInit／OSStart可达。栈指针仅复制，未证明已分配栈或OSTaskStkInit。TCB的rdy不表示ready位图成员。最终GOOD_OS、同程序K1–K4仍开放；uCOS3未开始，正式六门仍`94/1/1/1/1/0`。

## 独立见证与实验

非空fixture：18字段及ptcb均Vundef、p为12或11、Next为501:56或NULL；Prev／Flags／padding及保护字77保留。四个独立内存各在同一Mf读回32项。定理对任意初始IE bool及si/ci成立，可取两值共8个参数实例（256个typed-load实例），不是8次独立coqc运行，不是两任务已共存。空链fixture只有ptcb/head/frame三cells，各3项读回，对两种IE成立。

协议先于实验冻结。单因素仅将pop赋值换sskip，保留读取、guard、临界原语、18stores、入口、suffix和32项测量：仅head期望变为旧301:8，其余31cells及IE／栈不变。不授每条字段写入独立消融信用。

原positive及ablation01在import因旧probe依赖与最终生产模块不一致而失败，均不计有效对照；原计划和日志不改。最终probe06通过后，plan02显式继承原冻结结论、variant和测量，只更新依赖readiness。positive02通过；ablation02在tactic里自然数／整数scope处失败，ablation03仅补%Z后通过，所有Theorem陈述逐字一致。四项负控只改最终head／priority／frame／IE之一，保持证明体完全相同，分别在33／35／36／32行拒绝，避免把早期import拒绝当下游机制有效证据。

## 构建、信任、回归与保留

217活动源增量构建通过，复用1075旧产物，非source-only冷构建。框架、生产两接口及独立fixture逐根Print Assumptions／coqchk结果见trust.json；不新增公理，接受的依赖仅既有框架allowlist。所有早期Coq失败保留快照和日志，不覆盖冻结证据。

完整回归、396条既有诊断的逐ID比较、缓存精确恢复、1075旧产物hash保留及本轮一次性目录清理，以`final-report.json`和`final-evidence-manifest.json`为最终机器可读证据。默认审计仍有旧函数证据身份过期等失败，不降低门槛、不删除旧失败。

下一纵向义务：检查真实Hook与后续发布路径、解决端口栈初始化／函数地址表示，连接OSTaskCreateExt及七调用实际内存；再推进runtime invariant、OSStart和整核目标。
