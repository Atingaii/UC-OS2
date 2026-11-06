# 第61步：OS_TCBInit 空链失败分支的完整调用生命周期

## 固定对象与新增接口

对象仍为uC/OS-II V2.93.01上游`0c4a48e6fbc6e915714e816196619a5481accf0c`及固定配置、两类授权修复。fresh源码全部94项身份一致；source identity为`74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da`。源码快照、结构检查及参数映射见`audit/logs/stage61-tcb-empty-call/source-connection.json`。

新增`V293OSTCBInitFunction.v`手工组合完整归一化语法：参数101..107、局部108/109、全局91..96。七参数声明按源序，框架sfexec使用反向实参列表；随后分配ptcb和cpu_sr。保留cpu_sr=0显式赋值、成功分支两个真实scall、优先级表赋值、发布及成功返回。**语法完整不等于成功执行已证明。**

稳定接口`V293_OS_TCBInit_empty_call_return`从sfexec进入，真实执行七参数分配／store、两局部分配、cpu_sr初始化、enter、NULL链头赋值及判断、exit、return66及释放，恢复caller环境和任意初始IE／si／ci。一个Mf承载caller frame可写所有权及9对象29字节全部None；return前Ms承载所有参数／局部和值。入口没有中间M或执行结果假设，需要实际NULLhead、任意frame、7个typed值及9个已选distinct fresh块与Away条件。

## 独立物理入口与实验

独立probe只编码head301:0=NULL、frame601:0=77、caller旧局部602:0=88；caller的标识108与callee的ptcb同名。无TCB对象、无stack内存、无callee201..209。P只定义目标500，501/502两个Hook为None；错误分支不调用它们，未给Hook伪造空函数体。p12/p11为独立执行实例，每份初始IE任意，两种IE共4参数实例；每例3个typed-load及29个已释放字节（12与116为参数实例计数，不是独立coqc次数），不是任务共存。NULL错误状态从七调用初始化Mf的可达性尚未证明。

前瞻消融仅把P500函数定义删掉，不改源C、语法、实参或入口，证明同sfexec无loststep，其他函数定义逐点不变。**这是整call可用性实验，不授参数／guard／return／free各机制独立因果信用。** positive及四负控先冻结再执行；只改最终返回值、caller环境、freed字节或frame值中的一处，证明体逐字一致，分别在27/40/55/70行拒绝。端点负控是接口敏感性，不等同单机制消融。

## 失败保留与信任边界

code01/02为显式import、列表notation错误，03通过；proof01..12失败及07显式中断保留，13通过；probe01因In归约遗漏失败，02通过。开发修正包括NoDup反演命名、fresh/store实例参数、明确资源尾与值、语法空格、资源展开及状态change；没有改C、旧证明或冻结负控结论。生成器保留初始草稿用途，最终生产文件与成功snapshot逐字匹配才是证据。

按ADR0005手工映射临界宏，CPU_SR token字节效应擦除，不是真端口执行或verified frontend。只证明存在性无交错轨迹；从sfexec开始不含实参表达式求值。通用fresh块选择仍是前提；typed stack指针不等于有效stack。不证明成功Hook执行／优先级表执行／七调用Mf连接、local Hoare、所有执行safety或全94函数程序。

221源增量构建复用1095旧产物（非cold）。信任根、四模块coqchk、8项新增测试、完整回归、旧396条诊断逐ID比较、缓存原字节恢复及清理，见本步`final-report.json`与非自引用`final-evidence-manifest.json`。不删不利结果，不降低默认审计门槛；默认审计仍失败。旧C、配置、修复、Coq、测试、证据及可复用产物保持，仅按约定追加两活动源和中文文档。临时项先全inventory再全recheck才删除，旧缓存不删；无Git提交／推送。

正式六门仍94/1/1/1/1/0，完整OS_TCBInit／OSInit、源码级GOOD_OS和同程序K1–K4未完成；uCOS3未开始，总目标active。下一优先处理真实成功Hook边界与任务创建的纵向连接，不以错误分支或片段数量代替整核成果。
