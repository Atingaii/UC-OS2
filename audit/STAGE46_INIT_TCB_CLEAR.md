# 第46步：OS_InitTCBList 的两次真实数组清零

## 一句话解释

先真正调用清零函数，把13个TCB所在的728字节和13项优先级指针表的52字节清零，再在同一个返回内存证明全部13槽为规范NULL，而且保留后续写链表需要的可写资源。**清零完成不等于空闲链表已经建立。**

## 源码与布局

固定授权修复C的 `os_core.c:1591–1617`，准确函数 `OS_InitTCBList`：先4项局部声明，再两次 `OS_MemClr((INT8U *)&table[0], sizeof(table))`，随后才是链表循环和链头赋值。本轮只连接前两次调用，不声称包含外围函数局部分配／释放。

重新物化C，用clang预处理／AST复核全部94项函数身份，源身份 `74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da`。i386静态断言和Coq typelen一致：TCB56、TCB数组728、指针表52、OSTCBNext偏移20。**人工归一化和布局对照，不是已验证C前端或编译器／ABI正确性证明。** 精确函数体、AST、命令、布局断言见 `source03/result.json`／`layout.c.snapshot.txt`；前两次脚本对clang声明分组及空白的错误假设均留存，C没有修改。

## 稳定接口的真实连接

- `V293_OS_InitTCBList_clear_calls`：真实求值 `&array[0]` 及16位长度cast，连续执行两个实际scall。第二次调用在第一次真实返回的M1中，由有界内存定理重新构造新鲜参数对象，不假设M1具有入口M的新鲜性。
- `V293_MemClr_call_owned`：复用第45步实际分配／store／循环／void／free；通过分离内存片段和Maps.sub保留全部目标与frame可写权限；只搬内存型raw cells，不偷搬依赖环境的任意R。
- `V293_OS_InitTCBList_cleared_tables`：同一Mf保有728个零字节＋13个typed null槽＋frame；对每个p<13证明typed load为Vnull。不是从几个load猜所有权，也不是把13次不同执行拼在一起。

## 独立入口：表格已经填好

有限内存不导入旧probe，程序lookup无开放前提。入口TCB块82的0–727全部Vundef但已分配可写；优先级块84的0–51全部255。两个数组之后有保护字节，另有独立对象。

| 对象 | 入口 | 两次调用返回后的同一Mf | 证明范围 |
| --- | --- | --- | --- |
| TCB数组 | 13×56＝728字节，Vundef | 全部0，首／末字节读回0 | raw writable bytes，尚无TCBNext链 |
| 优先级表 | 13×4＝52字节，255 | 全部13槽typed NULL并可写 | forall p<13，不只是抽一槽 |
| TCB数组后偏移728 | 17 | 17 | 排除末端越界破坏示例 |
| 指针表后偏移52 | 29 | 29 | 排除末端越界破坏示例 |
| 独立块99 | 123 | 123 | 同一执行的frame保留 |
| caller环境 | 原来的ge／le | 原来的ge／le | 不冒充完整OS_InitTCBList调用 |

`InitConcreteExecution` 同时包含cstepstar、完整所有权和6类load断言（展开forall后18项）；字面完整两call AST和入口都单独经Coq检查。所有bytes为零不表示已经存在有效任务，当前任务／运行Inv尚未建立。

## 实际检查与不能抹掉的失败

- 189个旧活动源、旧C、旧tests、旧audit文件哈希不变。新增code＋proof后191＝88目标＋103框架／tactics。
- 正式make build通过，复用945旧产物；保留955生产产物。不是全仓source-only冷构建。
- 50根Print Assumptions及4模块coqchk通过；新证明只用既有classic／dependent funext，无新增公理、占位或MemoryNotFull假设。
- 三项前瞻单因素负控，所有Proof、入口、AST不变：TCB首字节错误255（行140）、全部优先级槽错误非NULL（行131）、frame错误124（行148），在预登记行各自被拒绝。**只是最终连接拒绝测试，非机制消融，不授下游安全信用。**
- 全量测试 1161 项，392 failures／1 error；旧 392 项失败诊断全部保留，新增8项测试均通过。新增旧测试诊断：['test_mem_clear_call.MemClearCallTests.test_all_old_sources_tests_c_and_evidence_retained']。 不改旧精确源数断言以制造全绿，最终数字以final-report为准。
- 默认audit继续exit2（stale function evidence input identity），正式六门仍94／1／1／1／1／0，未晋级。另有补充字节级控制：优先级表首字节错误255，正例通过、负例在预登记行25拒绝，满足原协议的字节检查；它单独执行同一入口／程序，不冒充与主probe共享同一个Mf。首次补充正例因未固定列表参数失败，整组不计信用，原证据保留；有效证据为byte-control02-plan/results。全部编译错误与3次诊断中断日志保留；中断不是逻辑拒绝。用-time定位到大列表的断言推断及vm_compute／tauto枚举，显式固定分离后件和按索引归纳替代枚举，没有降低结论或删除检查。

## 严格边界与下一步

只是固定配置下、无交错的存在性轨迹，非所有执行safety；完整OS_InitTCBList的TCBNext循环、最后NULL、OSTCBList与OSTCBFreeList尚未证明。OSInit／OSStart真实可达性、完整task／ISR共享不变式、源码级GOOD_OS和同程序K1–K4仍开放；uCOS3未启动，无commit／push。

下一步沿同一Mf把13个TCB串成空闲链：第0项→第1项→…→第12项→NULL，再写活动链头NULL、空闲链头第0项。完成这些以后，还要建立内部任务／对象池和启动组合，才能连接运行不变式。

本轮仅清理逐项登记、全量复核的一次性临时编译目录、3个临时C物化目录和probe产物。保留全部旧缓存／源／证据及955可复用生产产物；最终清理结果见cleanup.json。

## 文件入口

- `certiucos/v293/code/V293OSInitTCBClear.v`
- `certiucos/v293/proofs/V293InitTCBClear.v`
- `audit/probes/V293InitTCBClearProbe.v`
- `tests/test_init_tcb_clear.py`
- `audit/logs/stage46-init-tcb-clear/`：protocol、source03、production22、probe07、control-plan/results、build、trust、final-tests、final-report、最终manifest。
