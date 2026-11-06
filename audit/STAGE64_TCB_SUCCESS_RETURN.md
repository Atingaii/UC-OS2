# OS_TCBInit成功后缀的完整返回生命周期

## 第64步：第二个Hook返回后的发布与成功返回

### 这一步解决什么

以前，第60步只到return前，第63步只到第二个Hook调用前。现在稳定接口
`V293_OS_TCBInit_success_suffix_return` 从**第二个Hook已返回**的精确continuation开始，
真实执行保留的任务链插入、ready group／row更新、任务计数加一、exit、return 0，
随后释放参数与局部对象并恢复caller。不是把几个不同内存上的结论摆在一起：
发布产生的Ms直接交给return／free，最终同一个Mf保有所有列出的发布字段与frame。

### 内存与条件

- 原函数7参数＋2局部，共9对象，`1+4+4+2+4+4+2+4+4=29`字节，逐字节证明Mf中不存在。
- ptcb字节已由publication cells拥有，other_locals只拥有另外8对象，不重复分离同一地址。
- 接口显式要求9块NoDup，以及所有应存活字段／frame的块不属于释放集合；未自动从入口推导这些条件。
- 返回后只重建列出的cells所有权，不把任意断言R未经证明搬到caller环境。
- 未假设中间执行／store／free结果，所有中间内存由实际语义构造。

### 独立验证

独立probe使用有限字面量内存，p12／p11 × 旧任务链头NULL／非空四例，
起点有完整callee环境及29字节。每例13／14项最终typed reads，保有上一步的优先级槽、
邻槽和caller保护字77／88；任意初始IE、si、ci保持。
IE两值可实例化为8组，共108项typed读回及232个释放字节断言；这不是8次独立coqc或两任务共存。

终点负控只改return值、计数、caller保护字、被释放字节结论，同证明体最终均被拒绝。
第一套positive的FreeEndpoint成员证明不完整，保留原失败，不授控制实验通过信用；
第二套冻结计划仅修正共享成员tactic，测量语句不变，positive通过、四个负控分别在目标结论处失败。

原protocol提出的“改变saved权限后仍执行publication”的整片段实验**未执行**，不记成功。
另行前瞻冻结的低层消融只改变saved对象四个权限位，四字节值／地址／类型／load与free代码不变：
两种权限均可读0，primitive free仅在可写时有结果。它只检验释放权限前提，
**没有执行publication或完整return，不能给这些下游机制独立消融信用**。
六次harness失败及第七次成功证据全部保留：修正import、化简／地址读取证明及最终outside地址的显式Z类型；load／free测量语句不改，未改变判定条件。

### 尚未解决

固定配置的5个端口Hook仍只有声明。此probe从合成的Hook返回锚点开始，
**未证明这个锚点在固定P中从函数入口可达**；没有执行Hook，也没有造noop。
因此这一步不是完整OS_TCBInit，更没有连接OSTaskCreateExt、实际七调用Mf或完整OSInit。
手工前端／ADR0005宏归一化仍擦除CPU_SR token字节效应；只是存在性无交错local_steps，
不是local Hoare或全执行safety。完整分配、链无环及全内核不变式均未证明。

增量构建224源，复用1115旧产物，非cold；48信任根及framework顶层／生产定理／probe的coqchk检查。
旧395 failures＋1 error必须逐ID保留，默认make audit仍失败；最终机器结果以本目录final-report为准。
六门仍94/1/1/1/1/0，GOOD_OS与同程序K1–K4开放；uCOS3未开始，目标active，未提交／推送。

### 入门理解：为什么要释放局部变量？

参数和局部变量是一次函数调用临时借用的存储；任务TCB、ready表和全局链头则必须活过函数返回。
本步同时证明两件相反但都必要的事：**该删除的29字节确实删除，该留下的任务数据确实留下**。
下一步应把入口、两个真实Hook义务和这个成功后缀在同一调用上接起来；
缺失Hook不能由“应用hooks关闭”或假定空操作替代。

证据：`audit/logs/stage64-tcb-success-return/`；生产证明：
`certiucos/v293/proofs/V293TCBSuccessReturn.v`；独立probe：
`audit/probes/V293TCBSuccessReturnProbe.v`。
