# 第44步：把真实字节清零连接到空指针所有权

## 入门：这一步究竟解决什么

上一步已经证明 `OS_MemClr` 确实写入零字节。接下来 TCB 初始化要把清零后的指针槽当作 `NULL`。但是旧模型把“零字节”和“空指针字节”当成不同东西，因此不能直接接上。

本步处理的是模型里的表示连接，不是发现或修改了 C 内核漏洞。先统一编码，再验证旧证明，最后用同一份实际执行后的内存同时证明空指针所有权和读回结果。完整初始化和整核证明仍未完成。

## 为什么不是只改一行读取规则

`load` 是“读出了什么”；`Amapsto` 是“持有什么精确字节及写权限”。只让读取返回 `Vnull`，并不能把四个零字节证明成旧规范的四个 `MNull`。所以编码和解码必须一起处理。

最初尝试保留旧 MNull 读取兼容；全量构建暴露旧“解码→规范编码”定理不再成立。独立闭合反例 `DualEncodingCounterexample` 确认这不是单纯战术脚本问题：同一个值有两套可读字节时，不能从读回值唯一重建规范字节。最终候选删除该兼容分支，不改旧定理的前提或结论。

| 输入 | 新模型的指针解码 | 意义 |
| --- | --- | --- |
| 恰好4个零字节 | `Vnull` | 与 null store、字节清零采用同一表示 |
| 含非零字节 | `Vundef` | 不把任意内容变成 NULL |
| 3个／5个零字节 | `Vundef` | 不把错误宽度变成 NULL |
| 4个 `Undef` | `Vundef` | 未初始化不等于已清零 |
| 旧4个 `MNull` | `Vundef` | 不再允许第二套空指针表示 |
| 规范非空 Pointer 片段 | 原非空指针 | 原算法不改 |

以下结果已实际验证；该编码是本工程的源码级表示约定，不是C标准保证、ABI或真实机器零地址的证明。

## 新证明的端到端路径

`V293_zero4_null_owned` 将4个实际可写零字节合并为一个 typed null 槽，任意同环境分离 frame 保留。`V293_OS_MemClr_null_cell` 从任意4个旧字节（允许 Vundef）的原始所有权出发，执行既有原生清零循环，在**同一个 Mf** 上建立 typed null 所有权并给出真实指针 load。写入成功来自所有权，而不是入口给定成功 store 或目标 load。

独立有限入口使用255／Vundef／7／1，目标范围为块82偏移5–8；偏移4和9是17、29保护字节，另有独立对象123。实例独立列出完整 AST、证明入口可满足，在同一 Mf 检查 null、末端指针9、计数0、两个保护字节和123，共6个 load。

该执行只针对已分配参数的无交错循环体。它不是完整 scall／分配／释放／返回，不是所有执行 safety，不是整张13槽优先级表，更不是 TCB 链／OSInit／OSStart 可达性。

## 下一步怎么学

1. 读 `V293_zero4_null_owned`：区分“读回相同”与“拥有相同字节”。
2. 读 `V293_OS_MemClr_null_cell`：看旧循环如何提供四零字节，而不是把它当作假设。
3. 读 `NullConcreteExecution`：核对六次 load 都使用同一个 Mf，frame 不是凭空保留。
4. 下一阶段连接实际 `OS_InitTCBList` 的两次清零、TCBNext 链和全局空闲链；不能直接跳到 GOOD_OS。

## 实际迁移与验证

| 检查 | 观察到的结果 | 不能据此声称 |
| --- | --- | --- |
| 原有187个活动源隔离重建 | 无旧编译产物起步，187个实际编译，退出0，约1187秒，输入未变 | 不是原模型与新模型行为完全等价 |
| 旧规格迁移 | 只改5个旧文件；其中526条Lemma／Theorem／Corollary陈述逐一不变 | 不是所有其他定义和fixture都未变 |
| 正式工程构建 | 188源＝85目标＋103框架／tactics，退出0；复用从隔离树验证过的940个产物 | 不把这次约1秒的构建叫作188源冷构建 |
| 新生产证明／独立探针 | 2个／12个Print Assumptions根；独立探针重新在正式工程编译成功 | 不等于全部函数已接入顶层 |
| 框架信任检查 | 隔离树与正式工程分别实际检查48根，coqchk检查框架顶层、新生产模块、独立探针3模块，全部退出0 | 框架Soundness不是具体内核GOOD_OS实例 |
| 源码冻结／范围检查 | 均退出0，固定C与两项授权补丁未变 | 不是新授权了额外内核修改 |
| 默认make audit | 仍退出2：stale function evidence input identity | 不删除失败或改六阶段证据造通过 |

5个旧文件为 `framework/model/memory.v`、`tactics/sepauto/seplog_tactics.v`、`tactics/hoareforward/symbolic_lemmas.v`、`V293TaskPrioRekey.v`、`V293TaskRecordOwnership.v`。前者统一编解码；中间两者修复相应证明；rekey只迁移四个有限空值字节；最后恢复新唯一编码下的“指针读取→精确字节”证明。其余182个旧活动源保持字节不变。

48个框架／目标根实际只用既有白名单 `Classical_Prop.classic`、`FunctionalExtensionality.functional_extensionality_dep`、`Eqdep.Eq_rect_eq.eq_rect_eq`；未新增公理，不依赖MemoryNotFull假设。新生产和执行探针的依赖更小，只有其中classic／functional extensionality；表示边界等10个探针根是闭合的。

## 对照怎样避免自证

所有协议先登记，再执行；codec探针的证明和其他机制保持不变：

| 单因素候选 | 预期／实际 | 信用范围 |
| --- | --- | --- |
| 完整唯一编码 | 编译通过 | 编解码边界 |
| 只改解码，编码仍MNull | CanonicalEncoding处拒绝 | 编码与字节清零未统一 |
| 只改编码，去掉新解码 | NullRoundTrip处拒绝 | 存取不能往返 |
| 把所有字节列表当NULL | NonzeroRejected处拒绝 | 非零内容不能伪装空指针 |
| 恢复旧MNull解码别名 | LegacyNullRejected处拒绝 | 新规范不接受第二套null表示 |
| 实际清零后错误读回非空指针 | 保持全部Proof，在预登记读回连接第98行拒绝 | 同一Mf结果连接；不是全部交错执行安全 |

兼容别名是否破坏旧所有权并非只凭最后一个codec拒绝判断：此前全量构建在既有 `V293_pointer_decode_encoding` 失败，并另行编译了闭合的 `DualEncodingCounterexample`。反例表明读回null的旧MNull不等于新编码。删除兼容层后，原定理不加前提、不改结论便可重证。所有失败日志和候选快照保留。

## 历史模型与当前模型必须分开

第43步的 `ClrZeroBytesNotNull` 是**旧模型**真实检查通过的反例；本步未修改它的源码或原日志。将原探针放到新模型后，恰在该反例第139行拒绝，证明结果的输入模型已改变，不能继续把旧证据当作当前模型证据。

为保留旧时期重放材料，将935个原生产编译产物按原始哈希归档到 `audit/logs/stage44-null-bytes/before-products.tar.gz`，SHA-256为 `7be339822ed70b8650790cee9f2afe483d7af4fa33bce6c1e01f006276fd076c`；5个修改前源码保存在同目录before树的 `.v.snapshot.txt`。归档是历史对象，不得直接覆盖新模型依赖后混用。旧审计文件逐一保持不变，但其中指向已改源码／项目表的输入哈希已过期，不能说全部历史检查仍通过。

本轮不修改旧测试、不削弱正式门禁。全量测试仍有旧诊断及模型迁移引出的冻结身份诊断；新增8项测试单独验收，具体数量与ID差分以 `test-delta.json` 和 `complete-test-delta.json` 为准，不用“新测试通过”代替“全仓通过”。

## 清理与交付

先逐项记录并复核路径、类型、大小、哈希和目录成员，再删除本任务隔离构建树、codec变异树、一次性信任／探针编译产物。保留全部失败证据、精确快照、原对象归档、940个新生产可复用产物及既有缓存。清理前后的清单与实际结果分别见 `cleanup-*-plan.json`／`cleanup-*-preflight.json`／`cleanup-*-result.json`。既有lia缓存的自动变化单独记入完整性报告，不删除旧缓存。

## 尚未完成与下一步

实际 `OS_InitTCBList` 在锁定C的 `os_core.c:1591` 开始，依次清零整张TCB表、清零13槽优先级表、连接OSTCBNext、设置OSTCBList／OSTCBFreeList。当前只把**一个4字节槽**接到清零，不声称整表或这两次真实调用已接通。下一步扩大到真实表存储并连接函数调用／生命周期，然后建立TCB链、空闲／统计任务和对象池，最后组合OSStart与运行Inv。

GOOD_OS／同程序K1–K4、完整task／ISR safety、OSInit／OSStart可达性仍开放，uCOS3尚未启动；六门历史94／1／1／1／1／0不晋级，没有commit／push。最终目标保持active。

## 证据入口

- [ADR-0006](../docs/adr/0006-清零与空指针采用唯一编码.md)
- [生产证明](../certiucos/v293/proofs/V293NullBytes.v)、[独立探针](probes/V293NullBytesProbe.v)
- [完整最终报告](logs/stage44-null-bytes/final-report-complete.json)、[原187源冷构建](logs/stage44-null-bytes/cold-build03.json)
- [正式工程信任检查](logs/stage44-null-bytes/active-trust.json)、[测试差分](logs/stage44-null-bytes/complete-test-delta.json)
- [中文逐步讲解](../docs/开发中/时钟中断如何跳过零延时任务.md#已继续清零现在可以建立空指针所有权)

### 审计脚本自身的复核

最终对抗性复核发现，首版旧定理扫描器只统计到436条，漏掉了缩进的声明和名字末尾带单引号的声明。保留该子集结果与日志，新增完整扫描：覆盖5个文件实际全部526个Lemma／Theorem／Corollary头，按顺序比较原始陈述文本（不忽略注释／字符串），全部完全不变。分项为69／106／87／200／64。新回归测试还覆盖缩进、单引号名字及注释中的伪声明。这是加强检查和更正计数，不是更改旧定理、重写旧证据或放宽门禁。详见 `old-contracts-complete.json`。

最终全量1146测试：391项失败、1项错误；原377诊断全部保留，新增15项均为所改源码的历史哈希／精确前缀身份检查，新增8项测试通过。具体ID和原始trace全部保留，全仓仍未通过。
