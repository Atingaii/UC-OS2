# 第133步：初始化字节直接接入首个 TCB 调用

## 本步解决什么

第132步确认早期初始化后的 OSTCBCur=NULL、OSRunning=0，不能强套运行期 CurLINV。本步复用不依赖 CurLINV 的操作语义接口，把同一份返回内存直接交给原 OS_TCBInit，检查实际执行到哪里；不增加全局不变式，不修改 C、配置、手工AST或框架。

## 两个生产接口

文件：`certiucos/v293/proofs/V293BootTCBEntry.v`。

| 接口 | 已证明结果 |
| --- | --- |
| V293_boot_zero_payload_fields | 将真实清零的20＋32字节折叠为18个精确类型／值的待写字段，另保留Prev及3个填充字段；不引入未知旧值假设 |
| V293_boot_first_tcb_entry | 从原TCB初始化调用返回资源取出首节点及Next、空闲链头；其余12个节点、13个优先级槽、空活动头和caller frame仍分离拥有 |

四个保留字段位于24、40、42、43；Next位于20，未被payload重解释覆盖。指针旧值来自实际全零字节，非指针旧值为整数零。

## 同内存的执行检查

探针：`audit/probes/V293BootTCBEntryProbe.v`。`BTActualInitialization` 从原独立字节入口、非空caller，实际执行 OS_InitMisc → OS_InitRdyList → OS_InitTCBList，得到同一 Mf 上的原始返回资源与首TCB入口资源。三个调用只是 OSInit 片段，不是完整 OSInit。

`BTEntryToFirstHook`／`BTReachableFirstHook` 在同一静态program中直接调用七参数 OS_TCBInit，实际分配九个新鲜局部块，弹出首节点，完成原18次字段写入，停在首个真实 OSTCBInitHook 调用。空闲链头推进56字节，优先级字段读出12；实际 current 块166仍为NULL、running块185仍为0。首Hook之前没有 ready 发布或任务创建成功结论。

程序明确给出原TCB函数体，未给出Hook206的实现，因此证明该边界没有下一次局部执行步。这是该具体探针的缺失实现边界，不说明所有可实现的port都停住，也不提供Hook返回契约。没有用空函数代替Hook。

## 前瞻单因素对照

生产编译前的 `protocol.json` 固定了检查，不在结果出来后改协议。

`BTSameMemoryControl` 从同一份返回内存 M 建立两条存在性轨迹：

| 唯一变化 | 同一原函数、参数、地址、caller与中断状态下的观察 |
| --- | --- |
| 保留真实非空空闲链头 | 弹出首节点并写18字段，到达真实首Hook；prio=12 |
| 仅实际 store 空闲链头为NULL | 原空池分支返回66；首节点全部原字节、其余节点与frame保留，prio仍为0 |

对照不改变代码、其他输入或字段，不将提前返回当作后续Hook、发布体或整个内核已正确的证据。这些定理给出存在性轨迹，不是确定性或所有运行轨迹的定理。

## 不应从本步推出什么

- 这是直接TCB组件调用，不是完整 OSTaskCreateExt 或完整idle创建。prio12、ID65535与配置的idle参数一致，但栈大小64、块800只是有类型的fixture；没有证明真实idle栈存储、栈Hook或完整创建者参数来源。
- 全局标识符91显式绑定空闲链头；框架 OSTCBCur=60仍绑定实际块166。旧别名保留，不宣称整个program自动重命名或自动C前端对应。
- 两个TCB Hook、栈Hook、完整创建者、生产语义Inv／GoodI、运行期 initst、WFIFun、活动ISR、GOOD_OS／同程序K1–K4仍开放。不能拿已否定的纯物理Inv或ghost placeholder补洞。
- 六门94/1/1/1/1/0不变，不授予实际完整函数可调用信用；uCOS3未开始，总目标active。未提交／推送。

本轮已检查固定源码与analysis adapter：ucos_ii.h第1397、1405–1408、1414行只有三个创建Hook的声明，实际调用分别在os_task.c第391行和os_core.c第2118／2124行；当前checkout没有其实现体。检查身份见 `hook-source-inspection.json`。这不否认仓库外存在CPU port，也不重新开启已排除的汇编／硬件证明。

下一步应明确创建Hook的源码级契约／可用实现及抽象边界，再将真实栈初始化、创建者和TCB后缀连续连接；不能以臆造空Hook制造成功。

## 源码和验证

固定 `Source/os_core.c` 的 OS_TCBInit 为2022–2151行：2044进入临界区、2045–2048取空闲节点、2049–2097为本配置启用的18字段写入、2118首Hook、2124次Hook、2135–2147发布与成功返回、2149–2150空池返回。C/config/AST与旧证据保持原身份；模型仍是人工对应，不新增自动前端信用。

日志：`audit/logs/stage133-boot-tcb-entry/`。稳定生产proof06、探针probe07的源码与编译前后哈希一致。全部技术失败日志／快照保留。Python回归只检查结构和证据身份，不充当语义oracle；Coq编译、假设闭包与coqchk负责定理检查。

最终实测写入本目录 `checkpoint-report.json`／`verification.json`。旧423失败／1错误和 make audit 的 stale function evidence input identity 仍保留，不通过改变门槛或删除证据制造全绿。清理只删除逐项确认的一次性Trust文件和已恢复的缓存备份，保留可复用证明产物及失败证据。

### 本步最终实测

| 检查 | 结果／边界 |
| --- | --- |
| 稳定编译 | 生产proof06、探针probe07均exit=0；编译前后源码及快照哈希一致，所有早期技术失败保留 |
| 构建／清理后构建 | 均exit=0；196个目标模块＋103个框架／tactics模块 |
| Print Assumptions | 11根，仅原有classic与functional_extensionality_dep，无新增公理 |
| coqchk | 299活动模块＋19探针，exit=0，耗时约616秒 |
| 新增回归 | 8项；只检查结构与证据身份，不替代语义证明 |
| 清理前／后全量回归 | 1757项；423失败／1错误，失败与错误ID集合与第132步一致 |
| 源码检查 | OS_TCBInit、OSInit、OSStart和三次初始化准确片段身份通过，C/config/AST及覆盖清单不变；首次检查因模型文件名拼写错误失败，修正脚本后的source-check02通过，失败记录保留 |
| make audit | exit=2，既有stale function evidence input identity；未降低门槛 |
| git diff --check | exit=2，仅既有inferules.v行尾空白，与第132步输出逐字节相同；本步交付无行尾空白 |
| 旧文件 | 检查25241个基线文件，仅两份顶层文档的新增前缀、_CoqProject注册与生成依赖表变化；旧正文、源码和证据不改写 |

清理前逐项登记并再次核对全部8个目标，删除一次性Trust源码／产物及已恢复的缓存备份，共682123字节；原lia／nia缓存按基线恢复。没有删除既有文件，保留可复用生产／探针产物、技术失败日志和快照。上述有限检查点通过不代表整核目标完成。
