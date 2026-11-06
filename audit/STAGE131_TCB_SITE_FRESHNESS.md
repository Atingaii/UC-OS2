# 第131步：由真实分配表成员性推出不别名，并检查 GoodI 可实例化性

## 本步改动

固定 C/config/手工AST、原 OS_TCBInit 七参数两局部、原标准 fpre／fpost、真实 err 接收调用、框架规则和旧证据不变。
新增 `V293TCBSiteFreshness.v`，在真实 allocator 提供 `NodeMember` 的分配点，用静态条件 `~In reserved (V293_tcb_table_sites tcbtable)` 直接推出节点不等于 RESERVED。
表目录恰为13个原记录起点，步长56字节；它不声明额外物理内存。

原字段初始化、首Hook、优先级发布、次Hook、有限活动发布均沿用；同一 joint Inv 仍提供六项借还。
`V293_OS_TCBInit_site_fresh_internal_contract` 沿用原 BuildPreI／BuildRetI，不再要求对任意状态成立的通用 Fresh。
纯事实加入时保留完整空间资源，不错误要求非空字节状态 entail 空资源纯断言。
相较协议字面写的fields前，本实现将纯事实插在原字段初始化后、首Hook及发布前；NodeMember由分配器取得并持续保留，不依赖新状态oracle。此证明位置调整记录在protocol-deviations.json，原协议不改写，C执行顺序不变。

这消除了原 Fresh 过强的问题，但**不是完整函数已经可以实例化的证明**。原 GoodI 和 Hook 前提仍在，不能从静态检查通过推断全部下游机制成立。

## 独立检查与单因素对照

前瞻协议 `protocol.json` 在生产 proof01 前记录，代码、地址目录和其他参数保持不变：

| 检查 | 具体结果／边界 |
| --- | --- |
| 原 RESERVED `(209,0)` | 直接计算接受，独立展开目录证明与全部13个起点不同 |
| 仅将 RESERVED 改为首节点 `(82,0)` | 单因素拒绝；另给真实目录成员证明，不能再提供 Outside |
| 同块但偏移1 `(82,1)` | 接受且证明不在目录，说明无需过强的“必须不同块”条件 |

地址探针直接构造器计算和展开目录，不引用生产 distinct 引理作为自身判据。
负控制只检查地址准入边界，不表示 Hook 或发布失败；偏移1只是符号地址模型的反过强测试，不宣称真实 C RESERVED 或 ABI 自动对应。

## 更关键的对抗性发现：当前具体物理 Inv 无法满足 GoodI

本轮新增后验检查 `SFPhysicalInvNotGoodI`，机器证明：

`forall sd li, ~GoodI SFPhysicalInv sd li`。

这里使用第128步原三次初始化实际执行定理 `CPActualInitialization`，提取同一实际返回内存中的非空物理核心，而非假定一个核心存在。
该核心的抽象状态为空。框架 GoodI 第一条件要求此不变式状态不能再兼容非空抽象扩展；但它可与只含 `curtid` 的 singleton 分离合并，因此与该条件矛盾。

此发现是后验对抗性检查，不伪装成事前约定的消融结果；源快照和编译失败保留在日志中。
精确结论是**当前这组具体参数的 Inv 无法满足 GoodI**；不泛化为所有未建立可满足性的参数化 Inv。
更不说明 Coq 或框架本身矛盾：不能成立的是被当作调用前提的 GoodI，不是已经无条件证明了 GoodI。

因此第128～131步物理借还／条件推导不能据此授予实际完整函数可调用信用。第130步的“GoodI尚未证明”对这组具体物理 Inv 应加强为“无法满足”；旧冻结记录原文保留，本说明和新状态前缀给出纠正。
本步不是生产全局Inv，全部完整前提的联合可满足性未证明，且这组物理Inv已被排除。下一步应将抽象任务／事件／时间／当前任务所有权及物理语义关系接入不变式，先证明 GoodI，再连接真实函数，不削弱框架门槛。
原 OS_InitRdyList 在 os_core.c:1448 将 OSTCBCur 写为 null；不能直接把要求非空 Vptr 的运行态 CurTid 拼到该初始化返回上来假装修复。后续先核对初始化／运行边界，再决定最小可满足表示；本步未实现或宣称该方案通过。

## 尚未完成的目标

真实全局语义Inv及初始化保持、活动ISR、Hook函数体／WFIFun、完整创建者成功和同一program连续组合、最终源码级 GOOD_OS 与同程序 K1–K4 均未完成。uCOS3未开始，总目标active。
六门保持94/1/1/1/1/0，不因多一个条件证明文件增加信用。
旧423失败／1错误及 make audit 的旧证据身份过期不删除、不改写；不声称已经修复这些失败。

## 验证入口

日志为 `audit/logs/stage131-tcb-site-freshness/`。生产稳定编译 proof01，独立探针 probe06；probe01～05 的技术失败全部保留，最终快照与源码身份相同。
最终各项实测以 `checkpoint-report.json` 和独立重算的 `verification.json` 为准，未运行检查不预记通过。

### 本步最终实测

| 检查 | 结果与边界 |
| --- | --- |
| Coq 8.18 源码／探针 | proof01／probe06 均exit=0，前后源码及快照身份一致；五次探针技术失败保留 |
| 构建及清理后构建 | 均exit=0；194目标模块＋103框架／tactics模块 |
| Print Assumptions | 15根，仅classic和functional_extensionality_dep；无新增公理 |
| coqchk | 297活动模块＋17独立探针，exit=0 |
| 新增回归 | 8项两次均通过，不代表完整系统端到端通过 |
| 清理前／后全量回归 | 均1741项、423失败／1错误；失败／错误ID集合与第130步完全一致 |
| 源码身份 | 五个原函数片段及C/config/手工AST身份检查通过；不新增自动C前端信用 |
| make audit | exit=2，旧stale function evidence input identity保留 |
| git diff --check | exit=2，仅既有inferules.v行尾空白，日志与第130步逐字节相同；本步交付文件无行尾空白 |
| 旧可复用产物 | 1480项生产产物及80项探针产物原哈希不变；本步总数1485／85 |

普通make首次再生构建元数据时使用了相对工具路径；随后以原绝对coq_makefile命令重生，Makefile.coq和conf已精确恢复基线字节，未放宽变化允许集或改证明。记录在build-metadata-restoration.json。

清理先登记并复核全部目标的长度及SHA-256，再恢复旧lia／nia缓存、删除9个一次性文件共686661字节：临时Trust源码／产物、生产文件生成脚本和已恢复的缓存备份。既有文件未删除；生产及探针可复用产物、全部失败日志／快照保留。
