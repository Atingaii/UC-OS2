# 第267步：完整活跃调用的有限全局执行和挂起资源

## 本步补的是哪一个缺口

第266步已经在同一非空 typed 堆上独立证明原 `ProgSim`，但没有另立从完整调用入口开始的有限全局执行结论。本步只新增审计证明 `audit/probes/V293ActiveCallTraceProbe.v`，不改变生产接口、C、AST、框架或工程登记。

`FTfinite_call` 从**原来的** `FWtasks / FWos br cs ncs` 出发，经原框架 `V293_global_steps` 构造：

`sfexec 114 → 查找函数 → alloc saved → 初始化 → running=true → encrit → nesting 1→0 / lock=0 → OS_SchedNew → 目标指针更新 → 优先级比较 → 计数 mone+1=0 → cache 6→4 → switch → 目标原有 pending → excrit → sret/free → 目标 caller`。

不是把中间状态作为入口；实际分配、初始化、调度、复制、切换和释放也不是主定理的前提。主前提只有 running 块对原堆新鲜、saved 块对入口堆新鲜。对**任意给定 fresh 分配**都存在这条有限执行；这不是所有执行终止、任意中断交错或公平性的结论。

## 证明结构及复用

| 根 | 含义 |
| --- | --- |
| FTbody_prefix | 在已分配的 saved 上构造归一化活跃函数体的局部前缀，保留真实守卫与调度 |
| FTfixed_prefix | 在第266步同一入口资源上证明上述前缀，不假设抽象前缀执行 |
| FTenter | 原全局语义的函数查找、fresh 分配、分配结束 |
| FTto_switch | 原局部到全局提升及实际优先级复制，抵达 switch 前 |
| FTsaved_load | 从保存区空间资源得到真实 load |
| FTfinite_call | 实际 switch 与目标 pending 返回，接通完整入口到目标返回的有限执行 |
| FTendpoint_metadata | 读取实际终态定义，区分切出与目标任务各自的代码、环境和临界栈 |
| FTsame_entry | 同一入口上同时成立第266步原 ProgSim 和本步有限执行 |
| FTnonvacuous | 真实存在两个满足新鲜性条件的块，入口不是空条件 |

`FTsame_entry` 复用 `FWcomplete_active_simulation`，后者经 `FWactive_resources` 处理所有 fresh saved 的同堆资源链；有限执行则独立使用已有空间更新、调度执行、copy、switch 和 pending-return 定理。两者均不以中间执行或 ProgSim 为公开前提，不另建替代解释器。

`FTbody_prefix` 将既有活跃体局部构造用于任意外层 saved，去掉外层 kcall 后再用原提升定理接回，避免重复压入调用续体。旧证明冻结，未为复用而重写旧文件。所有新增内容留在 audit，不新增生产文件或覆盖行。

## 可以在终态检查什么

原来执行的任务为 OwnershipWaiting；切换目标为 OwnershipReady。二者不是“同一个调用从头执行到同一个任务返回”。

| 对象 | 终态结论 |
| --- | --- |
| 目标任务代码 | SKIP / kenil / kstop：目标原有调用已返回 |
| 目标局部环境 / 栈 | 环境恢复 emp，退出自己保存的临界栈顶，余栈 ncs |
| 目标 saved 块98 | free Tint32 真正成功；偏移0至3均为 None |
| 切出任务代码 | 仍是 RPpending，等待继续 excrit/sret；未返回 |
| 切出任务环境 / 栈 | saved 仍指向新鲜 bs，临界栈仍是 false::cs |
| 切出任务 saved | load Tint32 bs = 0，未被目标返回错误释放 |
| 全局字段 | current 指向目标，cache=4，counter=0，nesting=0，running=1 |

这些内存结论来自真实执行后堆与释放的逐字节 frame，不是仅对预设常量作判断。代码和任务元数据结论由同一个实际终态定义读取，不能据此声称挂起任务已经恢复。

## 预先冻结的对照与审稿边界

实现前冻结 protocol.json 及 SHA。沿用 `FWpending_contract_control`：仅把入口目标任务的 RPpending 换成 SKIP/kstop，其余程序和物理堆不变，则接口要求的 pending 等式失效。这仍只是**契约对照**，不是一个完整 mutant 程序执行；不能证明下游机制必要或正确。正向下游结论来自各自实际步与堆资源，不用早期拒绝替代。旧的真实栈原语对照和 current/cache 中间态反例保留，不宣称本步新增下游消融。

- 目标 pending 已经存在；尚未证明其安装来源。
- 切出任务仍挂起；未证明再次调度或返回，不承诺公平性。
- IE=false，保存栈顶=false，沿用 ADR-0005 / ADR-0010 的源码级切换边界；不是外部 port/ABI/硬件精化。
- typed high=88，而配置最低优先级为12；不是完整全局 Inv，不是初始化可达证据。
- 特定双任务 typed 实例不是所有路径 OSIntExit，不是任意 client，不是完整中断返回，不是 `WFInt`，不是 `GOOD_OS`。
- K1–K4 未闭合，uCOS3 未开始，未提交／推送。总目标仍按老师要求先完成 uCOS2，再进入 uCOS3。

## 来源、核验与下一步

固定 V2.93.01 提交仍为 0c4a48e6fbc6e915714e816196619a5481accf0c 加两类既有授权修复；OSIntExit 位置为固定 os_core.c:693–736。本步 source-identity.json 是此前来源记录的副本，逐项重查哈希与行锚点，不代表重新预处理或重估覆盖。新增证明不在 _CoqProject，不能算新增生产覆盖。

串行稳定重复编译、逐根 Print Assumptions、递归 coqchk，核验期间不编辑任何 Coq 输入。Python 回归检查接口、来源和边界，不替代 Coq 内核检查。全量测试比较第266步具体失败/错误 ID 和顺序，不只比较数量；不改旧测试或冻结证据来制造通过。

实测结果见 audit/logs/stage267-active-call-trace/verification.json。README 与状态文档仅前插本步，旧尾部逐字节保留。全仓审计和旧空白门若失败，仍保留失败；局部检查点不代表全仓通过。失败编译快照保留，清理仅涉及经逐路径/大小/SHA 确认的一次性驱动、备份和本步临时阅读文件。

下一步应解决生产共享 Inv/初始化与已有 pending 来源、切出任务恢复等连接义务，而不是继续以同类局部实例冒充 GOOD_OS。具体缺口仍需对原顶层入口逐项核对。

## 本步实测

| 检查 | 结果 |
| --- | --- |
| 稳定编译 | probe24 / stable-probe，源码 SHA 一致 |
| 信任检查 | 9个独立根；递归 coqchk 通过；756项 Coq 输入期间未改 |
| 根假设 | 仅既有 classic / functional_extensionality_dep |
| 构建／项目审计 | 通过；不新增生产文件 |
| 前步／新增回归 | 各5项通过 |
| 全量测试 | 2500项，429失败、1错误；与266失败/错误 ID 及顺序完全相同 |
| make audit | 退出2：旧函数证据输入身份过期；旧门不改 |
| git diff --check | 退出2：旧 inferules.v:581–586 空白；框架不改 |
| 旧输入 | 1070项，仅中文入口前插；旧尾部精确保留；另重查171项前步冻结 manifest |
| 编译证据 | 保留25份快照，其中19份非零退出 |
| 清理 | 逐项确认后删除9项一次性材料，共723759字节；既有缓存恢复原 SHA |

首次新增回归曾因 sha256sum 摘要文件包含文件名、读取器误用纯摘要比较而失败；首次全量2500项为430失败/1错误。只修正读取器为严格核对摘要和文件名，不改冻结摘要；首次日志保留，最终 full-tests-fixed.json 恢复为429失败/1错误。见 reader-format-fix.json。

前步检查点在开始前通过；本步前插文档后，前步检查点拒绝文档身份，原始日志保留，不改其 manifest。这里的局部通过不等于全仓或整核通过；详见 verification.json 和只读 checkpoint.py。
