# 第89步：完整非空函数体接通发布 Hoare

## 本步实际进展

固定对象仍是 uC/OS-II V2.93.01 的同一个配置后 `OS_TCBInit`，源码及模型身份见 `audit/logs/stage89-tcb-linked-hoare/source-identity.json`；没有改 C、配置、两个授权修复、旧证明或框架。

`V293_OS_TCBInit_linked_body_hoare` 证明既有 `V293_TCBInit_function_body` 的非空路径：初始化局部、加载／pop 空闲表、退出临界区、18 字段初始化、两个真实 CPU Hook 之间的优先级表写入、任务链表发布、ready 位 OR、计数递增和返回 0。**仍有两个真实 `scall` 的保持型 Hoare 契约作为前提**，没有给出这两个 Hook 的实现，也没有证明其 `call_rule` 实例。

与第87步相比，第三项“发布和返回段的 Hoare”不再是前提；第88步直接证明的发布段现在被实际应用，而不是仅仅出现在导入列表中。由 `RuleSound` 导出相同边界的 `RuleSem`。这不是无条件整函数调用、`WFIFun` 或整核 `GOOD_OS`。

## 为什么需要资源桥接

前段资源按字段初始化顺序排列；发布段需要 `ptcb`、Next／Prev、Y／BitY／BitX、任务表头、ready group／选中行、计数以及可选旧头 Prev。桥接证明使用标准列表 `Permutation` 和分离逻辑重组：

- `V293_tcb_initialized_publish_view` 没有接受资源视图、求值结果或执行轨迹作为前提。
- 发布需要的资源被提取，剩余 **25 cell** 保留在返回 frame，包括优先级槽、`cpu_sr`、其余15个初始化字段、7个参数和空闲表头。
- 绑定断言也重组到正确位置，没有复制字节所有权、丢掉剩余内存或把发布改成规格级更新。
- NULL 与非NULL旧表头均覆盖；地址分离由前置空间断言要求，不额外声称所有任意别名都可用。

这里仍只拥有模型所需字段；新 TCB 的18字段加Next／Prev合计52字节，不是整个56字节TCB所有权。

## 独立检查与证据边界

新探针 `audit/probes/V293TCBLinkedHoareProbe.v` 不导入任何旧探针。字面联合入口的新18字段、两个局部和优先级槽均为 `Vundef`；新 TCB 为 block301/offset128，另一个任务表头指针为同block/offset256，空闲next另取offset384，避免把free-head保持与任务链表Next误混为同一值。核心初／终态分别拥有35／36 cell、96／100字节；加只读当前指针和哨兵为37／38 cell、101／105字节。临界区栈参数任意，入口中断关闭。计数254→255只是字节上界压力实例，不声称它在最多13优先级的全局内核不变量下可达。

探针分别检查：联合初始入口可满足、只开放两个Hook的完整body实例、返回资源可满足、优先级11／优先级槽／free-head／Next／Prev／旧头回链／ready group和行／计数255／栈大小的实际 `load`，以及返回0。最终字面内存可满足不是一次无条件执行轨迹；返回后的读取信用与有前提的整体Hoare连接必须区分。

单因素控制只把实际最终free-head的期望值从next改成原head／新TCB指针；保持导入、资源假设、读取地址和类型、证明体不变。正控需先通过，负控必须被内核拒绝。这只检查post读取接口，不把该拒绝算成所有下游机制都已验证。全体尝试（包括失败）及前瞻计划保留在本步日志中。

## 验证与未完成项

以本步 `final-report.json`、`trust.json`、`post-cleanup-tests.json` 和冻结只读复核为准。255个活动模块及1个独立探针的 `coqchk` 通过，43个定理／接口根的假设仅为框架既有的经典逻辑、Eq_rect_eq与函数外延性三项。生产／探针共有11次编译尝试，其中9次开发期失败均连同源码快照保留；最终生产proof04和探针probe07通过。单因素正控通过，错误free-head负控被预期类型不匹配拒绝。本步6项新增结构检查通过，固定最终源后的全仓1430测试仍有423失败、1错误，424个旧诊断ID原序未变；默认审计仍因覆盖输入身份过期退出2，空白检查仍只报告旧 `framework/logic/inferules.v` 行尾空白。增量构建不等同 cold build；既有全仓失败和默认覆盖审计失败不通过降低门槛或重写旧证据隐藏。

正式六门仍为94/1/1/1/1/0。两个CPU Hook实现／规格连接、调用分配和free的框架Hoare、启中断入口、整函数WFIFun、全局初始化及Inv、源码级GOOD_OS和同程序K1–K4仍开放；uCOS3未开始。任务继续active，未提交、未推送。

下一步先核对外部Hook规格与真实 `scall`／`call_rule` 连接。当前上游头文件在1397／1414行仅声明这两个Hook，`csrc/analysis-port` 明确不是可执行CPU port；相关只读身份记录在 `hook-boundary.json`。不能把“应用hooks关闭”解释为这两个CPU调用自动变成skip。
