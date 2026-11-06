# 第122步：开启中断的发布借还及原完整函数体连接

## 目标与边界

固定配置 uC/OS-II V2.93.01、源码级 `GOOD_OS` 和同程序 K1–K4 仍是第一阶段目标。完成后再按老师附件推进 uCOS3。没有修改 C、配置、AST、framework、tactics 或历史失败；六门仍为 `94/1/1/1/1/0`。

本步将 `encrit1 → 原发布体 → excrit1 → return 0` 接起来，并把它接回原 `OS_TCBInit` 完整函数体，消除原来最后一项待证明的 Hoare continuation。**这仍是条件定理：容量、同 Inv 资源接口、freshness 和两 Hook 契约未在生产系统内消去。不能据此宣称标准整函数契约、生产不变量或整核完成。**

## 生产接口

文件：`certiucos/v293/proofs/V293TCBEnabledPublication.v`。

- `publication_private/enabled` 只持局部指针单元、完整私有新节点和调用者 frame；共享 head、两行 ready、group、counter 和旧链均不在开启中断的私有前置中。
- `publication_shared` 用存在量词隐藏实际旧头、链长和 ready bytes；进入临界区后从同一个 `I` 取出当前值，而不是相信进入前的共享快照。
- `publication_enter` 使用实际 `encrit1_rule`；`publication_exit` 将完整新节点并入共享池，归还同一 `I`，使用实际 `excrit1_rule`。返回前置不再私有拥有已发布节点。
- `V293_OS_TCBInit_publish_enabled` 对原 `V293_TCB_publish` 给出一个 `InfRules` 结论，内部组合真实发布体和 `rete_rule` 返回0，不要求发布 Hoare 定理作为前提。
- `full_publication_view/restore` 保留真实七参数、两局部和调用者资源。初始化节点与发布输入使用同一组字节；视图继承前一步对部分字段确切值的忘却，不是可逆字段语义视图。
- `V293_OS_TCBInit_free_body_published` 对原完整函数体只有一个 `InfRules` 结论，没有待证明的后缀 Hoare continuation；原空池返回66、优先级预留所有权、两 Hook lookup 和 allocator freshness 都保留原条件。

以上接口不是 `BuildPreI/BuildRetI` 的最终标准契约，也不是 `WFIFun` 或 `GOOD_OS`。

## 容量不能被四个字面输入替代

共享物理池允许8位 count=255 的合法表示；再插入一个节点需要独立的 `Capacity` 前提，证明当前实际输入的链长小于255。池本身没有有限13节点 arena 与任务映射约束，因此不能仅从本步物理表示推出容量。

空／双节点 × 两行的四个字面输入只证明这些具体入口非空可满足。开启中断的私有前置不持旧链快照；进入临界区前可能有交错，不能由最初 count=0/2 推出所有借出状态都小于255。

因此，原先预期的“同一字面 Inv 无条件实例化整个开启中断后缀”本步**没有实现**：检查拆为真实 enter、已关闭中断且 count=0/2 的 body/exit/return，以及显式保留 Capacity 的整个 enabled suffix。前瞻协议原文不改写，不以缩小共享不变式却不证明关闭保持性制造通过。

## 独立探针与消融

`audit/probes/V293TCBEnabledPublicationProbe.v`：

1. 对共享表示证明 `GoodInvAsrt`、精确性和 IRQ/aux 稳定性，构造 `PEInv y`。精确性从真实相同堆中的 head、ready 与 counter load 的唯一性推出，不假定存在见证唯一。
2. 同一 `PEInv y` 可容纳空／双节点旧链；两行各自检查真实完整字节堆。调用者局部资源与共享 `invlth_isr` 分离。它**不是生产 Inv**，未包含任务映射／ready 语义关系。
3. 独立实例化实际 enter 和 exit；已关闭中断的 count=0/2 后缀实际连接原 body、exit 和 return0。整个 enabled suffix 仍明确带 Capacity。
4. `PEMissingBorrowImpossible` 独立证明：只有空共享资源时不能导出持有 head 实际字节的共享池。证明依靠空堆 load 不可能成功，不仅依赖某条 tactic 报错。
5. Normal/Omitted 源只改变 `provide_shared` 一处布尔值；先分别证明同一个可满足局部入口并打印 `COMMON_INPUT_CHECKED`，再检查同一借用结论。删去共享所有权的控制应在借用结论拒绝；该对照只检验借用所需资源，不给后续 store、位图、计数或完整函数授予消融信用。

## 检查与清理

所有尝试、精确源快照、终态检查与清理清单保存在 `audit/logs/stage122-tcb-enabled-publication/`；以 `checkpoint-report.json` 为最终实测状态。失败尝试不删除、不覆盖；本步不提交／推送 Git。

最终检查应包含正式生产／探针完整 Coq 编译、所有新假设根、活动模块和直接探针 `coqchk`、固定源码身份、增量 build，以及清理前后失败ID集合比较。既有全量测试失败、旧审计身份失败和旧空白问题继续保留，不写成全量通过。仅清理已逐项记录且复核路径、大小、哈希的一次性 Trust／控制源及产品，恢复原 lia／nia 缓存；保留交付产品、源文件、全部失败日志和历史材料。

### 终态实测

- 正式完整编译：生产 `proof18`、探针 `probe11`；全部源哈希与对应编译快照一致。
- 44个新证明根仅使用既有 `classic` 和依赖函数外延性；`coqchk` 检查288个活动模块及7个直接探针通过，不代表顶层整核根已存在。
- 新增12项结构回归全部通过；清理前全量1665项中仍有423 failures、1 error，失败ID集合与第121步完全相同。清理后再次复测，实际终态见检查点报告。
- 增量 build 通过；1440个生产产品中1435个旧产品、35个直接探针产品中30个旧产品的哈希均不变。不将增量构建写成 clean build。
- `make audit` 仍因旧 `stale function evidence input identity` 退出2；`git diff --check` 的原6行 framework 空白问题保持不变。

## 下一步

把物理池与有限 TCB arena、任务映射／优先级／ready 语义关系连接，使 Capacity 与 allocator/token freshness 可从生产不变量推出；验证两 Hook 函数体，连接标准整函数契约、同一生产 Inv、WFIFun 和初始化可达性。之后再闭合源码级 `GOOD_OS`／同程序 K1–K4，第一阶段完成后开始 uCOS3。
