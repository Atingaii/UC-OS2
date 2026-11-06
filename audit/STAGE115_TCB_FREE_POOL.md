# 第115步：从共享空闲池取出真实 TCB，并归还变化后的链表

## 解决的问题

第114步的合法任务创建路径只接通了 TCB 空池失败。本步不把调用者预先持有的节点当成分配结果，而是证明：进入临界区后，从同一共享不变量借出空闲链表；真实读取头节点、读取其 Next、更新全局头；退出临界区时归还剩余链表，取出的节点转为调用者私有资源。

例子可写成：`head -> A -> B -> NULL`，取出 A 后变为 `head -> B -> NULL`，而调用者持有 A 的全部56字节。共享池不能同时保留 A 的写权限。

## 证明接口与边界

生产文件：`certiucos/v293/proofs/V293TCBFreePool.v`。

- `V293_tcb_free_chain` 是真实类型化字节的有限分离链表，不是固定 head／Next 快照；池内通过存在量词读取当前 head 和后继。
- 每个节点包含 Next 的完整写权限和其余22个单元，覆盖56字节，包括原布局中的 flags-ready 和填充字节。指针范围排除字段地址回绕。
- 池容量上界13，允许 NULL 和更短链表；弹出后把上界12的尾链提升到13以归还原池谓词。这里的13不是“池里必须有13个节点”。
- 池的精确性、`GoodInvAsrt`、ISR／辅助状态稳定性已闭合；精确性通过共享大内存上的真实 typed load 确定存在值，没有引入幽灵快照。
- `V293_OS_TCBInit_free_pop_transfer` 闭合实际 `head=ptcb->Next; excrit1` 片段：从链表自身导出范围与 Next 值，返回私有完整节点，并向同一 Inv 归还变化后的尾链。没有字段初始化或成功后缀的 `InfRules` 前提。
- 供上层连接原完整函数体的稳定接口是 `V293_OS_TCBInit_free_body_with_success`：IE=true 入口、真实 CPU 局部写0、encrit1 借池、`ptcb=head`、原空／非空判断已经连接。NULL 分支原样归还池并返回66。
- **该整函数接口仍以非空分支的字段初始化和原成功后缀证明为显式前提**。其声明有两个 `InfRules`，不能把它说成非空成功返回0已完成，更不是标准内部函数契约或 `WFIFun`。

C／AST 没有改变。对应 `os_core.c` 的 `OS_TCBInit` 位于2022–2151行，借池2045、读头2046、弹出2048、退出2049、字段初始化2050起。实际文件、函数切片和既有配置身份见 `source-identity-check.json`；本步不冒充重放历史逻辑修复目录。

## 排除空前提和错误资源分配

探针：`audit/probes/V293TCBFreePoolProbe.v`；不进入生产依赖链。

- 唯一 `FPInv` 同时接受空池、双节点池，以及写后仅剩第二个节点的池，不通过更换不变量逃避变化。
- `FPWholeEnabledLiteral` 给出 IE=true 的真实局部与共享池组合；CPU 初值99，入口尚未执行写0。调用者不持共享 head／节点地址401、501、502的字节。
- `FPActualPopInput` 给出双节点情况下真实弹出片段的空间前提；`FPPopTransferChecked` 在同一 Inv 上实例化闭合片段。
- `FPOnePool`／`FPSameInvariantChangedTail` 给出归还尾链的可满足实例；`FPTailNoPoppedBytes` 证明归还池不含取出节点501的字节。
- `FPActualHeadRead`／`FPActualNextRead` 从空间资源和内存拼接证明实际读取结果；`FPWrittenHeadRead` 证明真实 store 后 head 指向502。

这些是内存／局部证明实例，不是生产初始化可达性，也未建立全局任务表、就绪位图、已用／空闲节点全集关系。不能从这个形状不变量推出整核所有权保持。

## 前瞻单因素消融

实现前协议写明检查省略头更新；首次变异运行前另冻结 `controls-plan.json`；初次检查源因单元素列表记号冲突，在共同输入前失败，记录保留且不计入消融结论。修正为显式 `true::nil` 后，运行前冻结 `controls-plan02.json`。该次语义对照符合预期，但首源与协议同一文件系统时间刻度，未通过严格时间顺序门槛；保留记录、不削弱门槛。最终用 `controls-plan03.json` 前瞻重跑，写协议与创建变异源之间显式分隔时间刻度。两份检查源仅 `Action` 一行不同：

1. 执行原 typed head store，期待读到502；应通过。
2. 省略 store，保留完全相同输入和期待值；应因仍读到501被拒绝。

两者都先完成同一 `FPActualPopInput` 空间前提，以及 head／Next 的共同读取检查，再检验观测值。`FPOmittedWriteDiffers` 还正向证明未写入时结果不等于502，不把 Coq 编译失败本身当成语义反例。

该消融只检验一次物理 head store，不是整个变异 API、中断交错或退出临界区执行轨迹的验证；不能推称后续字段、Hook、发布机制也已验证。

## 实测和交付证据

证据目录：`audit/logs/stage115-tcb-free-pool/`。最终数值和检查结果以 `checkpoint-report.json`、`trust.json`、编译日志和冻结清单为准。

- 原生产文件、固定配置、源码／AST 和旧冻结证据保持不变；仅追加一个生产证明模块及独立探针／结构测试。
- 生产证明498行、21个证明根，探针422行、36个证明根；最终编译分别为 `proof30`、`probe19`，均成功。57个根的假设检查只列出既有 `classic` 与 `functional_extensionality_dep`；281个活动模块和独立探针的 `coqchk` 已通过（408.26秒）。
- 清理前后集成构建均成功，但不等于全新干净构建；新增9项结构回归两次通过，不替代 Coq 语义检查。清理前后全量均为1599项测试、423项失败、1项错误，失败／错误 ID 集合与第114步完全一致。
- `make build` 曾经由 PATH 中的 `coq_makefile` 重生成 Makefile，使生成文件的工具路径身份变化；用既定 opam Coq 8.18 的绝对路径重新生成后，`Makefile.coq` 和 `Makefile.coq.conf` 的哈希恢复为本步基线值，没有扩大允许变化范围。命令与结果保留在 `makefiles.json`／`.log`。
- `make audit` 的旧函数证据身份过期、`git diff --check` 的既有六行空白不能被消音；六门仍94／1／1／1／1／0。
- 清理前逐项记录并核对所有一次性源／产物，共删除39个文件、590795字节；保留1405个生产产物、5个探针产物、探针源码、失败快照和日志，恢复旧算术缓存，未删除既有文件。细目见 `cleanup-inventory.json`。
- 未提交、未推送；Git HEAD 未改。

## 下一步

用真实分配得到的完整私有节点，证明原字段初始化，再接 Hook／发布／返回0。还需与任务创建的预留槽所有权连接，以及构建统一生产 Inv、标准函数环境、初始化和源码级 `GOOD_OS`；同一程序 K1–K4 未闭合。阶段一未完成，uCOS3 未开始，总目标 active。
