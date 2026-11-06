# 第120步：完整函数体连接第二个 Hook，明确 Freshness 的资源边界

## 1. 与最终目标的关系

唯一目标仍是配置固定的 uC/OS-II V2.93.01 源码级 `GOOD_OS` 及同程序 K1–K4，再按老师附件推进 uCOS3。本步不是整核或整函数成功证明，不修改 C、配置、AST、框架或已冻结历史证据。

上一接口的剩余 Hoare 前提是“第二 Hook + 发布”。本步证明实际第二 `scall` 后，将其缩小到原 `V293_TCB_publish 108 93 94 95 96`，该节点包含链表发布、就绪位、计数、退出临界区及返回0。发布路径尚待连接；不能把假设发布正确写成已经成功返回。

## 2. 本次真正闭合的内容

生产文件：`certiucos/v293/proofs/V293TCBSecondHook.v`。

- `V293_tcb_second_hook`：从完整参数／局部资源出发，用第119步可逆视图和已有 typed `call_rule` 推导第二个真实调用，返回相同调用者资源；不是把该调用的 Hoare 正确性当作前提。
- `V293_OS_TCBInit_free_body_after_second_hook`：复用原完整 `V293_TCBInit_function_body hi hc`；其 Hoare continuation 仅剩发布，不再包括任何 Hook 调用。
- 第一个 Hook 的外部规格携带 `owner-share ** R`；真实优先级槽写入后已将 owner 与共享池半权限合并、写入并归还，因此第二 Hook 的规格只携带 `R`。其 `GoodFunAsrt R` 取自原证明的 `proj2 good`，未另加更强假设。
- 原七参数、两局部、CPU保存单元、类型化初始化节点、调用者 frame 保持。视图不是复制物理权限，只有空堆环境事实可以重复使用。

两项生产根及17项本步探针根通过 `Print Assumptions` 检查；最终结果见本步 `trust.json`。接受的假设仅既有框架的 `classic` 与依赖函数外延性，不新增公理或洞。

## 3. 为什么不能直接删除 Freshness 前提

这里要求的是 **新分配节点地址不等于 `RESERVED` token**。堆分离约束的是实际存储字节，存于槽内的指针值并不自动占有被指向对象。

`audit/probes/V293TCBSecondHookProbe.v` 构造实际非空字节状态：

- 固定参数／局部、完整初始化的 block501 节点、当前任务和调用者 sentinel；
- block403 的 priority5 槽以半权限存放 token；
- token 可取 `(501,0)`，与新节点地址相同，而完整 `TFFull (owner-share ** FPR)` 仍然成立。

`TSAliasPhysical` 证明上述资源可满足，`TSOwnerRead` 检查真实槽读值；`TSAliasFreshnessCounterexample` 正面证明从这一物理前置推出地址不等式的命题不成立。不是只靠某次编译失败猜测反例。

这只说明**当前物理前置不足以推出 Freshness**，不说明此状态可由生产初始化／分配器达到，也不构成新的 C 漏洞或第三类授权补丁。原 C 的 token 表示与模型符号地址的域分离、分配器来源／可达性仍须证明。不在 token 地址伪造一个存储单元来制造不相交性。

## 4. 非空调用实例和前瞻单因素检查

同一个 `TSSpec token cs` 有两个固定函数项：990 的首 Hook 携带 owner，991 的第二 Hook 不携带 owner。`TSFirstCallChecked` 和 `TSSecondCallChecked` 对所有节点／next 使用同一有限 Spec，通过既有逻辑参数承载具体地址，不随节点重建规格。后者另有完整字节入口和实际 ptcb 参数求值。

`TSAdmitsExact` 在同一个第二调用物理状态上检查规格允许的指针、任务和结果，另有正常接受和三项错误拒绝。它们是外部契约边界检查，不是 Hook 函数体执行、`WFIFun` 或完整成功路径。

控制协议先写入 `controls-plan.json`，再生成两个源；唯一源码差异为 token block405／block501。对应 owner 槽的指针编码必须随 token 改变，其余 TFInput 基础物理字节、GE／LE、节点、参数／局部及脚本不变。两组先分别通过完整物理资源与真实 owner 槽读取的共同检查，打印 `COMMON_INPUT_CHECKED` 后才验证相同的节点不等式：Normal 通过，Aliased 在此不等式处失败。没有将早期入口拒绝冒充后续机制生效。

## 5. 验证、旧失败与证据

目录：`audit/logs/stage120-tcb-second-hook/`。

- 原协议早于新生产证明；保留唯一生产编译和探针全部尝试的原始日志／快照。探针前6次失败分别涉及未显式导入的符号、load单调性接口形状和资源展开不足，均未删除；最终 `proof01`／`probe07` 通过。
- 活动源286份，其中目标183、框架／tactics 103；全部活动模块及5个直接探针模块运行 `coqchk`。它检查构建产物，不代表整程序根定理已经存在。
- `make build` 是增量构建，非 clean build；前后结果见日志。1430个生产产品保留，原1425个哈希不变。25个直接探针产品保留。
- 新增9项结构回归通过；清理前后全量1644项中仍有423 failures、1 error，失败ID集合与第119步相同，不能写“全量通过”。
- `make audit` 保留退出2及旧 `stale function evidence input identity`；空白检查保留既有6行 framework 问题，无新增空白问题。
- 原23536份既有文件除 README／状态的新增前缀、`_CoqProject` 追加和依赖文件外不变。旧文档正文、历史清单、源码身份和覆盖门不改写。
- 清理先完整列举并逐一核对一次性 Trust／Normal／Aliased 源及产品，再删除；恢复原 `.lia.cache`／`.nia.cache`，保留探针、生产产品、日志、源快照及所有旧材料。实际数量以 `cleanup.json` 为准。

最终机器核验入口为 `verify-checkpoint.py`，汇总 `checkpoint-report.json` 与冻结清单；文档中的结果须与实测一致。Git 仅只读检查，未提交／推送。

## 6. 接下来做什么

1. 在同一个生产 Inv 中连接开启中断后的发布临界区：动态借出 head／旧头Prev／ready组与行／counter，更新后归还；不能套用入口中断已关闭、共享字节私有持有的快照定理。
2. 从真实初始化／TCB分配域导出节点与 token 的非别名义务，消去目前保留的 Freshness 前提。
3. 连接两 Hook 函数体、标准整函数 `BuildPreI/BuildRetI`、生产 `Inv/WFIFun` 与初始化，再推进顶层 `GOOD_OS` 和 K1–K4；此前不开启 uCOS3。

阶段状态 `in_progress`；覆盖六门仍 `94/1/1/1/1/0`，总目标 `active`。
