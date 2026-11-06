# 第228步：把精确 OSIntExit 接到真实函数边界

## 从上一轮推进了什么

第227步证明原归一化 `OSIntExit` 的 changed-priority 本体能交还精确资源，但尚未包入真正的函数调用边界。本步新增 `certiucos/v293/proofs/V293OSIntExitExactInternal.v`，不改变 C、配置、AST、框架或旧证明：

1. 复用既有 `V293_ready_builder_fpre` 和 `V293_ready_builder_unpack`。入口包含同一 typed TCB、完整 lookup/ready/priority 数组和控制字节，不另造较弱入口。
2. `V293_OSIntExit_exact_builder_contract` 使用实际 `BuildPreI/BuildRetI`。`saved` 局部槽和 local domain 交还 builder；返回外部接口 `V293_exact_builder_post` 保留同一 `SWINV`、精确 `p_local`、abstract op、两栈、全局名称及 `extra`。不额外追加 `Atrue`，也不从旧弱后置逆推精确资源。
3. `V293_OSIntExit_exact_WFFunEnv` 闭合 **Exit+SchedNew 双函数环境**：Exit 本体调用同一个 Spec 的精确 scheduler 条目，scheduler 条目也由原本体的真实 builders 契约证明。两者使用同一 ambient ready/TCB/storage Inv。没有以 callee 的 `InfRules` 当作前提绕过环境证明。
4. `V293_OSIntExit_exact_call` 使用框架真实 `call_rule`。外部接口没有 callee 的保存槽；调用规则负责函数局部变量的分配与回收，调用者 frame 原样保留。

这里仍仅覆盖 `running=1`、`lock=0`、`nest<=1`、最高就绪优先级不同、clear ISR、原 IE=false 的路径。**未替换动态三函数 Spec**，没有删除 quiet/same 路径冒充全分支精确契约；Enter+Exit+SchedNew 的原动态环境仍待整合。

## 一个需要显式处理的资源细节

本体后置里同时保留高优先级名称绑定、scheduler globals 和其它名称。旧宽泛后置能隐藏剩余项，本步不能这样做。

`V293_exact_builder_pack` 先精确重排全部资源，再显式从高优先级 `Agvarenv` 绑定推出 `Aemp`，最后调用原 `V293_exit_builder_forget_names` 恢复外部 globals。被消去的是内存和抽象状态均为空的名称事实，不是任意堆片段；真实内存、局部槽和当前线程资源都必须出现在返回式中。

`p_local` 使用 selected LocalInv **常 Aemp** 的既定边界；这不代表任意 LocalInv 或完整生产 ISR LocalInv 都已建立。`GoodFrm extra` 的精度由调用者负责，契约自身不增加垃圾吸收项。用于 `call_rule` 的 CurLINV 蕴含只是副条件的前向弱化，不替代被保留的精确后置。

## 同一非空物理见证

`audit/probes/V293OSIntExitExactInternalProbe.v`：

- `XIbuilders` 实际计算新双函数程序的 BuildPreI/BuildRetI。
- `XIentry_owned` 与 `XIcall_entry_owned` 使用完全同一 `JBstate(JBmemory ...)`：真实 typed TCB、256 字节 lookup、ready/priority、run/nest/lock、counter 和保存局部槽共同存在。调用入口把既有保存局部槽置于 caller frame，不把它当作 callee 的新局部槽。
- `XIpost` 按字面写出返回资源，`XIpost_identity` 与新 fpost 核对；`XIactual_contract` 与 `XIactual_call` 使用 `XIenvironment` 的同一个 `XIspec`。实际 call 定理 ambient RI 任意，取环境中的同一 Inv 即可配合环境定理使用。

这是非空入口的数学见证，**不是初始化可达**，也不是完整 ISR 的执行结果。切换意味着原线程将来恢复，共享变量在 Inv 中存在量化，**不冻结**为切换前值。存储布局闭合不等于 lookup/控制字节的完整生产语义已证明。

## 预登记控制及核验

开发前冻结 `protocol.json` 与身份。重新递归核验旧 `RBshadow_control`：固定程序物理内存、控制字节和抽象资源，**只改变局部名字及绑定**，把保存变量改名为 `running` 后，builders 仍接收非空前置，但运行变量的全局绑定前提被遮蔽。它只检验名称边界，是对“不需要防局部名遮蔽”的反驳；**不是两次完整执行**，也不说明后续比较、switch 或返回是否执行。这个控制不替代本步新组合的 Coq 推导。

失败编译及源码快照逐次保留，**不声称语义 TDD**。Python 新测试检查结构、身份和证据，不是程序语义 oracle。所有新根和上述控制用 Print Assumptions 与递归 coqchk 核验；精确结果见 `audit/logs/stage228-exit-exact-internal/verification.json`。

两次构建、四函数配置后源码重建、全量测试和旧失败 ID/顺序核对均保留实际结果。历史423失败、1错误、stale function evidence 的 audit 失败和旧 inferules.v 空白问题不改写为通过。六门覆盖仍94/1/1/1/1/0，未提交或推送。

## 还缺什么、怎么读

下一步把这个精确 Exit 契约适配到动态 logical-argument codec，并联合精确 Enter、scheduler 与 quiet/same 路径，再连接连续 `EOI→Enter→Exit→iret`。其后仍需 WFInt、生产 LocalInv/控制值/lookup/初始化、最终源码级 GOOD_OS 和同程序 K1–K4。uCOS3 按老师附件放在 uCOS2 完成后，总目标保持 active。

入门时先看 `XIpost`：它就是“函数返回必须还回来什么”；再看 `XIbuilders` 区分函数外部资源与局部槽；最后看 `XIenvironment` 和 `XIactual_call`，理解“调用有规格”与“规格对应的函数体也已证明”是两个必须同时满足的条件。
