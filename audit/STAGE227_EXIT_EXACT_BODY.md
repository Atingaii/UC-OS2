# 第227步：精确资源贯穿 OSIntExit 的 changed-priority 本体

## 本步解决什么

第226步只把精确 scheduler 契约接到 call + target assignment，并返回 opened storage。本步在不修改 C、配置、AST、框架或旧证明的条件下，把它接到原归一化 `OSIntExit` 的优先级变化路径：

`saved=0 → running 判断 → encrit → nesting 递减/lock 判断 → OS_SchedNew call → target assignment → 不同优先级判断 → counter increment → current copy → switch → excrit → return`。

这里的“完整本体”指该归一化本体在 running=1、lock=0、nest<=1、最高就绪优先级不同、ISR flags 清空且原 IE=false 的前置下；不是所有分支的完整 ISR，也不是最终 GOOD_OS。

## 生产接口

- `certiucos/v293/proofs/V293OSIntExitExact.v`：`V293_OSIntExit_exact_body` 是本步上层入口；`V293_OSIntExit_exact_dispatch` 连接精确前缀和原就绪 handoff。
- 入口复用既有 `V293_exit_ready_body_data`，包含真实 typed TCB 所有权、完整 lookup/ready/priority 数组、当前指针、控制字节、计数器及名称绑定。
- `V293_exit_exact_body_post` 返回同一 `SWINV`、精确 `p_local`、原两栈、共享 abstract op、全部私有绑定/保存局部槽及 `px`。新 private 不再额外追加 `Atrue`；`px` 的精度仍由调用者决定。
- selected `V293_shared_li` 恒为 `Aemp`，因此 `CurTid` 和 `p_local` 精确同占用可互换；这是从独立 current 半权限构造，不是从旧 `CurLINV` 或含 `Atrue` 的旧弱后置逆向恢复。该结论不能推广到任意 LocalInv。
- callee 只需同一 Spec 的精确条目，不以 callee `InfRules` 前提循环假设自身。callee owned CI 沿用 opened Inv 空尾；ambient ready/TCB/storage Inv 由本体重新封装。
- `switch` 后置表示本线程将来恢复，不是目标线程立即返回。共享任务、计数器、控制字节等在 `SWINV` 中为存在量，不冻结为切换前数值；就绪/typed TCB 关系继续由原不变量约束，storage 中 lookup/控制值本身尚无完整生产语义。

## 非空入口与环境

`audit/probes/V293OSIntExitExactProbe.v` 的 `XEnonempty` 直接复用既有 `JBentry_nonempty` 的同一真实物理堆：typed TCB、256 字节 lookup、ready 与 priority table、控制字节同时存在。waiting 当前优先级6、ready 最高优先级4。`XEactual_body` 在完全同一 `JBdata` 入口上验证新的完整本体，后置 `XEpost` 按字面列出同一 Inv、精确 local、两栈、绑定及 saved=0，不由打印候选类型自动生成。

`XEenvironment` 证明实际单函数原 scheduler 程序和 `XEactual_body` 使用的同一个 `XEspec` 满足 WFFunEnv；ambient RI 任意。这里只是单函数环境，尚未替换原三函数 Spec；不代表初始化可达或完整 ISR 已闭合。

## 预先登记的对照与证据边界

开发前固定 `protocol.json` 及身份，期间失败编译逐次保留日志和源码快照，不声称语义 TDD。

1. 递归复核第224步 `RLlocal_exactness_control`：固定状态只改变局部断言，排除弱 CurLINV 随意反推精确 local。它是 local-only 控制，不是完整前置反例。
2. 递归复核第218步已保存的 `JBexcrit_control`：固定内存与抽象资源，只中和最终 excrit primitive；原 false::ci 不满足目标 ci。只证明 primitive 作用，不是两次完整本体执行。

两项来自不同 fixture，不能拼接成同一执行轨迹；它们不是对本轮整个组合定理的单因素执行消融。完整组合语义由真实 InfRules 推导和 Coq 内核检查负责，不把早期拒绝当成下游都通过。

## 核验与范围

实际结果以本步 `audit/logs/stage227-exit-exact-body/verification.json` 为准：稳定编译、所有新根与两个旧控制的 Print Assumptions、递归 coqchk、两次构建、四函数配置后源码重建及全量测试。新 Python 测试只负责结构、身份和证据回归，不代替 Coq 语义检查。

保留历史423失败和1错误及其 ID 顺序；既有 audit 的 stale function evidence 与旧 inferules.v 空白错误不改写为通过。六阶段覆盖仍94/1/1/1/1/0。

尚未完成：将新 exact body 包进真实 Exit builders、整合 exact Enter/Exit/SchedNew 三函数 Spec、quiet/same 全路径精确后置、连续 EOI→Enter→Exit→iret、WFInt、完整生产 LocalInv/lookup/控制值/初始化、GOOD_OS 及同程序 K1–K4。uCOS3 按老师附件在 uCOS2 后开始，总目标保持 active。

## 阅读方法

先读 `V293_exit_exact_body_post` 看必须交还的资源；再沿 `V293_OSIntExit_exact_body` 中 seq_rule 查看前后断言；最后对照 `XEactual_body` 与 `XEnonempty`，区分“程序推导成立”和“入口不是空集”。下一步优先把这一接口接到 Exit 的 BuildPreI/BuildRetI 与三函数环境，而不是再造孤立小模型。
