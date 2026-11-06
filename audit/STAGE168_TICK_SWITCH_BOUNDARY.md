# 第168步：原 tick 后 hook 在既有共享 SWINV 中取还资源

## 这一步实际解决什么

前一步要求调用者已经持有拆开的 canonical task／ready／clock core。本步将完整原后 hook 接到已有 `V293_time_ready_inv` 的 `SWINV` 边界：打开同一共享资源，执行真实 clock++、运行标志判断、head 赋值和原 while，最后重新封装同一个不变量。

生产文件：`certiucos/v293/proofs/V293TimeTickSwitchBoundary.v`。
稳定接口：`V293_tick_post_hook_switch_hoare`；对应 `V293_tick_post_hook_switch_semantics` 由框架 `RuleSound` 得到。

**这里不是新建生产不变量，也不是证明任意 IRQ 借出。** 现有 `SWINV` 固有 IE=false、ISR clear；本步只在这个实际边界内工作。既有共享不变量具备 `GoodI`，不等于所有生产 ISR 已安装该不变量，亦不等于初始化可达。

## 入口为什么还需要一个观察

共享不变量内部隐藏了 current、taskmap、events 和 clock 的存在见证，而固定有限链的抽象程序必须使用同一 taskmap。因此入口使用 additive conjunction（`//\\`）：

- 一侧是既有 `SWINV`。
- 另一侧观察**同一状态**中共享抽象槽的值，额外资源放在 `Atrue` 中；不是再拥有一份抽象表。
- 打开时读取两侧的四个真实槽并逐一对齐，不能随意换成另一份 witness。
- canonical 记录中缺失的链字段、scan、globals 和 caller frame 仍显式提供，未偷藏或丢弃。

运行路径返回同一 `SWINV`、最终 scan、全部实际链 residual、globals、frame 及 pend choices；停机路径返回同一 `SWINV` 和原补片。clock 与任务更新位于重新封装的不变量中。

中断标志是空资源观察，不满足普通 `GoodFrm`。本步没有把它们塞进 frame 穿过程序，而是从返回的真实 OS 控制状态重建，随后调用既有 `V293_time_ready_switch_close`。

## 独立检查和单因素对照

探针：`audit/probes/V293TimeTickSwitchBoundaryProbe.v`；事先协议保留在本步 `protocol.json`。

1. 复用第167步真实四任务字节堆、13项优先级表、在 taskmap 中的 readonly current、scan=idle、canary99 和合法栈顶1。`PCjoint` 从字节建立资源，`PCpack` 只作布局打包；本步入口构造不调用新 opening 或新主定理。
2. 从同一堆直接封装既有 `SWINV` 和 additive view，证明正确入口确实存在，而不只是证明一条可能空真的条件规则。
3. `SCwrong_clock` 仅把 view clock 37→38；`SCwrong_tasks` 仅把 view taskmap 改为空表。Inv、真实抽象槽、物理字节和补片均不变，由槽读取拒绝，不是改变 bitmap 后的早拒。
4. 正式实例化 run=1 和 run=0/255，以及最大无符号时钟的相同入口。原操作执行明确复用第167步，检查全部字段、clock 和 canary；它不是运行新 `RuleSem` 的实验。
5. `SCclock_control` 复用第167步真实停机执行的同一个 `Mf`：正确抽象时钟可恢复本步完整 SWINV 入口；只中和抽象 clock 后连 `SWINV ** Atrue` 也不能成立。覆盖37及最大时钟，保留合法抽象步骤。
6. 任务更新中和负控明确引用第167步的分离命名端点，不把后缀输出与旧 while 输出冒充同一 `Mf`。

## 验收与保留失败

稳定生产编译为 `boundary09`，探针为 `probe07`；16次完整编译快照及12次非零日志保留，证明调试失败不算语义反例。24个新增 Lemma／Theorem 根已通过独立假设检查，338个活动模块及58个探针模块通过 `coqchk`；检查期间551份 Coq 输入保持不变，允许假设与第167步相同。最终机器结果以本步 `verification.json` 为准，不能仅凭本文宣告通过。

本步新增5项回归全部通过；三轮完整回归各2003项，均保持旧基线1998项中的423失败／1错误，完整失败与错误 ID 集合相同。构建和清理后构建均退出0。旧 coverage evidence identity 过期及 `framework/logic/inferules.v` 六行 whitespace 保留，不改写旧证据来刷绿。

已逐项核对后清理本步专用且验证后不再交付的8份 Trust 临时编译文件和缓存备份，共689123字节；恢复既有 `.lia.cache`／`.nia.cache`，保留正式源码、失败快照和可复用 Coq 产物。清理与旧文件哈希核对见本步证据目录。

## 距离最终目标还差什么

- 仍是已有局部 time／ready 共享不变量；尚非统一生产 Inv／LocalInv／ISR 安装及 enabled=true 首次借出。
- 仍限合法未挂起有限链；canonical 任务域匹配 bindings 加 idle，不覆盖任意任务状态。
- LocalInv 仍是旧空见证，不是初始化产生的可达状态。
- CPU hook、完整 tick 函数／API／ISR、初始化、WFIFun、源码级 GOOD_OS 及同程序 K1–K4 仍开放。

函数六门仍为94/1/1/1/1/0，无新增整函数信用。第一阶段未完成，uCOS3 未开始，总目标 active；本步不提交或推送。

下一步应证明此共享边界如何由真实中断／函数上下文取得，并把 CPU hook 和完整函数入口连上；不要把当前 disabled/clear 局部闭环外推为整核完成。
