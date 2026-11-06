# 第273步：目标 pending 返回路径接入原 TaskSim

## 这一步解决什么

第272步只为已返回的有限 client 建立 TaskSim。本步把证明向前接到目标任务尚未执行 `excrit` 的 pending 续体，覆盖：

`SKIP → excrit → SKIP → sret → sfree(saved) → sfree(nil) → caller`

生产接口是 `certiucos/v293/proofs/V293PendingReturnTaskSim.v` 中唯一的 Theorem `V293_pending_return_TaskSim`。另有6个辅助 Lemma；独立核查位于 `audit/probes/V293PendingReturnTaskSimProbe.v`，共6根。这是有界范围的实质模拟连接，**不是整核 GOOD_OS 完成**。

## 精确前提与资源

- 初始 IE=false、si=nil、保存栈为 false::ci，全部 ISR 位清空。
- 调用表已有真实函数绑定；caller 的 SKIP 续体属于既有有限 client 家族。
- 目标任务独占 `saved ** (current_core ** CurTid)`。生产主接口没有 TaskSim、ProgSim、执行链或 free 成功作为前提，也不要求 InitTaskSt。
- 目标 LINV 使用既有空局部候选 `V293_shared_li`。旧 saved/RCframe 不是目标任务私有 LINV。

核心事实：在 IE=false、si=nil 时，这个既有 INV 只拥有空物理堆与空抽象资源。它允许把 current_core 留在任务侧；**不是删除了 INV 的义务**，而是从原 INV 定义证明其此分支为空，并在每个后继重新构造原 INV。

辅助单步接口量化**任意可分离外部 frame**，要求原 loststep 在该 frame 下真实进展、唯一后继和精确残余所有权。主接口逐步提供这些事实，构造原 TaskSim 的七项义务。释放使用原 free_mono、join_free，证明只消耗目标任务自己的保存区，不复制外部 frame。终点 P 是原 RDYINV ** LINV，不是 Atrue。高层可用零步匹配这些内部管理步骤；不修改原框架语义。

## 与原完整调用连接

`PTfull_call` 只要求同一 frozen 入口的两项 fresh 条件，沿用 FWtasks/FWos、CPpo、已有 pending 和原实际终止 caller。通过 FTto_switch 实际执行到 switch 前，再用原 lpstep 真正切换，交付切换后 pending 的 PTpacket：

1. 精确物理 join 与抽象 join；
2. 目标侧 saved98/current_core/CurTid；
3. 外部 STframe bs；
4. 目标 pending 原 TaskSim。

同时保留同堆实际返回执行：目标 saved98 四字节释放，旧 saved 与 canary 保留。两个推导的 switch 堆用同一个 store 结果相等连接，而非拼接不同堆。`PTnonvacuous` 构造 fresh 见证，排除空前提。没有把完整调用的实际终止 caller 改成非终止程序。

## 前瞻对照与反例边界

协议在实现前冻结于本步 protocol.json。

- `PTowned_free_boundary`：从真实 packet 得到目标 owned 堆可 free、原 whole 堆也可 free；保持 whole 堆不变，仅把任务侧分区改为 emp、全部物理资源划给外部，得到 owned free=None，且任意 R 的 saved**R 前提均不成立。**这是所有权分区边界，不是另一对完整 C 执行**；不是把 whole-heap free 成功当作任务所有权证据。
- `PTsaved_stack_boundary`：相同程序、堆、环境与中断状态，只改变保存栈顶 false/true，原 excrit 分别恢复 IE=false/true；空保存栈没有该 loststep。这里只核查原语边界，**没有证明 IE=true 的 pending TaskSim**，也不将其计入本接口覆盖。
- 未重跑或改写第270/272步的已冻结双完整执行证据；本步新增证据与旧证据分开计数。

## 验证与历史失败

两份新证明各稳定编译两次；逐根 Print Assumptions 和递归 coqchk 的实际结果见 `audit/logs/stage273-pending-return-tasksim/trust.json`。只允许原框架既有的 classic 与 functional extensionality，禁止新增证明占位或公理。

本步新增5项 Python 回归；全套结果及相对272的精确 failure/error ID 差分见 full-tests.json、test-delta.json 与 verification.json。不会删除旧失败或修改门槛换取全绿。make audit 的旧函数证据身份失配及 inferules.v:581–586 空白失败继续如实保留。272旧 checkpoint 会因新增工程登记/文档身份而失效，不刷新其冻结清单；逐项比较旧清单，仅允许 README、STATUS、_CoqProject 和生成的 Makefile 依赖身份变化。

编译失败快照保留。清理前记录每项路径、字节数与 SHA256，只移除本步一次性 Trust 产物/缓存备份，恢复原缓存；保留可复用 vo/glob、源码和核查日志。清理实测见 cleanup.json。

## 仍未完成与下一步

原任务仍 blocked；目标 pending 预先存在，沿用共同 si、typed high=88 非初始化见证和 ADR-0010 调用点抽象。未证明旧任务实际被调度切回、任意交错保持、切换前 TaskSim、完整共享循环、初始化可达、WFInt/WFIFun、同程序 K1–K4 或 GOOD_OS；uCOS3 未开始，未提交／推送。

下一项优先解决 IE=true 的 excrit 资源交接：core 必须从任务侧转入共享 INV，不能把本步 false 分支的空共享堆论证直接推广。最终仍须把同一程序、函数规格、初始化与中断环境连接为源码级 GOOD_OS；阶段目标保持 active。
