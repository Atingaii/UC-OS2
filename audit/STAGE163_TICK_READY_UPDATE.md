# 第163步：原 tick 单次等待节点更新，归还同一共享 core

## 本步在做什么

第162步只连接了 clock++ 的借还。本步连接原 `encrit ; (delay ; (advance ; excrit))` 单次迭代：真实 TCB／bitmap／scan-pointer 写入，随后使用已有合法抽象任务步，把更新后的资源归还到同一个 clock／task／ready core。

生产文件：`certiucos/v293/proofs/V293TimeTickReadyUpdate.v`；独立入口与对照：`audit/probes/V293TimeTickReadyUpdateProbe.v`。固定 C、配置、AST、framework、tactics、旧证明与旧冻结证据不修改。前瞻对照方案见 `audit/logs/stage163-tick-ready-update/protocol.json`。

## 资源接口与证明路径

1. caller 在 **IE=false** 时显式持有 focused canonical TCB、其他任务、ready/table、clock 和 scan-pointer。只使用一组 abstract task/event/current/time 槽，不另补一份 raw TCB 或 clock。
2. canonical record 不拥有 Next；time-wait 还不拥有 pend。`V293_tick_wait_missing` 明确列出 caller 必须补齐的字节。
3. `V293_tick_ready_wait_before_open` 只重排和展开已有权限。类型纯事实可以擦去／补回，物理字节权限不删除。
4. `V293_tick_ready_wait_iteration_hoare` 使用原 InfRules 与既有原单次迭代 Hoare，不以成功执行或表达式求值为假设。
5. `V293_tick_wait_absinfer` 经已有 `V293_tick_wait_transition` 作合法 abstract step；不是任意赋值抽象表。
6. `V293_tick_ready_wait_raw_close` 精确归还同一 `V293_time_ready_core`，并保留 scan、Next、到期后 delay／pend／event 残余及完整 caller frame；结论不使用 `Atrue` 丢弃残余。
7. RuleSem 只通过既有 RuleSound 正向导出。`CurLINV` 从 core 已有的 `CurTid` 与 caller frame 导出，不要求 caller frame 再拥有一份 current 指针。

## 独立入口为何不是空真

两项 task-map 记录：ready priority4、等待 semaphore 的 priority6；初始 bitmap=16、group=1，priority table 有13槽。TCB 字节、时钟37、scan 指针、只读 current 和 canary99 从分离的 encoded bytes 联合构造，栈顶1满足 `INUM=2`。抽象槽另在空物理堆构造后与同一物理堆合并。

当前任务见证不在这两个 task-map 记录内，LocalInv 是旧空见证；这只排除局部契约空真，**不表示初始化或内核可达状态**。

## 必须区分的验证

- 非空入口 + 正式 InfRules 实例：检查新接口可实际满足。
- 旧独立操作语义在同一入口运行：检查实际输出字段，不是新 RuleSem 的运行测试。
- d=1：priority6 到期后 bitmap=80，依然非空且 group=1；仅中和抽象任务更新，其他物理输出、END 和控制状态均保持不变，应因 task／ready 不一致被拒绝，不能靠空 bitmap 的提前拒绝冒充下游机制有效。
- d=0 与 d=3：分别保持等待与递减到2，不能误唤醒。
- 到期后的 Next、delay、pend、event 不属于 ready canonical record，必须以残余完整归还，不能拿 load-only 或 `Atrue` 投影替代精确资源等价。

## 明确未完成的目标

这是 **disabled-entry、单个未挂起等待节点** 的 focused 接口；尚未证明任意共享 core 都能打开成该前置条件。不是 IE=true 借入，不是生产 ISR 安装，不是完整 while／tick 函数／API，也未覆盖 taskstatus 无法表达的 suspend／flags。

生产 LocalInv／Inv 安装、CPU hook、初始化、WFIFun、源码级 GOOD_OS 与同程序 K1–K4 仍开放。无新增整函数覆盖信用；第一阶段尚未完成，不开始 uCOS3，不提交／推送。

## 验证状态

- 生产主规则与完整探针编译通过；40 个新增证明根、333 个活动模块和 53 个额外探针（合计386）独立 `coqchk` 通过。检查期间541份Coq输入未变，实际假设仍仅为既有 classic／funext_dep／Eqdep。
- 新增7项回归全部通过；三轮全套回归均1972项、423失败／1错误，完整旧失败／错误ID集合不变。结构测试不替代Coq证明。
- 构建与清理后重建退出0。旧 `make audit` 仍退出2：PROJECT AUDIT通过，但function evidence identity过期；旧 `git diff --check` 仍是framework/logic/inferules.v的581–586行尾空白，不改旧问题来制造全绿。
- 53次编译快照（含45次失败）完整保留。红灯回归中的一项把注释里的Atrue误当作结论，修正为先剥离注释，结论仍禁止丢弃式Atrue；没有弱化生产契约。中间编译失败不计作消融结论。
- 逐项确认后删除8个一次性目标，共680190字节；恢复原有 `.lia.cache` 和 `.nia.cache`。保留源文件、独立信任检查日志、全部编译失败快照和可复用Coq产品。
- 对28815份旧文件逐一比对，仅README、状态说明、追加的项目入口及生成依赖有预期变化；固定源码／配置／AST、framework／tactics、旧证明／测试和旧冻结证据不变。

机器验收：[`verification.json`](logs/stage163-tick-ready-update/verification.json)。本步为局部资源连接检查点，**不是整核或完整tick完成**；六门保持94/1/1/1/1/0，无新增整函数信用。下一步仍需任意共享core的focused打开、其他节点分支与整链连接，以及生产Inv／LocalInv、完整函数和初始化闭合；第一阶段未完成，uCOS3未开始，总目标active，不提交／推送。
