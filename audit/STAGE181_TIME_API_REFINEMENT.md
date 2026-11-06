# 第181步：时间 API 的临界抽象步与精确返回资源

## 这一步解决什么

第180步证明函数真的运行并返回，但 setter 的物理时钟已经变成新值时，证明里的抽象时钟仍是旧值；探针也没有在返回时保留完整的共享资源。本步补上这两个缺口。

这里的“抽象时钟”是规格状态中的时钟，不是机器上的另一份变量。`spec_step` 是已有规格允许的状态转换；它本身不是 C 指令。我们把实际执行分成临界写入前缀和退出／返回后缀，在两段连接处证明规格允许转换，并证明转换后的强共享断言在同一实际物理堆上成立。

| 环节 | OSTimeGet | OSTimeSet |
| --- | --- | --- |
| 调用起点 | 沿用同一 Cprogram、未分配 API 局部槽的 TRmemory | 同样，实参由实际调用求值并写入 |
| 临界区 | 实际把物理 clock 复制到 ticks | 实际把 ticks 参数写入物理 clock |
| 临界点规格步 | 返回实际 clock，整个抽象状态 O 不变 | 仅更新 O 的 ostmid 为实参 n，返回 None |
| 同一实际 Mc | 新 action 下强 core 成立 | 同步后强 core 成立；n≠旧值时旧抽象 clock 被拒绝 |
| 退出及返回 | 恢复原中断快照，真实求值 ticks，返回实际 clock | 恢复原中断快照，真实返回 None |
| 资源 | 真实释放160／161，返回后保留 Ccore ** CurTid ct | 同样，物理与抽象 clock 都等于实际参数 |

**仍仅是有限、无交错的实际执行与单次抽象步的连接，不是全并发模拟或整核 GOOD_OS。**

## 对象身份保持不变

- 仍为 uC/OS-II V2.93.01、锁定上游提交与原固定配置；两类既有授权修复范围不变。
- `csrc/upstream/v2.93.01/checkout/Source/os_time.c`：getter 237–250 行、setter 267–278 行。文件／函数片段以及既有 AST 映射哈希见本步 `source-check.json` 和独立重算的 `source-recheck.json`。
- 不修改 C、配置、AST、框架、tactics、旧证明／旧测试／冻结证据、Spec／Inv／LocalInv 或覆盖信用。
- 继续采用 ADR0005 的 encrit／excrit 抽象，不把规范化说成真实 CPU 端口实现已验证。
- 探针程序仍是 `Cprogram = pumerge RAapi RAinternal`；不是全目标的完整函数环境。

## 生产接口及所有权

新增 `certiucos/v293/proofs/V293TimeAPIRefinement.v`：

- `V293_time_set_body_refinement`、`V293_time_get_body_refinement` 是两个供上层使用的函数体接口。它们从实际输入所有权推导 saved 初始化、临界复制的成功 store、原 body 到 excrit 前的实际路径、合法 spec_step、同一 Mc 上的强 core、实际退出／free／return 和最终 `core ** R`。
- setter 从实际 owned fields 推出旧抽象时钟槽；用已有 `V293_shared_replace_slot` 更新 owned 抽象槽。**没有把 store、spec_step、free 或返回终点存在性当作接口前提。**
- getter 合法规格步保持整个 O，返回值由实际 ticks 求值得到，不只是在规格里指定一个数。
- `V293_time_owned_return` 由两个局部槽的可写所有权构造真实释放及 caller 恢复；`GoodFunAsrt R` 保证从 callee 切回 caller 后仍可评价 R。
- `can_change_aop R` 限定 R 不依赖被完成的 action；不声称任意 action 敏感断言都能原样保留。
- `V293_time_copy_before_exit` 的精确所有权在原中断快照评价，实际机器端点则关闭中断并把旧 IE 压栈。中间关闭快照只展示 `core ** Atrue`，使用已有 core 对辅助状态的不敏感性；**不会把任意 R 运输到不同快照**。
- 真正返回后恢复原快照，结论是精确 `core ** R`，不是将余下所有资源丢进 Atrue。R 在探针实例化为 caller 的 `CurTid ct`，保留其半权限。

两个接口量化程序、调用者环境、continuation、heap、抽象状态、原中断开关／栈及地址和值；对 R 的限制明确写在前提中。它们没有证明全生产 LocalInv 或整个全局 Inv 闭合；这里的 core 指既有 ready／共享字段／clock 组合断言。

## 同一次调用及事先冻结的对照

新增 `audit/probes/V293TimeAPIRefinementProbe.v`。四项对照在实现前写入 `protocol.json`，身份记录在 `protocol-identity.json`：

1. **实际调用与资源闭环**：`Rset_actual_refinement`／`Rget_actual_refinement` 从同一旧 TRmemory 执行真实调用／分配，实际 Ma 同时满足强 core 与精确 JsetPre／JgetPre，再将该 Ma 交给生产 body 接口。最终 Mf 来自这次执行，满足 `Ccore ** CurTid ct`。没有使用上一轮将余下空间投影为 Atrue 的 `Lowned`。
2. **仅省去 setter 抽象同步**：`Rset_ghost_omission_control` 保持同一 Mc、代码端点、IRQ 快照、END None 不变，只比较新旧抽象时钟。新值被强 core 接受，旧值在 n≠clock 时被拒绝。拒绝依据是物理时钟 load 与旧 ghost clock 矛盾，不是 action 守卫早拒。它是断言层消融，不声称执行了另一份删指令的 C 程序。
3. **仅改源实参**：`Rset_two_argument_control` 用同一 Cprogram、同一初始 TRmemory 分别完整执行 n／bad 两次调用。两个返回态各保留精确资源、写出各自的物理／抽象 clock；bad 的物理结果不是 n。不是把一个成功终点改标签复用。
4. **getter 的只读抽象步与真实释放**：`Rget_return_control` 的 spec_step 前后整个 TRabstract 相同；实际返回 clock，保留强 core 和 caller 资源，由 freels 推出160／161每个局部字节都已移除。

`Rjoint` 只额外插入空 footprint 的 builder 事实；原来的 core 与 caller 资源始终从真实调用的 owned frame 获得，不凭空复制权限。

## 对抗式复核与边界

| 质疑 | 本步处理或限制 |
| --- | --- |
| 抽象步是否凭空假设？ | 从 owned fields 的实际抽象槽推出已有 spec_step，复用原规格。 |
| 成功与负控是不是不同 heap／action？ | ghost 对照用同一 Mc 和 END None；只换 ostmid 值。 |
| 最终强资源是不是仍被 Atrue 吞掉？ | 最终是 `Ccore ** CurTid ct`；中间辅助状态运输才采用 `core ** Atrue` 投影。 |
| 强 core 是否等于整个全局 Inv？ | 不等于；没有建立生产 LocalInv、完整函数环境、初始化或全局 Inv。 |
| 有限 trace 与 spec_step 的合取是否已是全局 simulation？ | 不是。生产接口暴露相同临界点及前后缀，但尚无覆盖全部交错的统一模拟关系或顶层定理。 |
| 任意 caller 断言能保留吗？ | 仅 GoodFunAsrt 且 can_change_aop 的空间 frame；实际 caller 资源采用满足条件的 CurTid。 |
| 负控能否仅靠新测试的字符串断言通过？ | 语义结论由 Coq 定理及递归 coqchk 检查；Python 只守护身份、接口形状和实际证据。 |
| 是否处理 tick、hook、ISR 或 K1–K4？ | 没有；这些仍是后续连接义务，不能从本局部路径外推。 |

六门覆盖仍 `94 / 1 / 1 / 1 / 1 / 0`。第一阶段整核源码级 GOOD_OS 与同一最终程序 K1–K4 **未完成**；第二阶段 uCOS3 **未开始**；总目标 active。没有提交／推送。

## 验证与继续入口

本步证据目录：`audit/logs/stage181-time-api-refinement/`。

- `stable-compiles.json`：最终源码的生产／探针 coqc 退出码及源码身份。全部失败编译诊断和逐次快照保留，尤其 body07 的停止不会改写成成功。
- `trust.json`、`trust-inputs.json`：新增21个定理根的 Print Assumptions、两个入口及递归依赖 coqchk；检查前后全部 Coq 输入不变，假设不得超出上一轮允许集。
- `baseline-tests.json`、`full-tests.json`、`full-tests-final.json`：新增5项回归和两次全套检查，逐项比较原423失败／1错误的完整 ID。旧失败不删、不放宽 gate，不声称全套全绿。
- `verification.json`：最终证据、旧文件身份、编译、构建、审计、清理、限制汇总；`checkpoint-evidence-manifest.json` 冻结本步交付表面。

下一步应将这个局部接口接入生产 LocalInv／完整函数环境与调用上下文，再推进初始化及 tick／ISR；不能把“多一个成功有限路径”反复计为整核进展。

### 已执行的检查

- 两份最终源码编译通过，新增21个定理根的实际假设闭包未扩大；两入口及递归依赖 coqchk 通过，检查期间577个 Coq 输入不变。实际依赖假设仍只有既有 classical 与 functional extensionality。
- 新增5项回归通过，构建与项目结构审计通过。全套2068项保留原423失败／1错误，完整失败／错误 ID 与本步2063项基线及上一轮结果一致；最终文件状态另跑第二遍全套，结果记录在 full-tests-final.json 并由 verification.json 检查。
- make audit 仍因已有 stale function evidence input identity 失败；git diff --check 仍报告旧 inferules.v 第581–586行空白。没有重新冻结旧函数证据、放宽审计或改旧源码制造通过。
- 30次开发编译中24次失败的日志和源码快照全部保留；成功版本只认 stable-compiles.json 指向的实际 coqc 退出码和当前源码哈希。
- 清理逐项记录在 cleanup-inventory.json／cleanup.json；仅清本步临时假设驱动及其产物、新生成Python缓存、恢复后不再需要的原缓存备份。保留既有缓存、失败证据及可复用 Coq 依赖产品。
