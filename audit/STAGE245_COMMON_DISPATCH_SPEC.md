# changed / same 使用同一个精确调度入口

本步消除第244步 changed 与 same 的抽象操作不一致：**两条启用调度的路径现在都从 `sched;;spec_done None` 出发**，复用原实际 EOI → Enter → dynamic Exit → exint、原 bound LocalInv、Inv 和 BDspec。quiet 尚未合并。

## 为什么 same 也可以做一次抽象调度

实际调度不一定切换任务。若当前任务已经是最高优先级就绪任务，抽象调度可以选择它自己。生产模块 `certiucos/v293/proofs/V293InterruptCommonDispatch.v`：

1. `V293_equal_current_highest` 从 ready bitmap/task relation、当前任务对应的优先级，以及选中优先级与当前相等，推出当前任务最高就绪。
2. `V293_same_resources_sched` 从原物理资源提取 abstract task map 与 CurTid，建立原生 `sched_self` 条件。
3. `V293_same_schedule_reduce` 使用框架 `absinfer_sched'`、序列与序列结束规则合法消耗 `sched`，随后接回原 same 连续证明。不是直接重贴操作标签。
4. `V293_common_dispatch_entry` 的两个析取分支分别携带自己的有效性条件；不把互斥的 changed/same 条件同时作为全局前提，以免入口为空。
5. `V293_common_dispatch_BuildintPre` 建立共同强入口到实际 builder 的单向蕴含；`V293_interrupt_common_dispatch_continuous` 合并原 changed 与新 same 连续证明。

本步**显式增加 `V293_current_task tasks t nc` 纯条件**。它不是旧 same snapshot 自动给出的事实，也还没有从全局 Inv 或每个实际 builder 恢复出来。没有新增 heap、globals 或中间 Hoare 前提，但不能说未新增任何前提。

## 路线选择与对照

拒绝用 `spec_choice (sched;;done) done` 放宽统一规格：它允许跳过调度，并不能证明原精确调度操作在 same 下可执行。采用框架原生调度规则，不新增语义构造器、oracle 或内核修改。

独立 probe `audit/probes/V293InterruptCommonDispatchProbe.v` 检查：

- `CDbuilders`：changed/same 两条路径实际 BuildintPre/Ret 都实例化为**同一个 `BCintspec`**。
- `CDchanged_nonempty`、`CDsame_nonempty`：分别存在原 typed heap/abstract map 的分离见证；每条路径同一状态同时满足共同强入口和对应实际 builder。不是说两个互斥分支同时成立。
- `CDchanged_wrapper`、`CDsame_wrapper`：同一 BDspec、LDli、RDinv 和实际源 wrapper；`CDenvironment` 复用原候选 WFFunEnv/WFIFun。
- `CDcurrent_ablation`：固定一份任务表，仅将 abstract CurTid 从最高就绪任务改成等待任务，原生 `sched_self` 从成立变为不成立；`CDcurrent_only` 证明其余 abstract keys 全相等。
- `CDsame_abstract_steps`：明确给出 same 下 `sched;;done` 到 `done`、abstract state 不变的原生语义步。

上述消融**不是两次完整执行**，也不证明 quiet 路径适用。typed fixture 中旧 same 状态的操作字段被换成新入口时，仅用 action-free 断言构造状态见证；实际连续 Hoare 证明仍通过合法抽象步，不使用这种构造来搬运旧 Hoare 结论。

## 验证与剩余缺口

完整验证的实际结果以 `audit/logs/stage245-common-dispatch-spec/verification.json` 为准；Coq 编译失败快照和所有旧失败保留。新增 Python 检查只作来源／结构回归，不替代语义证明。旧423失败、1错误以及 stale function evidence 审计失败、框架历史空白失败不隐藏、不降低门槛。

这是启用调度的两分支局部连接，**不是所有 BuildintPre 的分类，不是 `WFInt`，不是 `GOOD_OS`，不是初始化可达**，未闭合同程序 K1–K4。统一操作只覆盖 changed/same；生产连续根本身仍参数化 intspec，probe 才通过字面 builder 等式固定为同一 BCintspec。原 all-clear 返回限制仍保留；没有独立新增返回侧非空证明。uCOS3 未开始，未提交／推送。

下一步须把“实际 builder 资源 → 动态分支条件”接通，明确当前任务关联应由何种 Inv 保持，再处理 quiet 的调度禁止条件。不能把本步单向蕴含倒过来使用，也不能以两个非空 fixture 替代全入口覆盖。

清理只针对本步一次性 Trust 驱动及其编译产物、恢复原有根缓存后的备份；源文件、失败快照、冻结日志和复用 Coq 依赖／产物保留。具体清单与恢复哈希记录在本步 `cleanup-inventory.json` / `cleanup.json`。

## 本步实测结果

| 检查 | 结果 |
| --- | --- |
| 生产模块／独立 probe | 6 + 14 个定理，Coq 8.18 编译通过 |
| 假设与递归 coqchk | 20 个根通过；仅沿用 classic / dependent functional extensionality |
| 新增结构回归 | 5/5 通过，不替代 Coq 语义检查 |
| 完整回归 | 2389 项，423 失败、1 错误；旧失败／错误身份及顺序逐项相同 |
| 全量构建、项目审计 | 通过 |
| make audit | 保留原 stale function evidence 身份失败，退出码2 |
| git diff --check | 保留原框架6行历史空白失败，退出码2 |
| 函数六门覆盖 | 94 / 1 / 1 / 1 / 1 / 0，不因本步局部定理虚增 |
| 整体目标 | GOOD_OS、WFInt、同程序 K1–K4 尚未闭合；uCOS3 未开始 |
