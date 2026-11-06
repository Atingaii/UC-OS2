# 第299步：quiet 分支在当前任务最高时接入同一精确调度规格

## 前因与本步结果

最终目标仍是固定 uC/OS-II V2.93.01 的源码级 `GOOD_OS` 及同程序 K1–K4 回归，之后再按老师附件做 uCOS3。**本步不是整核完成，uCOS3 尚未开始。**

中断退出有两种物理行为：需要调度时选择最高就绪任务；嵌套未退尽、锁定或未运行时，不进行调度。以前 quiet 包装使用 `END None`，enabled dispatch 使用 `sched ;; END None`，两者没有直接共用这个精确的中断规格。

本步没有把规格改成“调度也行、不调度也行”。而是证明：**若入口的抽象当前任务本来就是最高就绪任务，一次 `sched` 可以选择它自己，抽象状态不变。** 因此，这部分 quiet 输入可以使用原 `sched ;; END None`，再连接已有完整 `EOI → OSIntEnter → OSIntExit → exint` 证明。

通俗地说：这不是凭空跳过调度，而是执行规格允许的那次调度，选中的恰好还是当前任务。

## 生产接口

[V293InterruptQuietSched.v](../certiucos/v293/proofs/V293InterruptQuietSched.v) 的稳定接口是 `V293_interrupt_quiet_sched_builder`：

- 输入是实际 `BuildintPre`，与原 quiet 过滤、最高就绪条件作**普通合取**。最高条件检查同一个状态，不复制抽象资源。
- 明确要求 `intspec i = Some (sched ;; END None)`，仍用原函数规格、canonical Inv 和 bound LI。
- 由实际入口推出低位 ISR 清空；继承第298步，不重新要求所有 ISR 位为 false。
- 首先通过框架的 `absinfer_sched'`、序列提升及序列结束规则精确消耗 `sched`，再复用第298步的完整包装。
- 不要求调用方先提供中间 snapshot、具体执行结果或全部 ISR 清空的证明。
- 不改 C、配置、AST、框架、旧证明、旧门槛或冻结证据，没有新增公理。

`V293_irq_sched_self_guard_sound/complete` 双向证明这个断言恰好对应框架的 `sched_self` 条件，没有靠一个不可满足的断言制造通过。移除不需要的 CommonDispatch 生产导入后，最终证明仍通过；生产证明不依赖审计探针。

## 非空见证与单因素对照

[对照探针](probes/V293InterruptQuietSchedProbe.v) 复用现有 typed 物理堆和真实分离所有权，不建立另一套内核模型。

| 检查 | 结论与边界 |
| --- | --- |
| `QSfiltered_nonempty` / `QStyped_pair` | 当前任务为 Ready，入口深度1和255均有实际堆分割，满足真实 builder、quiet 过滤和新增条件 |
| `QSbuilders` / `QSactual_wrapper` | 使用与 enabled dispatch 相同的 `BCintspec`、`BDspec`、`RDinv`、`LDli`，连接同一完整源码包装；不是只验证函数体 |
| `QScommon_environment` | 直接复用已有三函数程序环境的 GoodI、WFFunEnv、WFIFun；不是重新假设或宣称全内核环境已闭合 |
| `QSnegative_nonempty` | 原 Waiting 非最高任务的 quiet 入口仍可满足，但不能满足新增条件。该负例保留原 END None 入口，不冒称两条同规格 C 执行 |
| `QSguard_ablation` / `QSabstract_current_only` | 固定 M、tasks及其他抽象键，仅切换 abstract curtid，新条件由接受变成拒绝；只测试抽象 no-op 决策 |
| `QSprecise_steps` | 原 `sched ;; END None` 到 `END None` 的实际抽象步骤保持同一个抽象状态，不使用任选规格 |

深度255仍遵循已有饱和行为：Enter不再递增，Exit后为254；不能假定始终恢复入口深度。两个深度的完整包装共用一个证明，不把重复实例数当覆盖率。

辅助 Python 枚举仅核对两任务、两种就绪状态的 no-op 决策算术；它不是 Coq 的替代证明，也不证明初始化可达或任意 C 执行。

## 尚未解决的关键缺口

1. **quiet 且当前任务不是最高就绪任务仍未接入此精确规格。** 例如调度锁期间存在更高优先级就绪任务，不能无条件把不调度解释成一次抽象自调度。本步不能移除这个条件。
2. 还需要证明生产可达状态满足所需关联不变量，或设计并验证能准确表达禁止调度状态的统一规格；不能通过任选调度直接放宽验收。
3. 已有 `V293_bound_dynamic_WFIFun` 是特定三函数程序和对应内部规格的环境证明，本步复用了它。它不等于全内核函数环境，也不自动给出无条件 `WFInt`。历史文档中“WFIFun待完成”必须按这一层次理解。
4. enabled dispatch 的强资源/current 条件、一般中断上下文、API/内部规格/初始化的同程序连接、完整 `WFInt`、顶层 `GOOD_OS` 和同程序 K1–K4 仍开放。
5. 非空输入加 Hoare 包装不等于已经构造一条完整具体执行轨迹；不证明初始化可达、终止或任意交错。

下一步应直接研究第1项留下的规格障碍，并向上连接实际生产入口，而非继续增加无关局部模型。

## 验证

| 实测项目 | 结果 |
| --- | --- |
| 最终生产证明及探针 | 各自两次同源稳定 `coqc` 通过 |
| 新增5个生产根、15个探针根 | 20根 `Print Assumptions` 及递归 `coqchk` 通过；依赖仅含既有经典逻辑与函数外延边界 |
| 本步新增测试 | 6/6通过 |
| `make build` | 串行增量构建通过；不是一次全量清洁重建 |
| project audit | 373个活动V293模块及103个框架/战术模块通过 |
| 全库回归 | 2663项，436个失败、1个错误，**全库未通过** |
| 与第298步比较 | 原435个失败的ID和顺序及原1个错误均保留；新增1项旧测试失败，因为它要求 `_CoqProject` 停在旧文件末尾，而本步追加了生产模块 |
| `make audit` | 原函数证据输入身份过期，退出码2；没有重写旧记录制造通过 |
| `git diff --check` | 原 `inferules.v:581–586` 六行空白，退出码2；固定框架未修改 |
| 旧输入与封存证据 | 2584项旧输入只改入口说明、project追加及生成依赖；第298步153项封存记录除上述可变入口外不变 |
| 清理 | 逐项确认后移除6项临时Trust产物、2份已恢复的缓存备份和一次性初稿生成器；两份既有缓存精确恢复，306份既有Python字节码保持原样，无新增字节码 |

本步测试允许后续继续追加生产模块，不再把旧project文件末尾当成永久验收条件。第298步测试与检查点原样保留；其对新project的拒绝另存日志，不倒改冻结证据。

最终结果见 [verification.json](logs/stage299-quiet-sched-bridge/verification.json)。失败编译及其对应源快照全部保留；局部通过与全库历史失败分别报告，不修改旧证据制造全绿。此工作区继续保留，未提交或推送。
