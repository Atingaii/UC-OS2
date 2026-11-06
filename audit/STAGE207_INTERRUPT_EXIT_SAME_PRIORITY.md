# 第207步：中断退出同优先级路径的完整归一化本体

## 前因与本步结果

第205步闭合了不调度的退出路径；第206步能在临界区内实际调用 `OS_SchedNew`，保留 ISR 现场、两栈及已经取得的 ISR 不变量，但只有退出中段。本步把它接回 `saved=0`、运行状态检查、真实临界规则和 `return None`，得到完整同优先级**归一化本体**的单个 `InfRules` 定理。

新增生产文件：`certiucos/v293/proofs/V293OSIntExitSamePriority.v`。
主定理：`V293_OSIntExit_same_priority_body`。
它不假设整个中段或 callee 的 Hoare 证明；仍要求 Spec 中存在第206步已经证明过的增强调度契约。**这不是全部真实函数 builder、全程序环境或 `GOOD_OS`。**

## 沿着代码看证明

前置中调用者拥有普通全局数据、就绪表、任务表、缓存与计数器，以及已经分配好的 saved 局部单元。运行状态为1，nesting 初值为0或1，lock为0，就绪选择结果等于当前缓存优先级。

1. 把 saved 原值改成0。
2. 从真实 running 单元求值，进入运行分支。
3. 原 IE=true：`encrit1_rule` 关中断，把 true 压入临界栈，取得 `invlth_isr I 0 (gettopis si)`；原 IE=false：`encrit2_rule` 压入 false，不额外取得该资源。
4. nesting 条件递减至0，nesting/lock 两个 guard 为真。
5. 经第206步定理实际调用调度器，计算最高就绪优先级，从表中读取并写入最高就绪任务指针。
6. 最高优先级等于当前缓存，因此不同优先级 handoff 不执行，counter 不变。
7. 分别使用 `excrit1_rule` / `excrit2_rule`，恢复原 IE 和临界栈。true 分支归还取得的不变量；ISR 位图和 ISR 栈保留。
8. 返回 `None`，保留普通数据的后置关系及 saved=0。

`V293_exit_same_core/data/result` 只包含普通资源，证明它们满足 `GoodFrm`。ISR、两栈和已取得的不变量继续放在动态 callee 契约内，**没有把它们强称为 GoodFrm**。本步资源所属 I 与规则环境 I 相同，不能借第206步更一般的双 I 接口夸大本步边界。

## 具体非空见证与有界对照

探针：`audit/probes/V293OSIntExitSamePriorityProbe.v`。

- `QPdata_owned` 从已有独立字节内存构造的 `RCbig_owned` 逐项重组资源，不假设目标断言。初始最高优先级单元使用存在量词 hv，而不是宣称从旧物理前置取得了固定初值0。
- `QPpre_nonempty` 把同一份普通内存转移到任意原 IE 和两栈；转移依据是已经证明的 `GoodFrm`，不是修改数据或忽略 OS 现场。
- `QPbody` 实例化完整归一化本体；bitmap=(0,16)，最高/当前优先级12，running=1，lock=0，nesting≤1。
- `QPboth_ie_and_nonempty_stacks` 明确给出原 IE 两值、ISR 栈 `0::nil`、临界栈 `false::nil`、nesting=1、counter=1、saved 原值1的具体前置非空见证。
- `QPzero` 是实际 saved 赋值的 Hoare；`QPsaved_read` 提取局部单元实际读取值；`QPwithout_zero` 在同一内存和 OS 现场下，由 saved 读取仍为1排除 saved=0 的边界断言。

最后一项只隔离 saved 初始化这一因素，**不是两份完整函数变体的执行消融**，也不证明删除初始化后任意下游机制都会失效。非空见证的 ISR 位图全清、LocalInv 为测试实例；没有构造生产 Inv 提供数据、取得不变量后的独立非空状态或启动可达性。

## 实测与证据边界

证据目录：`audit/logs/stage207-interrupt-exit-same-priority/`。

- 事前 `protocol.json` 固定本步主张、保持不变项及有界控制。保留每次编译的源码快照与日志，失败和中断也保留，不计为通过。
- 初期 probe03、probe05、probe06 在通用分离逻辑搜索耗时后被终止；最终改为明确消去纯现场事实、按资源重排，未删去内存义务或改变生产断言。最终成功版本以 `stable-compiles.json` 为准。
- 从固定配置重新构造 OSIntEnter、OSIntExit、OS_SchedNew 的修复源码文本，并复核源码、配置、AST 身份。没有改动旧 C、框架、旧证明和旧测试。
- 逐根 `Print Assumptions`，对两个新模块递归 `coqchk`，检查期间全部 Coq 输入身份不变；不扩大第206步的允许假设集。
- 新增5项结构回归，不冒充语义测试先行。完整回归逐项保留旧失败/错误及其顺序；旧 audit 和空白检查失败不被改写成通过。
- 最终实测数字、前一冻结证据检查、清理清单、原缓存恢复，以 `verification.json` 为准。未提交或推送。

## 距离最终目标还差什么

1. saved 目前是已分配局部单元；未把新增强契约接入所有真实 `BuildPreI/BuildRetI`，也未证明局部分配/释放执行。
2. 不同优先级 handoff、完整退出路径的统一规格仍开放。
3. 调度器增强 Spec 尚未与原三函数共同 `WFFunEnv/WFIFun` 统一，不能复用旧 plain Spec 环境冒充闭合。
4. 普通全局单元由调用者拥有；从生产 Inv 取得这些数据、生产 ISR/LocalInv/WFInt、完整初始化仍未完成。
5. 本体沿用既定归一化边界，不是端口/汇编精化证明。源码级 `GOOD_OS`、同程序 K1–K4 未完成，uCOS3 未启动；六门仍为 `94/1/1/1/1/0`，总目标保持 active。

下一步优先把已有非调度与同优先级本体接到真实退出 builders，统一增强 scheduler Spec 和三函数环境，再处理不同任务 handoff。不能用局部定理数量替代整核完成证据。
