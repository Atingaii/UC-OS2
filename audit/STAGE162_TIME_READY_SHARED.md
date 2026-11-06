# 第162步：同一共享不变量中的时钟借还与就绪资源

## 本步解决什么

第161步的后 hook 后缀已经有正式 Hoare 规则，但调用者仍须额外拥有原始字段，IRQ invariant 只是任意原样 frame。本步只推进其中的时钟入口：将物理时钟与已有 TCB／ready／优先级表关系放进同一个共享不变量，从该不变量实际借出时钟、更新、归还。固定 V2.93.01 C、配置、AST、框架、旧证明及旧证据不变。

生产文件：`certiucos/v293/proofs/V293TimeReadyShared.v`。
独立字节探针：`audit/probes/V293TimeReadySharedProbe.v`。
前瞻协议及原始失败记录：`audit/logs/stage162-time-ready-shared/`。

## 为什么不是把两个旧不变量直接相乘

旧 time core 与 ready core 都拥有抽象 task／event／time／current slots 和 current 指针。直接用分离合取拼接会重复拥有同一抽象槽，可能根本没有满足者。

新 `V293_time_ready_fields n` 只量化一组 `t / ts / es`，其中 `V293_shared_fields t ts es n` 与物理 `V293_ready_payload ... ts` 共享同一个 `ts`；再与物理 clock 单元合并，绑定同一个 `n`。精确性、ISR context 不变性、IRQ 开闭、切换开闭和 current store 均有证明。`GoodI` 的参数仍是旧见证用 `V293_shared_li`，没有因此得到生产 LocalInv 安装。

## 正式接口及其边界

- `V293_tick_ready_clock_prefix`：闭合 `encrit ; (clock++ ; excrit)` 的正式 `InfRules`，没有 continuation 或执行成功前提。调用前只有 action、OS 状态、全局地址绑定及 caller frame，没有另持物理 clock；中间实际应用 encrit 规则取得共享 core，原赋值规则写物理时钟，再由既有合法抽象动作同步 abstract time，应用 excrit 规则归还更新后的同一 core。
- `V293_tick_ready_clock_with_tail`：保留原后缀 AST 的右结合，接入**另行证明**的 continuation。其前提显式保留 tail 的 `InfRules`，不是已经证明完整后缀。闭合 prefix 的不同 AST 不代替此连接义务。
- `V293_tick_ready_clock_write / close`：保持同一个 TCB／ready／table payload；不新增 abstract action，不用运行结果倒推 Hoare。
- `V293_tick_ready_clock_semantics`：只经原 `RuleSound` 正向导出带 continuation 的 `RuleSem`。
- `V293_time_ready_clock_agreement`：从拥有的 core 推出物理 load 与抽象 time 相同，不把一致性另当前提。

本次借还规则只覆盖 `IE=true` 且所有 ISR flags 为 false、合法栈顶及良好 frame／LocalInv entailment 的入口。**不是实际 tick ISR 入口**；不能用于绕过处理中 ISR 对资源的占用。关闭 IE 的入口需要调用者已拥有资源，本步没有把它冒充同一个借出定理。

## 非空实例与单因素负控

`TRliteral_spatial` 用独立编码字节与真实分离 join 构造新 `SWINVt`：两个非空任务（priority 4 ready、priority 6 semaphore wait）、current、TCB 字段、ready 两行与 group、13-slot 优先级表以及独立 block 150 的32位 clock。抽象时间重定值仅用于构造 fixture，**不是初始化可达性或执行定理**。该 fixture 验证共享不变量可满足，不声称已提供新 Hoare 规则全部 caller bindings 的一次字面运行。该局部不变量还没有 event 对象／等待队列耦合：夹具的 event map 为空，即使包含 semaphore-wait 任务也可满足它，因此不能把这个实例当成整核有效初态。

| 对照 | 唯一变化／保持不变 | 检查结果的含义 |
| --- | --- | --- |
| `TRclock_ablation` | 保持 abstract time、整个非 clock 地址空间及 ready loads；仅 clock block 换值 | 旧 abstract time 与新物理 clock 不能满足同一新不变量 |
| `TRincrement_ablation_cases` | 固定旧 abstract time，分别检查物理 0→1、0xffffffff→0 | 覆盖普通增量和32位回绕的“未同步 abstract time”反例 |
| `TRready_ablation` | 对同一好入口实际 store 一个 ready byte 16→32；所有其他地址及物理 clock 不变 | 新不变量拒绝真实 task map 仍有 priority 4 ready、但 bitmap 不再含4的状态 |

ready 负控前后 bitmap 都非空、group 都为1；变化后 priority 5 的位仍为真。因此拒绝不只是较早的非空／group 一致性失败，而由 task-map membership 矛盾导出。clock 负控是构造状态对照，不声称执行了“删除 abstract action 的 AST”；ready 负控是一次实际 memory store，仍不是完整 tick 执行。

## 实测验收

- 生产稳定编译 `ready14`、探针稳定编译 `probe10` 均 Coq 退出0；24次编译快照（含17次失败）及原始日志全部保留，不删不利记录。
- 41个新增 lemma／theorem 根逐一 `Print Assumptions`；332个活动模块与52个独立探针模块通过独立 `coqchk`，退出0，耗时873.105286秒。
- 检查期间539份Coq输入不变；实际假设仍为既有 `classic`、`functional_extensionality_dep` 和 `Eqdep`，允许集合未扩大。
- 新增7项Python回归全部通过；三轮全套均1965项、423失败／1错误，完整失败与错误ID集合均与第161步一致，不把既有失败报告成通过。
- 构建及清理后重建退出0。`make audit` 仍退出2：project audit通过，coverage audit仍为旧 `stale function evidence input identity`；`git diff --check` 仍仅报告旧 `framework/logic/inferules.v:581–586` 六行尾空白，退出2。
- 逐一确认8项一次性目标后清理673392字节，恢复两份既有缓存；新源、失败证据及可复用Coq产品保留。26766份旧文件仅README、状态、项目入口及生成依赖有预期差异。
- 机器可读验收见 `audit/logs/stage162-time-ready-shared/verification.json`，冻结证据见同目录 `checkpoint-evidence-manifest.json`。

## 仍然开放

完整 tick 函数/API/ISR、CPU hook、task 更新后的共享 core 重建、生产 LocalInv／Inv 安装、初始化与 WFIFun、源码级 GOOD_OS 和同程序 K1–K4 均未闭合。旧六门仍为 `94/1/1/1/1/0`，本步不增加整函数覆盖信用。第一阶段未完成，uCOS3 未开始；总目标仍 active，不提交／推送。

下一步将原 while 的字段更新与这个**同一任务表**中的 TCB／ready 关系连接，再处理实际 ISR 资源转移；不能把开中断 clock prefix 当成完整中断处理函数。
