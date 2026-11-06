# 第224步：精确局部资源贯穿真实 Enter 与 EOI 前缀

## 从返回规则的实际要求出发

上一检查点已把 Enter 接入原动态三函数环境，但 Enter 契约中的 `CurLINV` 允许额外资源隐藏在 `Atrue` 中。原 ISR 返回规则需要的是精确的 `p_local`，不能从较弱后置直接反推出它。本步从原 Enter 的低层更新证明重新连接完整本体、真实 builders 和调用，始终保留精确局部资源。不修改 C、配置、AST、框架、tactics、旧证明或历史失败证据。

生产接口：`certiucos/v293/proofs/V293InterruptReadyLocal.v`。
实例和单因素对照：`audit/probes/V293InterruptReadyLocalProbe.v`。
前瞻协议、原始编译、逐根信任与回归证据：`audit/logs/stage224-interrupt-ready-local/`。

## 已闭合的证明链

| 接口 | 内容 |
| --- | --- |
| `V293_local_witness_identity` | 选定 `V293_shared_li` 恒为 `Aemp`，所以任意逻辑见证的 `p_local` 与空见证定义相等；不推广到任意 LocalInv |
| `V293_enter_local_extract` / `close` | 在原 ready/TCB/storage Inv 中打开并重新关闭 running/nesting 字节，精确 `p_local` 和两栈始终保留 |
| `V293_OSIntEnter_local_updates` / `body` | 从原低层更新证明连接完整 Enter 本体与真实 return，无现成 callee InfRules 前提 |
| `V293_OSIntEnter_local_contract` | 实际 BuildPreI/BuildRetI 接入完整本体；返回值仍要求 `result=None` |
| `V293_OSIntEnter_local_call` | 原 call_rule 给出精确入口到同一精确出口的真实调用 |
| `V293_irq_local_enter_pre` / `post` | 原 EOI 后 closed 边界（加真实全局名称）与精确 Enter 边界（加空局部域）双向转换 |
| `V293_irq_local_return_resources` | 调用后精确边界可恢复 `iretasrt' ** p_local`，同时保留零 footprint 全局名称绑定；这是资源蕴含，不是整段 ISR 执行 |
| `V293_irq_local_eoi_enter` | 原 BuildintPre、真实 eoi_ieoff_rule 和实际 scall 连成 EOI→Enter 两语句前缀 |
| `V293_ready_local_WFFunEnv` / `WFIFun` | 保持原三函数程序、同一动态 Inv、原 Exit/SchedNew 契约，只替换 Enter 条目，检查三个完整本体 |

没有为此引入新 codec：直接复用原上下文实参编解码。初稿重复的单函数规格和环境未用于联合路径，已移除；保留的最小路径直接进入原三函数环境。OS 两栈在函数契约内，不作为 GoodFrm 帧偷渡。

## 非空入口：明确是数学子堆

`RLentry_nonempty` 从已有真实 typed TCB、完整 lookup、就绪位图和控制存储实例 `REheap` 分离出精确资源子堆，并保留：

- 物理 join 回原 `JBmemory` 的见证；
- 抽象资源 join 回原 `RIabstract` 的见证；
- 子堆满足精确 Enter 边界及空局部域。

这是分离逻辑的数学资源分解，不是运行时删除内存，也没有削弱同一 Inv。它不声称整个原扩展状态满足精确边界，不证明从 OSInit 可达，也不声称旧 changed Exit 入口由本次 Enter 执行产生。`RLbuilder` 精确计算真实构造器；`RLenvironment` 使用原 RDprogram、RDinv 并给出 GoodI/WFFunEnv/WFIFun，实际 call 和前缀也使用同一实例。

## 单因素局部断言对照及其边界

固定同一 `REstate`、线程、LocalInv，只将局部断言的精确 `p_local` 换成 `CurLINV`：

- `REstate` 满足较弱 CurLINV；
- 同一状态不满足精确 p_local：后者的抽象 footprint 必须为空，而该状态含非空 curtid 抽象资源。

这是两种**局部断言**不能随意反向转换的反例。它不是完整旧 boundary 蕴含新 boundary 的反例（完整边界还有 Inv 的资源分堆），不是两次完整函数执行，也不是生产 LocalInv 必要性的实验。两边复用同一 codec，不以解码早拒绝代替下游证据。本体、builders、真实调用与前缀正确性由各自 Coq 定理证明。

## 对抗式复核

1. Inv 是否偷换？实例直接使用原 RDinv，生产环境用已有定义相等布局定理；没有删除 ready、TCB 或 storage 因子。
2. 是否从弱 CurLINV 逆推精确资源？没有。精确资源从提取到完整本体出口一直保留；较弱断言仅用于框架调用的必要侧条件。
3. 是否循环假定 callee 正确？三个 WFFunEnv 分支分别使用完整本体契约；真实调用只使用框架 call_rule 的规格入口。
4. 是否把见证独立性泛化？只对恒 Aemp 的选定 shared_li 成立；尚未证明生产 ISR LocalInv。
5. 是否用非空代替可达？保留原堆 join 来源，只称数学子堆满足性。
6. 是否省略 Exit、抽象操作或 iret 却称完整 ISR？没有。前缀只有 EOI 与 Enter；资源恢复蕴含也不执行 Exit/iret。
7. 是否通过删失败制造全绿？保留所有失败编译快照、423 项历史失败与1错误，比较旧失败/错误 ID 及顺序；既有 audit/whitespace 失败不改。

## 核验、限制与下一步

实测：30 个证明根的假设检查、668 个 Coq 输入身份核对、两个入口递归 coqchk、两次构建和新5项结构回归通过。全量2284项仍423失败、1错误，旧失败与错误 ID 和顺序保持。详细命令退出码以 `verification.json` 为准。逐根 Print Assumptions、两个入口的递归 coqchk、两次构建、新5项结构回归和全量回归保留日志。Python 结构测试在语义证明之后编写，不声称语义 TDD；对抗复核是同一执行者复核，不冒充独立审阅。

本步修复的是具体布局无法自动反推 prefix/suffix 的证明实例化，以及 EOI 界限的末尾策略；失败快照保留，最终使用显式布局参数和准确的整数界限证明，不修改定理条件。

**仍未连续连接含 Exit/调度的完整原 ISR。** 当前只处理 incoming 全clear、原 IE=false 的入口边界；生产 ISR 抽象规格、嵌套闭包、控制值与 lookup 语义、完整生产数据 Inv、API/初始化、WFInt、GOOD_OS 和同程序 K1–K4 仍开放。不能把 Enter 段精确资源闭合称为整个 ISR 已闭合。

下一步应把同一联合环境下的 Exit 调用接进原 ISR 中间段，检查 abstract action 与返回边界之间的真实控制语义；任何不匹配先记录为待证义务，不削弱规格规避。

六门仍 `94/1/1/1/1/0`，总目标 active，uCOS3 未开始，未提交或推送。逐一清点后只删除本步一次性信任驱动及其产物，原缓存按字节恢复；源码、失败证据、可复用 Coq 产品保留。
