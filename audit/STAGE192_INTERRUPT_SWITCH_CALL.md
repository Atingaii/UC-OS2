# 第192步：OSIntExit 的真实无实参 switch 调用接入

## 本步改变了什么

第191步的完整函数构造器已连接原 `OSIntExit` body，但仍要求调用方证明一条 `scall int_switch nil` 的 Hoare 三元组。本步从框架现有的 `call_rule` 推导该调用；上层稳定接口不再有语句级证明前提，只要求同一 `Spec` 中存在对应的无实参函数契约。

生产文件：`certiucos/v293/proofs/V293OSIntExitSwitchCall.v`（239行）。稳定接口：`V293_OSIntExit_port_lookup_builder_contract`。它仍连接真实 `P f` 查询、`BuildPreI`、`BuildRetI` 和原完整 body；没有添加运行时参数、原语、函数体或新公理。

**调用规则允许按函数规格验证调用方；它不会自动证明被调用函数实现了该规格。** 本步消除的是语句级残余前提，不是生产端口正确性的义务。

## 从源码到证明

1. 重建固定配置及两项授权修复后的源码，重新预处理，逐字节核对 `OSIntExit` 的函数和 body 哈希。原语句仍是 `OSIntCtxSw()`，没有运行时实参。
2. `V293_nullary_call` 使用真实 `call_rule`，其运行时 `vl`／类型列表均为 `nil`，返回类型 `Tvoid`；前后资源须满足 `GoodFunAsrt` 和实际 `CurLINV`，caller frame 须满足 `GoodFrm`。
3. `saved` 地址仅作为逻辑见证，编码为 `logic_val (Vptr address) :: V293_exit_encode x`；逻辑参数不改变 C 函数签名。其余12项动态元数据沿用第191步的有界 roundtrip。
4. switch 前置保留原物理 tail、`Int.add counter Int.one` 和实际 saved 单元。调用方的局部名称与 frame 仍在调用之外，不转交给 callee。
5. 对内部所有 saved block 使用同一个规则；只在 running=1、递减后 nesting=0、lock=0、选择优先级不同于 current 时要求 switch lookup。其他三项 scheduler／enter／exit lookup 与第191步相同。
6. 主定理声明只剩结论中的一次 `InfRules`。`Out`／`Sw` 仍是显式语义 continuation，不能把它们误称为已实现的生产端口。

本步不修改原 AST、C/config、framework、tactics 或旧证明／测试。`_CoqProject` 仅追加新生产模块；根说明只前插摘要，历史正文保留。

## 同一 Spec 与独立物理对照

探针：`audit/probes/V293OSIntExitSwitchCallProbe.v`（243行）。物理堆复用旧的独立字节编码／分离 join 构造，不从待测选择器反向生成堆。

| 证据 | 保持不变 | 结论与边界 |
| --- | --- | --- |
| `SCenabled_different` | 同一个 `SCspec`，任意32位 counter | 完整原 builder 在 nesting=1→0、current=0、selected=12 时通过真实无实参调用规则连通 |
| `SCenabled_same` | 同一个 `SCspec`，任意 counter | current=selected=12，启用调度但不调用 switch |
| `SCdisabled_nested` | 同一个 `SCspec`，任意 counter | nesting=2→1，禁调度分支连通 |
| `SCbuilder_pre_nonempty` | 独立完整物理入口与局部绑定 | 任意 counter／saved 旧值（含 `Vundef`）有入口见证，不从空前置制造证明 |
| `SCswitch_pre_nonempty` | 独立物理 tail 与 saved=1 | 真正拥有 counter+1 和 saved 单元；不是 `Atrue` 资源 |
| `SCcounter_control` | 同一物理堆、任务、saved 地址和其他元数据；两种快照均解码成功 | 只把逻辑 counter 从0改为1，由实际 `Tint32` load 排除错误解释，不靠 decoder 早拒绝 |
| `SCaddress_control` | 同一物理堆、counter=2、saved=1、任务和其他元数据 | 只把逻辑 saved 地址从15号块改为14号 counter 块，由两个实际 load 的冲突排除；两者均是合法指针编码 |
| `SCcounter_frame` | 其余构造参数完全相同 | 独立证明修改 counter 不改变14号块之外的任何字节 |
| `SCreject_runtime_argument`／`SCreject_bad_logical_address` | 同一选择器 | 非空运行时实参、非指针逻辑地址分别拒绝；这两项只是输入层对照 |
| `SCmissing_callee_environment`／`SCno_full_function_environment` | 同一 `BLprogram`／`SCspec` | 203号有规格但无代码，实际 `EqDom` 不成立，因而实际 `WFFunEnv` 不成立 |

`SCspec` 的 switch 前后使用相同的物理资源，仅作为**非生产 identity 契约**验证调用接口。没有证明 `OSIntCtxSw` 的实现，也没有证明切换到另一任务的效果。current=0 的 fixture 仍复用 idle TCB（优先级12）；它不满足完整 current-task/TCB 优先级一致性，不能泛化为生产多任务状态。非空快照也不是运行执行 trace。

## 前瞻协议及保留的错误

协议在实现前保存在本步日志目录；Python 初始测试则在生产模块首轮编译后、探针编写前保存，并非测试先行。原协议第一项有笔误：“空实参及错误逻辑形状拒绝”；实际原 C、冻结 AST 及自始选择的调用规则均要求空运行时实参被接受。`protocol-clarification.json` 单独说明应为“非空实际实参及错误逻辑形状拒绝”，原 `protocol.json` 和其哈希不改。初始测试原样保留，未在见到结果后改门槛。该测试只检查拒绝命题名，不能把勘误中“自始要求”的设计意图当成事前冻结的 Coq 语义测试；无实参接口的直接依据是原 C、原 AST 和最早生产源码快照。

初始结构测试为3通过、2错误（探针／稳定验证材料尚缺），只是缺材料的红灯，不是已经构造了语义反例。语义对照来自上述独立 Coq 命题及其机器检查，而不是 Python 字符串测试。所有19次 Coq 尝试（15次失败、4次成功）的源码快照、完整日志和退出码均保留；没有删除不利结果。

## 验证与已知未通过项

- 稳定编译：`body10`／`probe09`；生产6根、探针18根，共24根逐根 `Print Assumptions`，两入口递归 `coqchk`；保持检查期间601份 Coq 输入不变，假设不超出第191步白名单。
- 新增5项回归；完整测试三轮各2124项（末轮在说明文档定稿后运行），其中旧423失败、1错误及其有序ID原样保留，新增全部通过。它不是全库测试通过。
- `make build` 和项目审计通过；完整审计仍因旧函数证据输入身份过期退出2；`git diff --check` 仍报告旧 `inferules.v` 581–586行空白并退出2，均不靠改门槛隐藏。
- 冻结前核对32637份原有文件，仅允许根摘要、追加项目列表和生成依赖清单变化。缓存恢复原字节；仅清理逐项登记的本步临时信任驱动、备份、一次性生成器及本轮新建的 Python 缓存。具体结果以 `verification.json`、清单及只读复查为准。

## 仍需完成的纵向连接

下一步应将真实函数的逻辑参数／调用任务入口接成统一函数规格，继而建立带实际 callee 代码的局部函数环境；不能把 lookup 或 identity fixture 当成 `WFFunEnv`。还需接入生产临界／抽象切换契约、生产 ISR/LocalInv、初始化及全局环境、全交错模拟和同程序 K1–K4 排除。

规范物理入口仍固定 IE=false，任意初始 IE 的真实保存恢复没有证明。框架允许的抽象中断／任务切换边界可使用，但不能私造原源码没有的端口函数体，具体硬件／ABI 不属于当前源码级目标。

六阶段覆盖保持 `94/1/1/1/1/0`；`GOOD_OS` 未完成，uCOS3 尚未开始，总目标保持 active。本步不提交或推送 Git。
