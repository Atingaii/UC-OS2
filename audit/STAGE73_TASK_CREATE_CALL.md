# 第73步：创建函数从真实调用入口到条件成功返回

## 本步解决什么

第72步已证明从 `OSTaskCreateExt` 函数体入口到返回，但入口内存中12个参数/局部对象尚由前提给出。本步把入口前移到**已求值实参的 `sfexec`**：实际执行调用派发、9次参数分配及写入、3次局部对象分配，然后用同一个新内存接入既有函数体与返回证明。不再假设调用者内存里已经存在创建函数的局部对象。

唯一源码目标仍为 uC/OS-II V2.93.01、提交 `0c4a48e6fbc6e915714e816196619a5481accf0c` 加上两类授权修复，配置未改。重新提取94个函数身份，均与冻结清单一致。详见本步 `source-connection.json`、`source-layout.json`、`function-connection.json`。逐项参数/局部声明的源码类型、模型类型、ident和顺序，以及反序实参类型，还由 `declaration-connection.json` 单独核对；这仍是手工映射检查，不是翻译器正确性证明。

## 可复查的证明链

生产代码：
- `certiucos/v293/code/V293OSTaskCreateExtFunction.v`：完整函数record，沿用已有精确body。
- `certiucos/v293/proofs/V293TaskCreateCall.v`：实际分配与纵向连接。

| 环节 | 本步证据 | 边界 |
| --- | --- | --- |
| 函数声明 | 源码9参数：task、p_arg、ptos、prio、id、pbos、stk_size、pext、opt；3局部：psp、err、cpu_sr | 手工前端，不是自动验证翻译器 |
| 进入调用 | `V293_create_call_prologue` | 从已求值实参开始，不含上层C表达式求值 |
| 参数与局部对象 | 真实 `sallocp_step` 9次并store，`salloclv_step` 3次，`sallocend_step` | 显式输入12个互异、相对原内存fresh的块 |
| 局部布局 | `V293_create_function_layout` 从新环境推出 `getaddr` | 不再把完整布局作为独立假设 |
| 函数体与返回 | 稳定接口 `V293_OSTaskCreateExt_success_call_under_hooks` | 三个真实Hook返回契约仍开放，成功且OSRunning=0 |
| 同一最终内存 | 返回0、恢复原caller；创建12对象38字节释放，TCB调用9对象29字节保持已释放 | 幸存块与创建局部块分离仍是显式前提 |
| 保留数据 | 31项发布/全局/caller-frame数据typed读取 | 读取公式复用生产post，非独立post oracle |

局部对象初值为 `Vundef`，不提前假造栈返回、err或CPU_SR。CPU_SR的源码归一化初始化仍由原body执行。task按ADR0007用uint32 selector表示，不宣称函数指针ABI正确；ADR0004/0005保持不变。

## 独立字面内存与控制

`audit/probes/V293TaskCreateCallProbe.v` 独立构造 `CallMemory`，只含全局、TCB和调用者frame，没有创建函数12个局部块；`CallLiteralEntry`、`CallBlocksDistinct`、`CallBlocksFresh` 均实际经Coq检查。`CallConditionalExecution` 从该内存的真实调用入口连接至TCB入口和最终返回；完整成功仍以Hook契约为条件。新环境按实际分配顺序构造，避免把不同map插入树形误作定义相等。

端点负控事先冻结第二轮计划 `control-plan02.json`，保留完全相同证明体，仅分别把返回0改9、最终caller改为callee、释放None改为仍分配。正控成功，三个负控均在证明体内失败，不把语法或缺import当有效负控。首轮缺直接import的失败计划和四份日志保留，不计为成功验证。

独立锚点 `V293TaskCreateCallAnchor.v` 的前瞻协议见 `protocol.json`：只把第一个反序实参opt从合法uint16值改为 `Vnull`；程序、类型序列、其余8实参、caller、初始内存、续体不变。合法值有真实call派发一步，非法值没有 `cstep`。**只授予入口类型派发信用，不能推出后续分配、函数体或Hook已验证。**

## 验证与保留的失败

- 本步生产function、production proof、literal probe、anchor的接受版本分别为 `code01`、`proof10`、`probe05`、`anchor06`；原始快照/成功和失败日志完整保留。
- `proof05` 和 `probe02` 的探索性搜索被显式终止（exit -15）：前者在布局唯一性搜索膨胀，后者在全量内存展开时膨胀。后续分别改为显式Permutation、独立块外读取引理，没有改目标或放宽前提来制造通过。
- 237活动源增量构建通过，复用1175旧产物；**不是cold build**。
- 信任根数量、`Print Assumptions`、`coqchk`实际退出状态以 `trust.json` 为准；只接受既有框架允许的classic/extensionality/eq_rect_eq，不新增Axiom/Admitted等。
- 新增4个测试；完整回归应为1340项、395失败、1错误。与第72步逐一比较，保留原有396条有序失败/错误诊断，不删除或重新分类。最终实际数字见 `final-report.json`。
- 旧C、配置、Coq、framework、tests、evidence及1175旧生产产物按任务前哈希保护；只追加 `_CoqProject` 两源、前置两份索引说明、追加中文教程。前一步manifest本体不改。
- 全部Coq检查结束后精确恢复两项既有缓存。本轮scratch、源码临时提取目录和probe构建产物逐项确认/统一复核后清理；保留生产可复用产物、所有证据和probe源。清单及结果见 `cleanup-inventory.json`、`cleanup.json`。

## 尚未完成与下一步

这是**存在一条不交错的局部执行轨迹**，不是 `local_hoare`、所有执行safety或源码级 `GOOD_OS`。未实现 `OSTaskStkInit`、`OSTCBInitHook`、`OSTaskCreateHook`、`OSInitHookBegin`、`OSInitHookEnd`；没有伪造这些调用为noop。三项Hook契约尚未兑现，完整成功实例不能被描述为固定缺Hook程序已经运行成功。

下一步应处理真实端口义务和调用环境/幸存块分离的上层实例，之后连接实际调度与OSInit七调用同一连续内存；错误清理路径及其他功能族仍待闭合。六门仍 `94/1/1/1/1/0`，同程序K1–K4未完成，uCOS3未开始。总目标active，本步未提交或推送。
