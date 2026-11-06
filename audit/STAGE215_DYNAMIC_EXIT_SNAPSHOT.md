# 第215步：退出契约中的可变状态改为动态逻辑快照

## 为什么继续改

第214步已经让 quiet/same/changed 在同一调度 lookup、同一 storage Inv 下成立，但 changed 的计数器、嵌套层数、就绪输入和任务表等仍是规格的模块参数。改变一次计数器就可能需要另一份规格，不能直接用来描述运行中的多次调用。

本步只改变逻辑实参，不改变固定 C、配置、AST、运行时函数、框架、已有证明和源码级切换边界。`OSIntExit/OSIntEnter/OS_SchedNew` 三函数环境不再固定 changed 的这些运行值。

## 新接口及其依据

- `V293_changed_snapshot` 保存 lo/hi/current/nest、指针表内容、抽象任务/事件表、时间、high/target 值、counter、抽象操作及临界现场。`V293_changed_encode/decode` 有逐记录 roundtrip 和单射证明。
- 字节快照使用 `int32` 表示。codec 只识别结构；旧前置的纯有效性断言继续约束字节范围等语义条件，不用过早拒绝冒充执行证明。
- 地址、类型、指针表**长度**和其余布局仍静态；表的内容进入快照。`V293_dynamic_exit_inv_length` 证明旧 Inv 只依赖表长度。前置显式携带长度等式，提取后才改写 Inv，不假设所有表具有相同布局。
- `V293_OSIntExit_dynamic_builder_contract` 对任意真实 `BuildPreI/BuildRetI` 及逻辑实参证明完整归一化本体，内部复用旧路径证明和第214步精确规格嵌入。没有“整个退出本体已正确”的外部 Hoare 前提。
- `V293_dynamic_exit_env_WFFunEnv/WFIFun` 使用一个动态规格、一个调度 lookup、同一 `V293_scheduler/V293_shared_li/Inv` 直接闭合三函数环境。quiet/same 仍使用其原有动态逻辑实参。

新接口的后置复用已证明的恢复契约：共享存储值在原线程恢复时存在化，而不是把切换前快照冻结到恢复后。Inv 的物理布局保持相同；逻辑参数中的任务/操作等关系仍受旧契约约束。

## 实际字节正控与单因素对照

`DPenvironment/DPbuilders/DPactual_contract` 实例化同一个具体程序与规格。`DPchanged_nonempty` 从独立字节内存接入新入口，对 nest=0/1 及任意 counter 成立；不是假设前置非空。

`DPcounter_dynamic_control` 保持最大 counter 的物理状态、其他逻辑字段和程序不变：

1. counter=`1` 和最大 UINT32 的两个快照均正确编解码；两者各自匹配的实际内存入口均非空。
2. 最大 counter 的状态满足动态匹配快照，却不满足仅把 counter 冻结为 `1` 的前置。
3. 负控由 `DPcounter_load` 对实际拥有的 block 12 内存读取推出矛盾；两侧 codec 都合法，故不是编码提前拒绝。

该对照只证明入口资源能区分过期快照，**不声称两个完整变体执行**，也不由此推断所有动态字段均有独立的具体差分执行。通用契约量化所有快照，但额外具体非空见证主要改变 counter/nest。

`DQquiet_nonempty/DQsame_nonempty` 也接入新入口，但沿用另一套物理地址夹具。不声称三条具体正控来自同一个地址实例或同一个初始化状态。

## 验证与边界

证据目录：`audit/logs/stage215-dynamic-exit-snapshot/`。事前协议先于实现记录；全部失败编译快照保留。新增 Python 测试仅为结构回归，语义结果来自实际 Coq 编译、逐根假设和递归 `coqchk`。实测结果以 `verification.json` 为准。

changed 仍限原 IE=false、ISR 全清和旧契约的完整所有权/有效性条件；本步没有扩展到任意中断现场。生产数据所有权如何从 Inv 获取、生产任务/ISR 不变量、`WFInt`、初始化、最终 `GOOD_OS` 与同程序 K1–K4 仍开放。接受的 OSIntCtxSw 归一化仍按 ADR-0010，不是硬件、ABI 或原外部调用 refinement 证明。

六门覆盖仍为 94/1/1/1/1/0。uCOS3 尚未启动；总体目标保持 active，未提交或推送。下一步应优先连接生产中断不变量和资源获取，而不是把本步局部环境误计作整核验证。
