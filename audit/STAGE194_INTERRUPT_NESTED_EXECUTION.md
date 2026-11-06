# 第194步：OSIntExit 嵌套路径的实际连续执行

## 这一步解决什么

第193步建立的是原始 `OSIntExit` 的统一、带 callee 契约的内部 Hoare 规格；规格查找成功不等于对应函数真的执行了。本步补上一个明确较小的执行闭环：**已经分配局部变量、OSRunning=1、入口嵌套计数在2至255之间**时，实际执行初始化、递减、退出临界区以及返回释放。

活动工程仍只针对固定的 uC/OS-II V2.93.01 和既定配置。C、配置、原始 AST、框架、tactics、既有证明、测试与冻结证据没有修改。六门仍为 `94/1/1/1/1/0`，没有把本步局部结果登记为整函数或整核通过。

## 必须区分的两个程序

- 原始配置后函数通过 `V293_EnterCritical(&cpu_sr)` 和 `V293_ExitCritical(&cpu_sr)` 调用端口；分析端口只有声明，没有可执行实现。
- 本步沿用 ADR-0005 的**显式抽象程序**：严格匹配这两个调用的形状后，分别替换成框架已有的 `encrit`、`excrit`。`V293_OSIntExit_abstract_normalization` 证明的是 AST 归一化等式，不是原始端口调用与该程序的语义保持定理。CPU_SR 字节级保存被擦除；IE 的保存恢复由框架临界栈承载。

不能用后者的执行结果声称前者的端口实现已经存在，也没有新加“永远正确”的调用公理。

## 主接口与真实执行内容

文件：`certiucos/v293/proofs/V293OSIntExitExecution.v`。
稳定接口：`V293_OSIntExit_nested_execution`。

| 顺序 | 真正执行的步骤 | 结论／边界 |
| --- | --- | --- |
| 入口 | 已有 saved 的局部绑定与可写字节 | **不包含函数入口的局部分配** |
| 1 | 32位物理写入 saved:=0 | 不要求 saved 的旧值是 IE 编码 |
| 2 | 读取 OSRunning==1 | 实际读内存，不用纯逻辑标签代替 |
| 3 | encrit | IE=false，原 IE 压入临界栈 |
| 4 | 读取并物理写回 OSIntNesting-1 | 2→1；255→254；一般覆盖2≤n<256 |
| 5 | 再读更新后的嵌套计数 | 仍不为0，不访问 lock、调度器或 switch |
| 6 | excrit | 任意初始 IE 恢复，既有临界栈尾不变 |
| 7 | void return、实际 free | 每个局部字节被释放，调用者环境／continuation 恢复 |

定理没有以整个语句或 callee 的正确性为前提。两个 store 前提是具体的内存操作；见证另从可写字节构造这两个操作，排除“前提不可满足所以证明成立”。块外字节保持由独立 frame 结论表达。

## 非空见证与单因素消融

文件：`audit/probes/V293OSIntExitExecutionProbe.v`。

- `NEnested_witness`：独立物理内存含 running=1、任意2至255的 nesting、saved旧值23；构造两个真实 store，再执行**完整抽象 body 到释放返回**。对任意初始 IE、is/cs 尾量化，最终 nesting=n-1、running仍为1、saved的4个字节均释放，其他块保持。`NEnest2`、`NEnest255` 分别固定两个边界。
- 该 fixture 的 `NEprogram` 对所有 callee 均返回 None，证明这条路径确实不需要调度／切换 callee；但执行从已经分配的 body 开始，**这个空 program 不是合法生产函数环境，也不证明 sfexec 入口**。
- `NEcritical_pair_witness`：从相同非空物理输入、相同 continuation，实际执行临界**中段**的两个版本；唯一差异是 excrit 替换为 skip。两者均写入同一 nesting=1；正常版本恢复 `(enabled,si,ci)`，删除版本留下 `(false,si,enabled::ci)`，并证明二者不同。初始 IE=false 时也因栈多一项而不同。
- `NEnest_changed`：实际递减 store 后，读取不能仍等于入口计数。

**消融范围修正**：冻结协议里的“同一入口／返回前”在本轮只落实到独立临界中段边界；中段挂有同一待执行 return continuation，但未证明变体从完整函数入口到该边界的前缀，也未执行变体的 return。这是比原协议更窄的结果，见 `protocol-clarification.json`。保留原协议，不事后改写成“完全满足”。正常完整 body 的返回执行由另一根定理单独验证，不能移植给变体。

## 验证与旧失败

本步日志目录：`audit/logs/stage194-interrupt-nested-execution/`。

- 稳定编译为 `body09`、`probe07`；包括失败尝试在内，每次保留源码快照、日志及退出码，编译期间源码必须不变。
- 14个公开 Lemma/Theorem/Corollary 逐根 `Print Assumptions`；两个新模块及递归依赖由 `coqchk` 独立检查。精确结果、依赖和允许的既有假设见 `trust.json`，不把这些检查外推为全部生产环境。
- 新增5项结构回归；它们不能替代 Coq 语义证明，也不声称本步遵循语义级 red-green TDD。
- 全量测试、构建、项目审计和旧失败的有序ID比较以 `verification.json` 为准。旧测试423失败、1错误及旧审计问题没有通过删测或改门槛隐藏。
- README 与状态文件只前插，本项目清单只追加；基线逐文件 SHA 检查保护既有文件。一次性信任驱动与产物在逐项登记后清理，原有算术缓存恢复原字节；保留可复用 Coq 产物和全部证据。

## 尚未完成与下一步

本步不是任意交错执行、生产 ISR/LocalInv、原端口语义保持，也不是 n=1→0 的调度分支。尚未闭合真实函数入口局部分配、完整 WFFunEnv、初始化、上下文切换、抽象模拟、同程序 K1–K4 与 GOOD_OS。

下一步优先接通同一抽象 body 的实际函数入口分配，将“局部变量已经分配”从调用方前提移到连续执行链中；随后再把此局部执行接回生产环境及不变量，而不是继续把条件规格计为整核证明。uCOS3 仍须在第一阶段完整结束后开展，总目标保持 active。
