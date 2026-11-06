# 第195步：OSIntExit 的实际函数入口、分配与返回

## 本步消除什么义务

第194步从“callee 局部变量已经分配”的函数体入口出发。本步只消除这段入口断点，不另建调度模型：

`scall → sfexec → salloclv → sallocend → 第194步完整 body → void return/free → caller`

生产入口为 `certiucos/v293/proofs/V293OSIntExitCallExecution.v` 中的单个接口 `V293_OSIntExit_nested_call_execution`。保持原 void/无参数/一个 Tint32 saved 局部变量的函数形状，body 使用 ADR-0005 已明确接受的临界原语抽象。不修改 C、配置、原 AST、框架或旧证明。

主接口仅要求本函数的真实 program lookup、标识符不遮蔽约束、全局 running/nesting 绑定、物理读取以及 nesting 单元的写权限。新鲜块存在性、两次 store、callee local NoDup/writable、call continuation 和实际释放均在证明内部构造，不作为调用方执行 oracle。

## 可观察的结果

当 running=1 且 2≤nest<256：

- 从真实无参数调用开始，分配一个全新的 saved 块，不能借用 caller 的同名局部变量。
- 实际执行 saved:=0、嵌套计数递减、encrit/excrit 和返回释放。
- 最终从物理内存读取 nest-1、running=1；新局部块的4个字节均不存在。
- 恢复原 caller 环境、任意初始 IE、中断状态和既有临界栈尾。
- 除 fresh 块和 nesting 块之外，各块字节保持；这不是“最终全堆精确等于原堆只更新一个字节”的定理。

这里的“恢复 caller”首先指环境恢复。若 caller 自身某个地址别名 nesting，不能宣称那个字节也不变。独立见证采用不同物理块，另证 caller 字节保持。

## 前瞻验证与消融

协议在新 .v 创建前冻结于 `audit/logs/stage195-interrupt-call-execution/protocol.json`。

| 因子 | 真实控制 | 能说明什么／不能说明什么 |
| --- | --- | --- |
| 正常调用 | 非空 program 只有 OSIntExit 定义，其他 callee 均 None，完整执行 | 嵌套路径不依赖调度 callee；不是完整生产函数环境 |
| caller 遮蔽 | caller 同名 saved 为 Tint8；caller running=0，而 global running=1 | sfexec 使用新 callee 环境，返回恢复旧环境；两个 caller 块字节独立保持 |
| 删除函数定义 | 同一唯一函数删除后，实际 sfexec 无下一步 | 只验证入口 lookup，不能冒充后续执行证据 |
| 多一个实参 | 相同 program，给 sfexec 增加一个有类型的运行实参 | 实际 dnil 签名／tlmatch 拒绝，不只是 builder 拒绝 |
| 分配／释放 | fresh 从任意输入堆的存在性构造，末尾4字节实际释放 | 不借用旧 caller saved；块外 frame 另证 |

独立 `CLnested_call_witness` 对所有 2≤n<256 非空，并对2→1和255→254各有实际调用推论。入口负控只授权入口结论，后续分配、写入、栈恢复和释放均由独立完整正控证明。未声称从局部 trace 推出任意中断交错。

## 检查与信任边界

稳定编译为 body06／probe01，所有失败尝试保留；不是测试先行开发的声明。9个 Lemma/Theorem/Corollary 根逐个 Print Assumptions，并对两入口递归 coqchk；假设不得超出已有允许集合，不能把结构 Python 测试当 Coq 语义证明。

本步新增5项回归；两轮全量测试实测均为2139项，旧423失败和1错误及其有序标识保持。最终实测以同目录 `verification.json` 为准。`make build` 与项目边界审计均成功，`make audit` 的旧证据身份失败及既有 inferules 空白失败不伪装为通过。源码由锁定版本重新物化、预处理、逐函数哈希比对，两次结果必须一致。

**仍未证明**：原始端口调用到原语的语义保持、n=1→0调度／真实 OSIntCtxSw、生产 ISR/LocalInv、全环境／初始化、全局模拟、同一程序 K1–K4 和最终 GOOD_OS。六门保持94/1/1/1/1/0，uCOS3未启动，总目标 active。本步不提交／推送 Git。

清理只限本任务新建的一次性 Trust 驱动／产物及缓存备份，先登记后删；原算术缓存恢复，源码、可复用产物、全部成功与失败证据及旧文件保留。冻结清单时不重定向输出到仍打开且被纳入清单的日志，避免重演第194步已记录的封存失败。

## 下一步

先补 n=1→0 的调度路径与可执行 callee，再连接生产资源、初始化和框架模拟；不能把“可调用的嵌套分支”重命名成整核验证。只有 uCOS2 最终源码级 GOOD_OS 与同程序 K1–K4 完成后，才按老师附件进入 uCOS3。
