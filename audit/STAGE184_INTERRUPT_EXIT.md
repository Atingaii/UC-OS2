# 第184步：原 OSIntExit 的真实递减与嵌套／调度锁守卫

## 先看它实际做什么

第183步证明了原 `OSIntEnter` 的入口计数，本步沿固定源码继续 `OSIntExit`。仅在外层 `OSRunning == 1` 时，原函数进入临界区，先有条件递减嵌套计数，再判断递减后的计数与调度锁。计数为0时不减，不能发生0减1回绕到255。

下表描述**运行标志恰好为1且已进入临界区后的片段**；不是完整调用／返回证明。

| 调用前 nest | 递减后 nest | lock=0 时是否进入调度分支 | lock>0 时 |
| --- | --- | --- | --- |
| 0 | 0 | 是；源码没有额外的正计数入口判断 | 不进入 |
| 1 | 0 | 是 | 不进入 |
| 2 | 1 | 否 | 不进入 |
| 255 | 254 | 否 | 不进入 |

一般形式为 `depth(nest)=Nat.pred nest`，调度分支启用当且仅当 `nest<=1 && lock=0`。这只决定是否进入分支，**不保证发生任务切换**：后面还需运行真实 `OS_SchedNew`、读取优先级表、比较优先级，并在不同优先级时调用真实 `OSIntCtxSw`。`run=0`、`run=2` 的外层比较均为假；本步对其有物理字节求值对照，但尚无完整外层函数契约。

## 源码身份与最小实现

在仅应用两类授权补丁的临时源树重放预处理，精确核对 `Source/os_core.c:693–736`，与冻结清单的源码行、预处理偏移、函数定义和函数体哈希一致。源码定义的 SHA-256 为 `eface83f6f4b0aa36685c3996ec8df5d48091ea2ccb2f62918fb03a91f3bd789`。详细输入与完整配置后 C 见 `audit/logs/stage184-interrupt-exit/source-check.json` 和 `OSIntExit.configured.c.txt`。

- `certiucos/v293/code/V293OSIntExit.v`：手工建模完整配置后 AST，保留保存状态的局部变量、整数提升／字节转换、实际空 trace 分支、四个真实调用及 void 返回。没有把 `OSIntCtxSw` 偷换成普通任务切换 primitive，也未提供空 CPU hook。完整 AST 不等于已证明前端翻译正确，更不等于完整函数 Hoare。
- `certiucos/v293/proofs/V293OSIntExitHoare.v`：直接由两个拥有完整写权限的真实字节单元推导表达式求值，应用已有真实赋值规则；不以外部求值 oracle 替代内存读取。
- 稳定接口 `V293_OSIntExit_nesting_dispatch_hoare`：连接实际递减和两个实际 `sif`，只在递减后计数与锁均为0时要求残余 `dispatch` 的 Hoare 证明。这个前提没有被证明，必须由后续真实调度／中断切换资源连接消除。
- `V293_OSIntExit_disabled_hoare`：若旧计数至少为2或锁非0，不需要任何 dispatch 正确性前提，真实片段保持除计数递减外的原资源。不能把不可达调度分支的正确性记为已验证。
- `V293_OSIntExit_nesting_dispatch_semantics`：经框架 `RuleSound` 得到同一片段的 `RuleSem`；仍保留启用分支的残余证明前提，不是全程序 simulation。

## 预注册消融与非空性

协议及其身份在实现前固定，见本步 `protocol.json`、`protocol-identity.json`。

`audit/probes/V293OSIntExitProbe.v` 独立构造 nest、lock、run 三个字节块及一个当前任务指针，空 local domain、`IE=false`、固定 action。`XEnonempty` 证明实际前置资源非空。空 LocalInv 仅为探针 fixture；生产片段接口仍量化 LocalInv，不宣称已有生产 ISR 不变式。

1. 固定 nest/lock，只改 run 为1、0、2：从真实705块读取外层比较，分别真、假、假。
2. 固定 run=1/lock=0，只改 nest 为0、1、2、255：从真实701块读取条件及减法表达式，覆盖不下溢、退出最外层和仍有嵌套。
3. 固定 run=1、实际减后 nest=0，只改 lock 为0、1：从真实702块读取锁守卫，一真一假。
4. 只省去递减时，旧 nest=1 的后续零判断为假；真实减后 nest=0 时为真。这里使用分别构造的前后物理 fixture，**不是具体执行 trace**；赋值与守卫的连接由单独生产 Hoare 推导给出。
5. 同一个物理堆 `XEmemory 1 1 0` 上，正确候选 post（旧 nest=2，减后1）接受；仅把候选 post 的计数改为未递减的2时，由同一实际 `load Tint8` 的值1直接排除。domain、run、lock、IRQ、action 不变，不用早期拒绝冒充后置检查。
6. 三个单因子 frame 定理分别证明改变 run/nest/lock 时，变化块外每个字节的 `get` 都保持；这排除偷偷改变其他物理输入的混杂。

## 验证、失败保留与边界

稳定编译为 code02、body10、probe08；全部失败快照／日志保留。其中 probe05／06 故意输出具体目标诊断 Coq rewrite 的展开形状，不计通过。没有修改旧 C、配置、旧 AST、框架、tactics、旧证明、旧测试或冻结证据。新增5项回归；编译／假设闭包／递归 coqchk／两轮完整测试、旧失败 ID 精确比较及清理结果，以本步 `verification.json` 为准。

实测31个新引理／定理根，两个入口递归 `coqchk` 退出0（约232秒），检查期间585个 Coq 输入哈希未变。实际假设集合为既有允许的 classic、dependent functional extensionality、Eqdep 的 `eq_rect_eq`；其中最后一项出现在经框架 `RuleSound` 得到的语义接口，不能把本步实际假设写成上一轮仅有的两项。逐根对应见 `assumptions-by-root.json`。没有新增公理声明或放宽允许清单。

新增5项回归均通过，`make build` 与 `project-audit` 均退出0。两轮全套均为2083项，实测均为423失败、1错误，全部失败／错误 ID 与2078项基线逐项一致。不能写作全套通过。`make audit` 的旧 stale identity 和 `git diff --check` 的旧 inferules.v:581–586 行尾空白均原样保留。收尾逐文件清理本步临时 trust 驱动与产物，恢复原 lia/nia 缓存；源码、日志、快照和可复用 Coq 产物保留。不提交／推送。

**本步仅闭合真实计数和后续两个守卫的片段接口。** 完整函数的 saved 局部／builder、实际临界区进入退出、启用分支的调度与 `OSIntCtxSw` 证明、ISR 安装与全交错、生产 LocalInv、全局初始化／环境、同程序 K1–K4 及最终 `GOOD_OS` 仍开放。允许的框架任务／中断抽象边界不改变，不开展编译器／ABI／硬件证明。六门保持 `94/1/1/1/1/0`；第一阶段未完成，uCOS3 未开始，总目标 active。下一步优先连接这一个原函数的真实调用资源和完整函数契约，不能把新增文件数量当作整核进展。
