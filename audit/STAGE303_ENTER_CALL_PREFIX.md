# 第303步：完整 Enter 调用连接实际中断入口

## 本轮推进了什么

固定对象仍为 uC/OS-II V2.93.01、上游提交 `0c4a48e6fbc6e915714e816196619a5481accf0c`。重新核对 `os_core.c:663–671` 的 `OSIntEnter`，沿用已有固定配置 AST，未改 C、配置、框架或既有证明。源码与相关输入哈希见 `audit/logs/stage303-enter-call-prefix/source-identity.json`。

上一步仅执行 `updates` 语句。本步把它包入真正的 `scall → sfexec → 空参数/局部分配 → 函数体 → return → 空释放 → 恢复 caller`：

- `V293_control_enter_full_call`：任意有效控制字节、任意 caller 与 continuation，构造完整调用；不接受执行轨迹、store 结果或后继内存前提。
- `V293_control_enter_call_bridge`：同一个调用后内存读回固定 Enter 前端的一步结果，嵌套字节外内存不变。
- `V293_control_enter_irq_local`：实际 EOI 后执行完整调用，停在 Exit 调用入口，尚不执行 Exit 或中断返回。
- **稳定上层接口 `V293_control_enter_irq_global`**：从普通当前任务状态出发，用框架原 `pint_step` 创建 `kint`，保存被打断的表达式/语句上下文；接上前述轨迹，保留其他 ISR 位、生成的中断栈和精确 Exit 入口 continuation。

全局输入只有原任务、环境、IE=true、无临界区栈以及可中断条件，并不是已经构造好的 `kint` 执行状态。`goodks` 是框架 continuation 合法性前提，不是输入执行轨迹。

## 为什么 caller 可以有同名变量

`sfexec` 为无参数、无局部声明的 Enter 建立空 callee 环境，因此读全局 running/nesting；返回时 `sfreeend_step` 恢复原 caller。用例故意把 caller 的 running/nesting 名字分别指向全局 nesting/running 的地址。若错误沿用 caller，running=1、nesting=0 的实际 guard 会读成 false，而正确 callee 读成 true。

完整调用用例保留非空堆、独立 sentinel；三组实际调用覆盖 running=0/n=254、running=1/n=254、running=1/n=255，结果分别不变、255、255。通用用例进一步量化全部有效字节（包括非1的 running）。本步仍统一要求 nesting 可写，即使未启动/饱和分支实际不写；不声称最弱前置条件。

全局用例含非平凡被打断表达式、非空 caller、原中断栈 `[1]` 与已激活的其他 ISR 位1；进入中断0，最终栈为 `[0;1]`，位1保留。程序环境确实绑定 Enter；Exit 只作未执行切点，不因停在调用入口而获得 Exit 绑定/正确性覆盖。

## 对抗复核和消融边界

两个提前冻结的单因素对照分别选择空 callee / 错误 caller、正确 caller / 错误空恢复环境，检查实际 guard 求值和返回环境名字查找。每组基准必须编译成功，错误变体必须被 Coq 拒绝。其他程序、内存、期望值及证明不变。

**这些是独立环境边界判别，不是完整执行模拟消融。** 不把早期程序绑定失败当成对返回、内存读回或中断恢复的验证，也不修改原语义以制造通过。所有开发失败源快照与日志原样保留。

## 验证与未闭合部分

实测结果在 `audit/logs/stage303-enter-call-prefix/verification.json`，包括10个新结论的全部假设、递归 coqchk、两份源各两次稳定重编译、8项新测试、完整回归、build / audit 分列以及清理记录。只读复核：

```sh
PYTHONDONTWRITEBYTECODE=1 python3 -B audit/logs/stage303-enter-call-prefix/checkpoint.py
```

本轮最终实测：

| 检查 | 结果 |
| --- | --- |
| 两份新 Coq 源稳定重编译 | 各2次，共4次通过 |
| 新结论假设与递归 coqchk | 10个全通过；递归复核约361秒，无新增信任项 |
| 两组独立环境边界消融 | 基准均exit 0，错误变体均exit 1 |
| 新测试 | 8项通过 |
| 完整回归 | 2693项，436失败、1错误；旧失败/错误ID及顺序与302步完全一致 |
| 增量build / project-audit | 通过；活动377份、framework/tactic103份 |
| make audit | 仍因旧函数证据输入身份过期失败（exit 2） |
| git diff --check | 仍为旧 inferules.v 六处尾空白（exit 2），日志字节未变 |
| 开发失败 | 11次均保留原始源快照/日志，其中包含诊断输出尝试，不改写为通过 |

清理仅针对逐项确认的26份本轮一次性 Trust / 环境消融源和编译产物、已恢复缓存备份；保留其源快照、失败日志、既有306份pyc与可复用生产/用例编译结果。根缓存恢复至本轮开始的原字节，所有旧 C/Coq/测试/冻结证据未修改；清单及复核结果见本步目录。

这是**有限执行存在性加固定前端读回**，不是全交错 TaskSim/safety，不是完整 ISR 返回。抽象任务状态 O 仍为参数，尚未把该接口接入未过滤的 `BuildintPre`、初始化可达状态、旧 `osintspec/WFInt` 或整个内核环境。框架 `GOOD_OS`、同一固定程序 K1–K4 以及 uCOS3 均未由此完成。旧全仓失败保留，不宣称全仓通过；目标继续 active，未提交/推送。

下一步优先从实际 builder 资源推导本接口所需的真实字节/权限，并向完整 Exit 调用与固定控制前端模拟连接；不能把这里的任意 O 当成已建立的具体/抽象状态不变量。
