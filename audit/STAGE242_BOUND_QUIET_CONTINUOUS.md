# 第242步：bound LocalInv 下的 quiet 连续中断返回

## 本步到底完成了什么

上一检查点只有同一候选环境中的 Enter/Exit/Sched 函数契约。本步稳定入口 `V293_interrupt_bound_quiet_continuous` 把原 wrapper 的 `EOI → scall Enter → scall Exit → exint` 连起来，后端接实际 `BuildintRet`，返回保留 `p_local bound`。运行时代码、原 ready/TCB/storage Inv、固定 C/config 均不改变。共同规格原样使用第241步的 `V293_bound_dynamic_spec`，没有再引入第四套运行时程序。

新增生产文件 `certiucos/v293/proofs/V293InterruptBoundQuietContinuous.v`，独立检查文件 `audit/probes/V293InterruptBoundQuietContinuousProbe.v`。生产代码不导入 audit。实际实测见 `audit/logs/stage242-bound-quiet-continuous/verification.json`，编译失败尝试的原快照与日志也保留。

## 资源链路

| 环节 | 具体动作 | 不能推导的更大结论 |
| --- | --- | --- |
| 名称绑定 | 从现有 bound p_local 取得 running/nesting/lock 的 GE 地址观察 | 不增加外部 globals 前提，不证明启动时建立这些绑定 |
| Enter/Exit | 实际 scall 使用同一个 bound LI；Exit 选择动态 quiet 编码 | 不把 quiet 的条件推广到 changed/same |
| running 权限 | 完整写权限拆成两个只读半份，一个交给 Exit，另一个留在 GoodFrm frame；返回后重组 | 不复制任何可写堆单元 |
| 关闭 Inv | 将真实控制字节和原 kept 资源重新组成 storage，再关闭原 Inv | 不改变 Inv 使困难状态消失 |
| iret | 只复用旧资源蕴含引理，将 globals 显式保留为 frame，最后重建 bound p_local | 没有不同 LI 之间的 Hoare transport |

`globals` 是 GE 名称/类型观察，其资源足迹为空；并不等于“可以任意丢弃绑定”。复制的只有这一观察，字节与抽象对象仍遵守分离逻辑权限。

## 入口与返回不空泛

- `BQbuilders`：字面前置/后置确为实际 `BuildintPre` / `BuildintRet` 的结果。
- `BQentry_nonempty`：原 typed 字节堆上的同一个状态，同时满足强 quiet snapshot 与实际 builder 前置，且没有额外 globals frame。
- `BQenvironment`：原三函数程序、同一 BDspec/LI/Inv 的 GoodI、WFFunEnv、WFIFun；复用第241步已检查的真实函数体契约。
- `BQactual_wrapper` / `BQnonempty_actual_wrapper`：连续 wrapper 实际调用，不把中间 InfRules 当作前提。
- `BQreturn_literal`：独立写出的 spec_done、ISR、ISR 栈、空临界区栈、IRINV、空局部变量域与 bound p_local。
- `BQreturned_nonempty`：从 typed 原始资源单独构造返回侧状态，实际返回 builder 也可满足。这里只是状态见证，不声称运行时可达。

## 预先声明的消融与反例边界

1. `BQreturn_forget` 只把返回断言中的 bound p_local 弱化为 shared p_local，其他 IRINV、堆资源和中断元数据不变。这是单因素断言弱化，**不是两次完整执行**，也不说明所有控制变量绑定都已由初始化建立。
2. `BQroom_is_necessary` 复核原饱和算术反例：running=1、旧 nesting=255 时 Enter 保持255，Exit 变254，不能声称恢复255。没有删除不利结果。
3. `BQquiet_is_not_all` 复核 running=1、旧 nesting=0、lock=0 的 dispatch 边界并非 quiet。
4. `BQother_bit_survives` 证明 EOI 不会清掉其他活动 ISR 位；因此不能从当前位完成就推出 all-clear。
5. 移除最初复制的旧 import 大包与未使用的 storage 别名后重新编译；按直接符号依赖补足最小所需模块。编译的成功/失败快照均保留，不将编译失败称作语义反例。

## 必须保留的限制

生产连续定理从强 snapshot 出发，要求字节界限、栈顶界限、`Room`（running=1 时旧 nesting<255）、`Quiet`（running=1 时旧 nesting>=1 或 lock>0）、先前 ISR 全清与向量有效。抽象操作固定为 `spec_done None`，并未完成真实 ISR 抽象操作。

**不是所有 BuildintPre**：具体入口同时满足实际 builder，不能反向证明任意 builder 都满足上述控制条件。**不是 `WFInt`**，不是初始化可达，也**不是 `GOOD_OS`**。changed/same 在 bound LI 下的连续返回、完整中断不变量、初始化、其他 API 纵向连接和同程序 K1–K4 仍未闭合。候选 Enter 与旧 local-storage Enter 的规格边界差异仍保留，不能声称旧完整环境只改了 LI。uCOS3 未开始，未提交／推送。

## 验证与历史失败

本步对七个生产根和十五个独立根逐根检查假设，并递归 coqchk。允许的已有逻辑基础仍仅 classic 与 functional_extensionality_dep。完整构建、project-audit、全回归和输入身份核对结果以冻结 JSON 为准；新增五项 Python 测试只做结构/来源回归，不能替代 Coq 证明。旧423失败、1错误，以及 make audit 的陈旧函数证据身份失败、原六处 whitespace 失败，必须保持，不降低 gate、不改写旧证据。

下一步优先将 bound-LI 的 changed/same 连续返回接到同一候选规格，再处理实际 builder 的可达控制条件与非全清 ISR；这些仍不能绕过初始化与 WFInt。
