# 第229步：精确 Exit 接入原动态三函数程序

## 本步解决的问题

第228步只有固定逻辑参数的 Exit／SchedNew 双函数环境。本步复用原
`V293_ready_irq_unit` 三函数程序，把精确 changed 后置接入原动态逻辑实参，
并与精确 Enter、两种 scheduler 调用约定放入同一个新 Spec。
没有改动 C、配置、AST、框架或旧证明；也没有原地改写旧 Spec。

## 从入口到调用的连接

1. `V293OSSchedExactJoint.v` 以已有 proof-level tag 区分精确 critical
   scheduler 与原 ISR scheduler。两个分支分别使用已证明的真实本体契约。
   两个 `V293_spec_embedding` 是前后置的 assertion equality，不用弱化
   changed 后置来迁就旧 callee。
2. `V293OSIntExitExactDynamic.v` 直接使用原 `V293_ready_dynamic_exit_fpre`、
   `V293_ready_dynamic_changed_fpre`、`V293_changed_decode/encode` 和原
   ready/TCB/storage Inv。changed 分支解码后使用第228步精确 builder 契约；
   quiet/same 分支继续使用原 unified 完整本体证明。两个分支都通过同一
   tagged scheduler 条目，而不是把 callee 的 InfRules 当作额外前提。
3. `V293_exact_dynamic_spec` 的三个条目是精确 Enter、动态 Exit 和联合
   SchedNew。在同一个程序、Spec、Inv 下证明 WFFunEnv 与 WFIFun，另有真实
   Enter call 和 changed Exit call。退出 call 使用框架 `call_rule`，caller
   frame 保持不变。
4. probe 复用原 RDpre 和 RDprogram，证明同一个 JBstate/JBmemory 满足原
   builder 入口与调用入口。`XDliteral_post` 把动态 changed 后置化成第228步
   字面 XIpost：同一 Inv、精确 p_local、两栈和 globals；没有额外 Atrue，
   callee 的局部保存槽及 domain 由 builder 归还，不混入外部后置。

quiet/same 后置仍是原弱契约；有整个 funasrt 的等式证明它未被删除或替换。
不能把本步称为全路径精确 Exit。changed 仍限 running=1、lock=0、nest<=1、
different priority、clear ISR、原 IE=false。切换后共享值不冻结，后置也不冻结
incoming counter；Inv 内保留存在量化。LocalInv 仍为常 Aemp，owned CI 是已有
opened Inv 的空尾，并不是完整生产 ISR invariant。

## 对照与反驳检查

沿用已证明的 counter 单因素边界对照：固定最大 counter 的同一物理状态、
程序、布局和其他逻辑参数，只换逻辑 counter 快照。两侧 codec 均合法；正确
快照满足原入口，错误快照被实际 counter load 的唯一值排除。此对照只检查
入口／load 边界，不是两次完整执行，不能据此断言下游 switch／return 均被消融
验证。本步明确不声称语义 TDD；所有编译均成功，Python 仅检查结构和身份，
不能替代 Coq 程序推导。非空见证不是初始化可达证明。

对“只是换名字没有纵向连接”的反驳是：真实 builders、原完整 Exit body、
三函数 WFFunEnv/WFIFun 和真实 call 同时存在；对“弱化前置凑非空”的反驳
是直接复用原 fpre，并在同一物理状态上证入口。可信根、实际命令、源码身份、
全量测试和清理结果记录在 `logs/stage229-exit-exact-dynamic/`，最终以
`verification.json` 的实测值为准，不以本文代替检查。

## 当前状态与下一步

旧423失败、1错误及旧 audit/whitespace 失败保留；六门覆盖仍为
94/1/1/1/1/0。GOOD_OS 与同程序 K1–K4 尚未完成，总目标 active，uCOS3 未开始，
本步未提交／推送。三函数局部环境不是整核，也不是连续 ISR。

下一步补齐 quiet/same 的精确返回边界，并衔接 closed Inv 到 Exit 入口；再连接
同一 ISR 的 EOI→Enter→Exit→iret，处理生产 LocalInv、控制值及 lookup 关系、
WFInt、API 与初始化，最终闭合源码级 GOOD_OS 和同程序 K1–K4。
只有第一阶段完成后才开始老师要求的 uCOS3 阶段。
