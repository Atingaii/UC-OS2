# 第231步：同优先级 OSIntExit 完整本体保留精确资源

## 本步解决什么

第230步已经把 quiet 分支接入精确合同，但动态环境的 same 分支仍是弱合同。本步先打通 same 的真实调用链：

`真实 scheduler builders/本体 → call_rule → target 指针赋值 → 同优先级比较 → excrit → return`

不是把旧弱后置改名为强后置。same 的新前置也更强：从入口就要求 `p_local li tid nil`，不能从旧 `CurLINV` 逆推。运行程序、固定 C 源码、配置、AST、原 ISR codec/context、框架与旧证明都保持不变。

## 稳定接口

| 文件 | 接口与作用 |
| --- | --- |
| `V293OSSchedISRExact.v` | `V293_OSSchedNew_ISR_exact_contract` 对真实 BuildPreI/BuildRetI 调用已证明的精确 scheduler payload；`V293_OSSchedNew_ISR_exact_WFFunEnv` 关闭该单函数环境；`V293_OSSchedNew_ISR_exact_call` 使用真实 call_rule；`V293_OSSched_ISR_exact_prefix` 接真实 target update |
| `V293OSIntExitSameExact.v` | `V293_OSIntExit_same_exact_priority_body` 从 saved 清零到 return 证明原完整归一化 OSIntExit 本体的 same 路径，不接收任何“本体已正确”的假设 |
| `V293OSIntExitSameExactProbe.v` | 重新构造实际堆上的精确局部所有权、完整 same 前置、两种 IE 和非空栈，以及同一新 scheduler Spec 的实际 call 与单函数环境 |

完整本体的条件是 running=1、lock=0、nest<=1、ready 选择与 current priority 相等，以及原 bitmap/task-table 有效性、地址环境和 GoodLInv/GoodFrm 条件。IE 初值允许 true/false；ISR、两栈在合同内保存恢复，不偷偷放进 GoodFrm。后置保留精确 `p_local`，nest=0、saved=0、目标指针指向最高优先级 ready task，counter 原值不变。

`V293_exact_tail_reads` 只在比较表达式的求值侧条件上把精确资源弱化，执行链的断言一直保留精确资源。不存在从弱 post 回推强 post 的桥。原有 `V293_exit_depth` 行为没有修改，因而此合同本身也不证明 nesting 与 ISR 栈深度的全局对应。

## 非空与对照

- `QEcurrent` 直接证明既有实际 current-pointer bytes 上的精确 `p_local`，再经互不重叠内存合并构造 `QEjoint_owned`、`QEphysical_owned`、`QEbig_owned`；不拿旧弱前置作为精确资源来源。
- `QEpre_nonempty` 使用同一 `RCbigmemory` 证明实际完整 same 入口；`QEboth_ie_and_nonempty_stacks` 明确覆盖 IE 两值与 `[0]`、`[false]` 非空栈。
- `QEbody` 在同一新 `QEspec` 下实例化完整本体；`QEscheduler_environment` 证明实际 callee 的 WFFunEnv；`QEcallee_nonempty` 和 `QEactual_scheduler_call` 给出真实 scheduler call 入口及规则应用。
- `QElocal_control` 复用固定 REstate 的局部断言边界对照：旧 CurLINV 成立而精确 p_local 不成立。只替换断言，不是本步完整 QEpre 的反例，不是两次完整执行。
- `QEwithout_zero` 通过实际 saved load 区分同一物理状态上的 saved=1 与 saved=0 断言；`QEzero` 仅为赋值边界的旧局部合同实例。这也不是两次完整执行的消融。

不声称语义 TDD。实现前协议冻结在本步 `protocol.json`；Python 回归只检查结构和证据身份，语义以 Coq、Print Assumptions 与递归 coqchk 为准，不能互相充当循环判定器。

## 本步边界与下一步

**本步尚未替换动态三函数 Spec 的 same 合同。** 本步证明的是精确 scheduler 的单函数环境与 same 完整本体，不能据此宣称原三函数环境已使用 same 精确合同。下一步是 same 的函数边界 builders/codec 与原 Enter/Exit/SchedNew 动态环境连接，再推进连续 ISR、WFInt 和初始化可达。

fixture 使用常 Aemp LocalInv、Tvoid 指针表和局部实际字节布局；不是完整生产 ready/TCB/storage Inv，也不是初始化可达。参数化本体定理不等于所有参数下完整内核状态都可达。

完整连续 ISR、EOI/Enter/Exit/iret、嵌套闭包、生产 LocalInv、GOOD_OS 和同程序 K1–K4 仍开放。uCOS3 未开始。总目标保持 active，不因局部通过就宣布两个阶段完成。

## 复核入口

```bash
python3 -B audit/logs/stage231-exit-same-exact-body/checkpoint.py recheck
```

实测见本步 `verification.json`、`trust.json`、`full-tests.json`、两次 build 日志及冻结 manifest。保留旧423失败、1错误及原 audit/whitespace 失败；六阶段覆盖仍为94/1/1/1/1/0。失败编译源码快照和错误日志同样保留，不把局部编译修正解释为全库缺陷已经消失。未提交／推送。
