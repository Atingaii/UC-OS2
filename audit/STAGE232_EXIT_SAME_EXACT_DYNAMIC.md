# 第232步：same 精确合同接入原动态三函数环境

## 本步解决什么

第231步证明了 same-priority 的完整 `OSIntExit` 本体，但原三函数环境尚未采用这个精确合同。本步接通：

`完整 same 本体 → BuildPreI/BuildRetI → 原两级动态 codec → Enter/Exit/SchedNew 的 WFFunEnv/WFIFun → 实际 Exit call_rule`

固定 C/config/AST、原三函数程序、原 ready/TCB/storage Inv 布局、框架、tactics 与旧证明不变。same 的新前置也更强：从入口就要求 `p_local`，不是从旧 `CurLINV` 前置或旧弱返回反推强合同。原 changed 与 quiet 的入口、返回字面保持。

## 稳定接口

| 新文件 | 上层接口与证据 |
| --- | --- |
| `V293OSSchedAllExactJoint.v` | `V293_OSSchedNew_all_exact_joint_contract` 用真实 builders 同时覆盖 exact-critical 和 exact-ISR；两条 `V293_exact_*_to_all_joint` 用 assertion equality 嵌入联合规格 |
| `V293OSIntExitSameExactInternal.v` | `V293_OSIntExit_same_exact_builder_contract` 对真实函数边界调用第231步完整本体；局部 saved 单元由 builder 管理，不在外部函数断言中偷带 localenv |
| `V293OSIntExitAllExactDynamic.v` | `V293_OSIntExit_all_exact_dynamic_contract` 分派原两级 tag；`V293_all_exact_dynamic_WFFunEnv/WFIFun` 关闭同一原三函数程序；`V293_OSIntExit_all_exact_dynamic_same_call` 使用真实 call_rule |
| `V293OSIntExitSameExactDynamicProbe.v` | `SEenvironment`、`SEactual_contract`、`SEactual_call` 与 `SEentry_nonempty` 在同一实际实例上连接环境、本体、调用和可满足入口 |

联合 scheduler 的 tag 只是逻辑实参，不增加运行时代码。critical 臂沿用第225步精确合同，ISR 臂采用第231步精确合同。changed 分支通过 critical override 的 equality embedding 复用既有完整合同；same 分支通过 exact-ISR override 嵌入；quiet 不调用 scheduler，直接复用第230步合同。`V293_all_exact_dynamic_changed_kept` 与 `V293_all_exact_dynamic_quiet_kept` 分别证明前后置的字面相等，不把两种规格粗略认作等价。

same 合同沿用原 `V293_same_exit_index/args/valid`，没有新建 codec。有效条件仍是 running=1、lock=0、nest<=1、ready priority 与 current priority 相同及 bitmap/table 条件；两种 IE 均可，ISR 和两栈在合同中恢复。返回 `None`、nest=0、目标指针为最高就绪任务、counter 原值不变，并保留精确 `p_local`。saved 仅在内部被清零，局部单元随后交还 builder；不将该局部值错误暴露为外部函数全局性质。

## 实际入口与对照

- `SEge` 将 table/target 的全局声明实例化为 `V293_tcb_type` 指针；实际 pointer bytes 与旧物理堆一致由 `SEpointer_bytes` 证明，不以旧弱所有权推出精确资源。current-thread 槽沿用旧 fixture 的 Tvoid 声明，符合 `p_local` 对该声明类型的存在量化，不能称所有槽都已是生产 TCB 布局。
- `SEcurrent` 直接构造 current-pointer bytes 上的精确局部资源，之后逐块合并 `SEinternal_owned/SEjoint_owned/SEbig_owned`。`SEentry_nonempty` 与 `SEcall_entry_nonempty` 量化 IE 两值，明确使用 `[0]`、`[false]` 非空栈。
- `SEliteral` 展开本次真正的动态前后置，核对 nesting、counter、OS context 与最高就绪目标，非独立的小模型后置。
- `SEie_control` 固定同一个物理状态，只替换逻辑 IE 实参；两套快照均可解码且有效，错误 IE 在断言处被排除。这不是两次完整执行，也不证明下游机制都工作。
- `SElocal_control` 复用固定 REstate 的局部断言边界反例，只比较 CurLINV 与 p_local，不是本步完整入口的反例。
- `SEarity_control` 记录真实 BuildPreI 对多余参数的拒绝；`SEreturn_arity_observation` 同时保留 BuildRetI 本身不检查参数个数的观察，避免把早拒绝扩大成所有 builder 都有相同检查。

不声称语义 TDD。协议在实现前冻结于 `protocol.json`。Python 仅检查结构和证据身份，不能替代 Coq 语义；44 个本步根的 Print Assumptions 与四个入口模块的递归 coqchk 才是对应的机器证明检查。去除重复 imports 后曾暴露列表 notation 的导入顺序依赖；保留失败快照，将唯一 List import 放在其他 imports 之后并重新编译通过，没有改语义合同或放宽门槛。

## 尚未完成什么

**三条 admissible Exit 路径现在在同一 Spec 中采用精确资源合同，不代表对所有输入或所有可达执行已经全覆盖。** stronger same 入口仍需从实际 ISR 中间状态推导；不能由环境闭合跳到连续执行已闭合。

fixture 使用常 Aemp LocalInv，虽有实际类型的 table/target 与实际字节所有权，仍不是完整生产 ready/TCB/storage Inv，也不是初始化可达。WFFunEnv/WFIFun 的参数化证明不自动给出生产中断入口可满足性。

下一步应在同一原程序、新 Spec 和同一 Inv 下连续连接 `EOI → Enter → Exit → iret`，明确区分 quiet/same/changed 可调用条件，验证中间精确资源与共享资源的转移；不能通过挑选另一份 fixture 冒充连续执行。生产 LocalInv、共享控制值与 lookup 语义、嵌套闭包、WFInt、初始化、GOOD_OS 和同程序 K1–K4 仍开放。uCOS3 未开始，总目标 active。

## 复核

```bash
python3 -B audit/logs/stage232-exit-same-exact-dynamic/checkpoint.py recheck
```

实测见本步 `verification.json`、`trust.json`、两次 build 日志与 `full-tests.json`。旧423失败、1错误、原 audit/whitespace 失败都保留，六阶段覆盖仍为94/1/1/1/1/0；本步不刷新旧失败以制造通过，也不提交／推送继承的大量未提交修改。一次性 trust driver 和恢复原缓存后的备份会在清点后清理；失败编译源码快照、日志、旧文件与可复用 Coq 产物保留。
