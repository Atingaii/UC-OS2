# 第230步：quiet Exit 精确资源接入原动态三函数环境

## 本轮解决什么

`OSIntExit` 不总会调度。系统未运行、嵌套深度仍大于1，或者调度锁未释放时，会执行 quiet 路径。原证明返回 `CurLINV`：它允许额外资源被 `Atrue` 吸收，不能一般地逆推精确 `p_local`。第229步只修复 changed 返回；本步从真实 nondispatch 本体重新保留 quiet 的精确资源。

**quiet 的新前置也更强**：调用者必须真正交出 `p_local li t nil`。本步没有证明原弱前置能推出新强前置；没有修改旧证明、C/config/AST/framework/tactics 或历史失败证据。

## 端到端连接

1. `V293OSIntExitQuietExact.v` 复用原 quiet codec、valid 和名称桥接；external/frame 改为精确 `p_local`，真实 `V293_OSIntExit_nondispatch_body` 保留它，builders 按原规则借还 saved 局部槽。只在规则侧条件将精确局部资源弱化为 `CurLINV`，不反向推导。
2. `V293OSIntExitQuietExactDynamic.v` 复用原两级 logical path tag，仅替换 outer=false/inner=true 的前后置。changed、same 和 malformed fallback 字面复用第229步契约；不增加运行时分支或另一个解码层。
3. 原 `V293_ready_irq_unit` 三函数程序不变；同一新 Spec 和原 `V293_ready_dynamic_exit_inv` 下证明 WFFunEnv/WFIFun。Enter、joint scheduler 和 changed/same 本体不变。
4. `V293_OSIntExit_quiet_exact_dynamic_call` 真正使用 `call_rule`，保留任意 GoodFrm caller frame；ambient RI 独立于 callee 的 owned Inv。

quiet 的泛型合同保留原全部 valid 控制分支、原 IE/ISR/两栈；不是只证明 run=0 或常量 Aemp 的局部合同。实例的 `V293_shared_li` 仍是常 Aemp，不等于生产 ISR LocalInv。

## 非空与精确性证据

`audit/probes/V293OSIntExitQuietExactProbe.v` 与原 RDprogram、全局环境、saved 局部域对齐，显式构造五块互不相交的内存：当前任务指针、run=1、nest=2、lock=0、saved 值。使用 extra=Aemp，入口与字面后置没有额外 Atrue，也不把 callee saved 槽混入调用者后置。`Qentry_nonempty` 和 `Qcall_entry_nonempty` 证明同一实际物理入口分别满足 builder/call 前置。

`Qliteral` 的后置字面返回原 OS context、globals、run/lock、nest=1 和精确 p_local；saved 槽由 builder 借还。`Qactual_contract`、`Qactual_call` 使用同一新 Qspec；不是把尚待证明的 callee InfRules 当成假设。

这是最小 quiet footprint 的可满足性，**不是初始化可达**，也不是含完整 TCB/ready/storage 的生产中断入口。泛型合同不要求 quiet 访问不到的 ready 数组，也不以这个简化 fixture 声称生产 ready Inv 非空。

## 单因素边界对照与审阅

复核既有 `RLlocal_exactness_control`：固定同一 REstate，仅把局部断言 `p_local` 中和为 `CurLINV`，后者可满足而前者不能。它说明“原弱后置自动升成精确后置”不成立，**不是两次完整执行**、不是当前 Qpre 的完整反例。不声称语义 TDD。未新增重复的运行时控制因素或凭入口拒绝宣称下游机制生效。

审阅关注：
- 是否只改后置、偷用弱契约？否，强化新入口且从真实本体保资源；旧文件保持。
- 是否偷偷丢栈/ISR/资源？OS context 在合同内，不放进不合法 GoodFrm frame；exact external 明确保留两栈。
- 是否加入无意义 path tag？否，原两级 codec 不变，仅 quiet 替换，changed/same 等式证明保留原条目。
- 是否空前置？五块实际内存给出 builder/call 入口见证。
- 是否等同整核？否，same 仍弱；初始化、生产 ISR、WFInt、GOOD_OS、同程序 K1–K4 均开放。

## 验证与复现

前瞻协议在实现前冻结。每次编译均保存源文件快照、日志、退出码与前后哈希；失败编译保留。最终版本独立 Print Assumptions 与递归 coqchk，具体根数量、耗时和结果以 `audit/logs/stage230-exit-quiet-exact/trust.json` 为准。Python 仅作结构/身份回归，不替代 Coq 语义证明。

```bash
make build COQBIN=/data/home/lucentzhou/.opam/default/bin/ JOBS=2
python3 -B -m unittest discover -s tests -p test_exit_quiet_exact.py
python3 -B audit/logs/stage230-exit-quiet-exact/checkpoint.py recheck
```

两次构建、四个配置后函数身份、全量测试、历史失败 ID 与顺序、旧文件保持及清理均以 verification.json 为准。既有 423 个失败、1 个错误与 audit/whitespace 失败不得删除或称全绿。六阶段仍 94/1/1/1/1/0。

## 下一步与学习顺序

先读本步 Qliteral，理解“入口交出什么、返回必须拿回什么”；再看 Qentry_nonempty，理解“证明的条件确实有人能满足”；最后沿 Qactual_call → 三函数 WFFunEnv → quiet builder → nondispatch body 阅读，不必一开始通读所有 tactics。

下一断点是 same-priority：旧 ISR scheduler 契约仍返回弱 CurLINV，需要真实 scheduler call、target assignment 和 Exit 同优先级路径全程保精确资源。其后才是连续 EOI→Enter→Exit→iret、WFInt 和初始化。总目标仍 active；GOOD_OS 未完成，uCOS3 未开始，未提交/推送。
