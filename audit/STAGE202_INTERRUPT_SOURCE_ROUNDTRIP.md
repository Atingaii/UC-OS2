# 第202步：从真实中断准入到完整同任务调用与中断返回

## 解决哪个缺口

第201步消费的是输入映射中已有的返回现场；不能由此推断现场的来源已经证明。本步改从原始任务代码、表达式续体、局部环境和 `IE=true / ci=nil` 的实际映射绑定出发，由原 `pint_step / li_step` **现场生成** `kint`，随后运行显式框架包装器：

`中断准入 → EOI → OSIntEnter 完整调用 → OSIntExit 完整调用 → exint`

包装器明确位于已接受的源码级中断抽象边界，不是编造一个平台 ISR 的 C 函数。固定程序的三个配置后函数均独立重建并核对哈希，原 C、配置、已有 AST、框架和旧证明未修改。

## 主接口与实际行为

`V293_interrupt_source_roundtrip` 不要求预先存在 `kint`，也不把 trace、分配、store、free、执行结果或路径分类答案列作前提。它要求实际 `T/les/aus` 绑定、中断允许条件、源码 lookup、空间所有权、地址不别名，以及同一 task map 中“当前任务已经最高就绪”的关系。

原中断规则保存被中断代码/表达式续体/环境，令处理器局部环境为空，压入 IRQ 并置 ISR 位。显式 EOI 清除该位，`OSIntEnter` 真实经过 scall/sfexec、空局部分配、原分支、赋值和返回，使物理 nesting 从0变1。`OSIntExit` 再经历 fresh saved 四字节分配、临界区、nesting1变0、真实 `OS_SchedNew` 调用、目标指针更新、比较 false、退出/返回/释放。最后由原 `exint_step` 恢复原代码、表达式续体、局部环境和 ISR 栈；原始临界栈为空，IE 依原规则设为 true。

最终给出原 `T/les/aus` **整体恢复**、heap 指定更新与块外 frame、nesting0、当前目标指针，以及 saved 四字节均已释放。不是只恢复一个预期指针便宣称全现场恢复。该路径不会执行 task switch。

## 独立非空见证与消融

| 检查 | 保持不变 | 改变/观察 |
| --- | --- | --- |
| `SXcomplete_roundtrip`、`SXroundtrip_canaries` | 独立 ready4/waiting6 任务资源、非空 ready/table/decoder、实际 intunit lookup | 完整准入/两次调用/中断返回；非空表达式续体及 caller 恢复，saved 释放；counter19、canary99、caller同名saved23/局部running0保持 |
| `SXenabled_actual_entry`、`SXdisabled_no_interrupt`、`SXonly_IE_changed` | 同一程序、代码、环境、堆与 IRQ 安装 | 仅初始 IE 改变；true 实际准入，false 不存在 lintstep；只是否定中断准入，**不否定其他全局执行** |
| `SXeoi_prefix_control`、`SXeoi_only_effect` | 函数程序、初始代码/环境/堆、中断准入与准入后的公共调用续体 | 仅以 skip 中和 EOI；两侧都经过实际 li_step，到同一代码/环境/heap/aux 端点，IRQ1 的 ISR 位分别 false/true |

EOI 对照只运行到两个完整调用之前。它不是两份完整 ISR 的返回消融，不能据此声称所有下游机制都有效；下游成功由独立完整正控核验。没有为了让消融“通过”而改掉 frozen protocol。

逻辑空间前置明确在 **ISR 已清除、IRQ 已压栈、IE=false、局部环境为空** 的视图。见证先从 `FXentry 0 4` 的真实空间资源出发，按 cell/read-bytes 结构证明辅助状态无关性，再对特定 frame 使用它；没有从 `GoodInvAsrt` 直接推出任意断言可跨 ISR 栈变化。这个特定逻辑视图不等于从原任务生产 invariant 推出真实 ISR invariant。

## 检查与复现

证据目录：`audit/logs/stage202-interrupt-source-roundtrip/`。前置 `protocol.json` 保持原哈希；所有失败编译快照与日志保留，包括一次因整张内存展开过慢而中断的尝试。稳定身份是 body22/probe07，共22个新根，逐根假设和递归 `coqchk` 结果记录在 `trust.json`。完整回归、旧失败有序 ID、旧文件身份、清理清单与限制以 `verification.json` 为准。

```bash
python3 audit/logs/stage202-interrupt-source-roundtrip/recheck-checkpoint.py
/data/home/lucentzhou/.opam/default/bin/coqc -q -R . CertiOS certiucos/v293/proofs/V293InterruptSourceRoundtrip.v
/data/home/lucentzhou/.opam/default/bin/coqc -q -R . CertiOS audit/probes/V293InterruptSourceRoundtripProbe.v
python3 -m unittest discover -s tests -p test_interrupt_source_roundtrip.py
```

先做只读重检。不要重跑会覆盖冻结输出的生成/编译驱动；独立 coqc 可能更新已有算术缓存。

## 仍开放的边界

这是同任务、从满足前置的状态出发的存在性不交错 trace，不是对所有中断/交错的 safety 定理。独立空间 fixture 的任务表非空，但不保证运行时映射已覆盖全部任务，也不是初始化可达性见证。

没有生产平台 ISR C 源码/refinement、原 `OSIntCtxSw` 实现、不同任务的现场生成历史或等待任务唤醒；没有建立生产 ISR/LocalInv、WFFunEnv、初始化、完整全局环境或全系统模拟。`GOOD_OS` 与同一程序 K1–K4 仍未闭合，uCOS3 未启动；六门仍为94/1/1/1/1/0，总目标 active，未提交/推送。旧423项失败、1项错误及旧审计/空白失败均不得隐藏或清零。

下一步应把这条存在性执行与具体 ISR 规格、局部不变量和调用环境证明连接，而不是将任意包装器或测试状态计为生产中断系统已验证。
