# 第69步：任务创建入口接通 TCB 成功返回

## 这一步实际完成了什么

稳定接口：`certiucos/v293/proofs/V293TaskCreateTCBSuccess.v` 中的
`V293_OSTaskCreateExt_to_TCB_success_under_hooks`。

同一条存在性、无交错执行轨迹现在连接：

1. `OSTaskCreateExt` 已有的函数体入口、参数检查、CPU_SR 初值和优先级槽预留；
2. 栈初始化调用、**显式的真实栈 Hook 返回义务**、`psp` 实际写入；
3. 七个实参实际求值与 `OS_TCBInit` 调用；
4. TCB 调用分配、字段初始化、**两个显式真实 Hook 返回义务**、优先级表写入、任务链及 ready 位图发布；
5. 返回 `0`，释放该 TCB 调用的9个对象／29字节，恢复 caller 环境。

这里不是把两个不同状态的结果拼贴起来：TCB 初始化从前缀实际到达的 `Mbridge` 开始。输出也暴露到达该内存的前缀轨迹；fresh9 仅相对 `Mbridge`，不错误地说它们在可能分配内存的栈 Hook 之前也 fresh。

## 所有权接缝

调用者14个单元包含优先级槽，TCB 初始化也需要这个槽。不能同时把它列为 callee 输入和 caller frame。新接口将它移交给 callee，caller frame 只保留其它13个单元；利用分离逻辑重排同一内存，不复制权限。

最终仍保留 caller 的 `psp`、参数、`err` 及外部 frame。TCB 的9对象释放结论没有因为跨函数连接而丢弃。

## 三项 Hook 义务尚未兑现

没有新增 Hook 实现、公理或 noop。三个义务都要求实际执行轨迹和所列所有权保持，不要求整个内存输入输出相等。固定源中的五个端口仍只有声明，固定程序实际在缺失的 StackHook 入口停止。不能将这个条件定理记为固定程序成功运行。

## 独立检查

`audit/probes/V293TaskCreateTCBSuccessProbe.v` 不导入旧 audit probe：

- 两份字面 body 内存和两份假设返回锚点内存分别证明可满足，各42个拥有单元；
- p0／p12 的 body 入口实际到达缺 StackHook，并证明无下一步；
- 完整条件实例仅一例：p12、旧任务链头 NULL、栈返回非 NULL；**并非全部分支或无条件成功实例**；
- 同一最终内存中，42项结果均可 typed load；读回集合复用生产后置定义，不是独立的完整语义 oracle；三个字面终点负控另行固定返回值、err及表槽。返回值0，但 `err` 仍为9，因为调用结果赋值还在 continuation 中；
- 同证明体终点负控分别改坏返回值、`err` 和优先级槽，正控通过后，三个变体都在修改的终点失败。

前瞻单因素消融只在独立、可满足的返回锚点删除 `kassignr err Tint8`：输入返回值同为0，内存、环境、IE／si／ci和后续 continuation 不变。保留赋值则 `err=0`，移除则 `err=9`，caller77两侧均保留。**只授该赋值锚点信用，不授三个 Hook、整个前缀或完整创建路径消融信用。** 两侧控制状态不同是被删除 wrapper 的直接结果，不声称二者在同一 continuation 层级结束。

## 验证记录与失败保留

证据位于 `audit/logs/stage69-task-create-tcb-return/`。先冻结 `protocol.json`，再重新 materialize 固定修复源、Clang 预处理／AST，核对94个配置后函数身份。

生产证明的前五次失败均保留：缺显式 import、过长 exists binder、缺 Hook 单元定义及所有权重排问题；第六次通过。首次 probe 编译期间追加了 readback helper，且因该 helper 的状态参数推导失败而失败；该次不授源码身份信用。第二次从最终完整源码快照重新编译，交付身份以第二次为准。不重写第一次快照或失败日志。

231活动源增量构建，复用1150旧产物；不是冷构建。最终信任检查、回归、缓存恢复、清理计数和证据身份以本步 `final-report.json`、`trust.json`、`regression-comparison.json`、`cleanup.json` 与 `final-evidence-manifest.json` 为准。

## 下一步怎么理解

把它看作“子函数已经返回，调用者还没有接走返回值”：

- 返回 `0` 是 callee 的返回值；
- `err=0` 要再执行 caller 的赋值动作，目前主定理尚未执行它；
- 然后还要检查 `err==0`、运行态下调度，并返回 `err`。

下一步应连接主轨迹上的 `err` 赋值，并继续保留9对象释放与 caller frame，随后建模精确创建后缀。不能拿独立锚点实验替代这段连接。

## 不变的边界

沿用 ADR0004/0005/0007 的手工前端边界，非 verified frontend／ABI。不是 localHoare、全执行 safety、完整 `OSTaskCreateExt`、完整 OSInit 或 GOOD_OS。七次创建调用实际 Mf 连接、同程序 K1–K4 和最终整核证明仍开放；六门仍94/1/1/1/1/0。uCOS3未启动，先完成第一阶段的目标不变。未提交／推送。
