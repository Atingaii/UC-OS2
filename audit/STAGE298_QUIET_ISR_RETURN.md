# 第298步：quiet 中断返回不再要求 ISR 全清

## 这一小步解决什么

最终目标仍是固定 uC/OS-II V2.93.01 的源码级 `GOOD_OS` 和同程序 K1–K4 回归，然后再开始 uCOS3。**本步不等于整核完成，uCOS3 未开始。**

原 quiet 包装证明要求所有 ISR 位为 false，这比实际入口的不变量更强。本步从真实 `BuildintPre` 内的 `isr_inv` 推出 `j<i` 的位为 false；EOI 清掉当前位 `i` 后，只关闭 `[0,i]` 所需的不变量。对于 `j>i`，不再额外要求清零。

通俗地说：归还自己负责的一段资源，不能凭方便要求其他所有中断也都处于关闭状态。

## 接口与证明链

生产文件：[V293InterruptQuietISRReturn.v](../certiucos/v293/proofs/V293InterruptQuietISRReturn.v)。上层接口为 `V293_interrupt_quiet_builder_general`：

- 输入仍为实际 `BuildintPre` 与原 quiet 过滤的普通合取，不改代码、规格、LI 或 Inv。
- 顺序仍为原 `EOI → OSIntEnter → OSIntExit → exint` 包装。
- 从入口自身推出低位清空，不要求调用者另交全清证明、执行结果或中间 snapshot。
- 使用原 `END None` 中断规格、既有完整 Enter/quiet Exit 调用和真正的 `iretasrt'` 返回资源。
- `255` 饱和入口配对后准确返回 `254`，不声称一定恢复原深度。

底层区间转换显式携带当前 ISR 元数据；不能从任意 ISR 状态无条件生成返回不变量。没有新增公理，也没有修改 C、配置、AST、框架或历史证明。

## 单因素对照：不是空前提

[Coq 对照](probes/V293InterruptQuietISRReturnProbe.v) 使用旧的非空 typed 堆，保持内存、抽象状态、全局/局部环境、栈、代码、BDspec、RDinv 和 LI 不变，只激活非当前位 `1`，当前向量为 `0`。

| 检查 | 可检查的结论 |
| --- | --- |
| `QKsame_heap_active_input` | 同一 M/O 上，原全清入口与仅额外激活位1的实际新入口都可满足；深度1..255 |
| `QKactual_wrapper` | 原完整包装适用于该真实入口；没有执行结果前提 |
| `QKactive_return_resources` | 深度0..255的返回资源切点可满足，仍保留位1 |
| `QKactive_entry_and_return_bit` | 任意满足相应入口/返回断言的状态，其实际 ISR 位1确实为 true，而非仅定义中的表达式 |
| `QKother_bit_preserved_and_old_gate_rejected` | 位1不被 EOI 清除；旧全清条件拒绝该输入；255配对后254 |
| `QKlower_active_builder_rejected` | 当前向量1而较低位0活跃时，真实 builder 仍拒绝；没有删除 `isr_inv` 放宽入口 |

另有独立五位布尔枚举：160组，62组满足低位清空，98组拒绝；逐例检查返回区间全清、区间之外逐位不变。它仅辅助核对算术，不能替代 Coq 证明。首次派生计数漏算当前位的两个输入，原失败和修正理由保存在 `structure-tests-diagnosis.json`，没有改变逐例断言。

## 严格的结论边界

1. 保留原 quiet 过滤；不是 unfiltered `WFInt`，也不是统一 `OSIntExit` 规格。
2. 活跃高位见证不是初始化可达性证明；不宣称生产系统一定可达该状态。
3. 输入可满足、完整 Hoare 包装、返回资源可满足是各自的结论。两个独立端点见证不是同一条具体 C 执行轨迹；返回资源指 `exint` 的返回条件切点，不能冒充弹栈后的任意运行状态。
4. 参数化接口不要求全 ISR 清空，不表示任意入口都满足原不变量。低位活跃的负例必须继续拒绝。
5. 一般 enabled dispatch、强 current guard、统一高层规格、`WFIFun`、完整 `WFInt`、`GOOD_OS` 和同程序 K1–K4 仍未闭合。

## 验证与阅读顺序

| 本轮实测 | 结果 |
| --- | --- |
| 生产与对照最终同 SHA 各两次编译 | 通过；31份编译快照全部保留，其中23次失败不删除 |
| 18个新根的假设检查、递归 `coqchk` | 通过；只使用既有 classic / functional extensionality 信任边界 |
| 新增 Python 回归 | 6项通过 |
| `make build` | 增量构建通过，不冒充全量干净重建 |
| project audit | 通过，372个活动文件、103个框架/战术文件；文件数不代表完成度 |
| 全量 Python 回归 | 2657项，435失败、1错误；不是全绿 |
| 原失败身份 | 原434失败和1错误按ID与顺序保留；新增1项为旧第297步测试要求 `_CoqProject` 精确等于其冻结末尾，本步追加模块使其拒绝 |
| `make audit` / `git diff --check` | 仍分别报告原函数证据身份过期 / 原框架6行尾随空白，不修改旧门槛 |

旧检查点首次复验先被编译改变的 lia 缓存拒绝；恢复本任务开始时的精确缓存后，再次复验由 `_CoqProject` 追加身份拒绝，两次原始日志都保留。全量回归在恢复缓存后运行，没有改写旧冻结证据来制造通过。

机器结果见 [verification.json](logs/stage298-quiet-isr-return/verification.json)；本步局部检查与全库状态分别报告，不能将旧失败隐藏为全绿。

建议先读本页的对照表，再看 `QKactual_wrapper` 的定理声明，最后按“入口低位清空 → 区间归还 → 完整包装”的顺序读生产文件。下一项工作仍是将一般中断上下文、调度/不调度和高层规格接到同一生产入口，而不是继续堆积互不相连的小模型。
