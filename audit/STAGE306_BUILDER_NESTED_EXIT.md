# 第306步：同一 builder 资源连接完整 Exit 嵌套调用

## 先把前因后果说清楚

最终交付仍是固定配置 uC/OS-II V2.93.01 的源码级 `GOOD_OS` 和**同一程序** K1–K4 回归，不是“增加若干证明文件”。第305步把实际 builder 资源接到 `EOI → OSIntEnter`，但停在 Exit 调用之前。本步消费这个**同一个后继堆**执行完整 Exit 嵌套分支，推进到最终 `exint` 语句之前。

直观理解：原先已经处于第 n 层中断，新的中断进入时把计数加到 n+1；退出时必须减回 n，同时不能破坏任务、就绪表和其他内存。Exit 自己还会分配一个四字节临时变量，返回时必须彻底释放，不能只证明“计数读起来正确”。

| 阶段 | 实际完成的内容 | 尚不代表什么 |
| --- | --- | --- |
| builder | 沿用未过滤的原 `BuildintPre`；读取实际控制字节选嵌套分支 | 不是从初始化证明中断可达 |
| EOI/Enter | 同一 P 执行实际前缀并保留 snapshot | 不是另造一份后置资源 |
| Exit 调用 | 调用、局部分配、初始化、临界栈入出、递减、guard、返回释放 | 不是 raw CPU port 调用实现 |
| 整堆结果 | 精确等于调用前堆在 nesting 地址写入 pred(n+1)；fresh 块所有偏移均处理 | 不只是排除 fresh 块后的 frame |
| 资源 | 同一后继内存重新持有原深度 snapshot，控制读回一致 | 不等于旧完整 Inv/WFInt |
| 当前终点 | 下一条语句为 `exint` | 没有执行 `exint`，没有完成 TaskSim/GOOD_OS |

## 生产接口与证据来源

- `certiucos/v293/proofs/V293InterruptBuilderNestedExit.v`
  - `V293_nested_saved_free`：对释放区域内、负偏移、区域外、其他块分别证明整堆等式；不是仅检查四个已释放字节。
  - `V293_nested_void_return_exact` / `V293_nested_body_exact`：执行实际返回与单个局部块释放，恢复 caller；实际临界栈 push/pop 保留。
  - `V293_nested_call_exact`：稳定完整调用接口；调用者只提供实际函数身份、全局绑定、两个 load 和 nesting 写权限，不提供执行或分配/释放结果。
  - `V293_builder_snapshot_nested_return`：实际 byte store 与分离逻辑资源更新使用同一内存。
  - `V293_builder_nested_prefix`：稳定 builder 接口；两个函数都来自同一 P，保留输入 `getabst st` 和 `aop`，最终停在 `exint` 前。
- `audit/probes/V293InterruptBuilderNestedExitProbe.v`
  - 从既有 canonical 非空 ready/TCB/storage 堆获得 builder；不是空堆见证。
  - 原深度1和254分别执行到 Enter 后2和255，再返回1和254。
  - `BNprogram` 明确安装归一化 abstract Exit 和 Enter；**不是**把旧 `RDprogram` 的另一种 boundary Exit 偷换成同一个函数。嵌套分支不调用 scheduler；这个二函数程序不是完整内核环境。

源体身份与信任边界沿用既有 `V293OSIntExit.v`、`V293OSIntExitExecution.v` 和 ADR-0005；本步没有更改 C、配置、AST 或 framework。归一化临界区原语不意味着已经实现原始 port。

## 前置范围与开放义务

本步要求实际捕获 running=1、原深度 **1..254**；locked 值不另加 quiet 过滤，范围从 builder 导出。原深度0可能走调度分支；原255的 Enter 饱和后 Exit 会变成254，不能套用“恢复原深度”。未启动、最外层调度/切换、最终 `exint`、一般 ISR 返回约束、统一旧 Inv/WFInt、初始化可达及同程序 K1–K4 均仍开放。uCOS3尚未开始。

## 单因素后置观察对照

事前协议固定最终期望深度254→255，除此之外源文本完全相同。两侧均先取得已完成非空实际 `EOI → Enter → Exit` 及资源 witness，再在最终 `Loads` 处检查观察；正确侧通过，错误侧在该处类型不匹配。**这不是删除 decrement 的程序消融，也不据此声称所有下游机制必要。** 首轮两侧因缺少直接导入 `JBmemory` 提前失败，保留原日志；补齐相同导入并另写02协议后才获得有效对照。

## 验证和已知历史守卫问题

实际命令、源快照、失败尝试和最终结果位于 `audit/logs/stage306-builder-nested-exit/`；最终汇总以本目录 `verification.json` 为准。不得把局部通过写成全仓通过。

第305步旧测试 `test_frozen_history_and_append_only_project` 用精确相等将 `_CoqProject` 固定在305末尾。因此本步**正常追加注册**必然使它失败。这个问题已在306实施前协议中声明；旧测试、原110项 manifest、补充13项 manifest 及全部失败证据保持原样，既不漏注册新生产文件，也不通过改写冻结测试制造绿色。新增306测试使用“旧前缀保留 + 新路径仅一次”，允许后续合法追加，但不豁免任何冻结源码变动。

第305步的末尾复核脚本另有已纠正的 `.json.json` 问题；其权威结果应同时参见 [305补充说明](STAGE305_CHECKPOINT_CORRECTION.md)，本步已逐项检查并冻结两份305 manifest。

### 本步最终实测结果

- 生产6个结论与probe3个结论均打印假设，递归 `coqchk` 通过（416.73秒）；假设未超出既有经典逻辑与函数外延性边界。
- 两个最终源各稳定重编译两次通过，增量 `make build` 通过；新6项测试全部通过。
- 完整回归2711项：437失败、1错误；除预声明的305精确注册守卫外，原436项失败及1项错误的ID与顺序均保留。**不是全仓回归通过。**
- `project-audit` 通过（active380/framework103）；`make audit` 仍因原 `stale function evidence input identity` 退出2；`git diff --check` 仍是原 inferules 六行尾空白，日志字节与305一致。
- 生产开发失败11次、probe开发失败1次、首轮观察双方提前失败2次，全部保留快照和日志；有效第二轮仅错误后置观察被拒绝，不把提前拒绝计为机制验证。
- 清理仅针对本步一次性 Trust/Observe 源及其编译物、已恢复的根缓存备份；生产/probe源与可复用编译物、所有失败快照与日志、原306个pyc保留。

## 下一步怎么做

最短剩余纵向路径：从本步 `exint` 前的同一资源出发，证明实际中断返回所需 ISR 区间条件，执行返回并连接旧完整不变式；然后覆盖外层调度/切换，而不是再包装一层条件定理。完成这些后仍须处理初始化与全局模拟，才能关闭 `GOOD_OS`。
