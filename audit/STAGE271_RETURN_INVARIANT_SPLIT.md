# 第271步：实际返回后分离原框架 INV 与 RDYINV

## 为什么先做这一步

第270步已交付实际完整调用和目标 pending 返回，以及 `ready_current_core ** (CurTid ** frame)`。但框架的任务模拟不直接消费这种形状，而使用共享 `INV`、当前任务 `RDYINV` 和独立资源。仅把 core 名字换成 Inv，或让两个断言同时持有同一份 core，都会造成错误。

本步不新建不变式，不改旧断言、源码或执行规则。新增生产文件 `certiucos/v293/proofs/V293CurrentReturnInvariant.v` 的唯一上层接口为 `V293_current_return_invariants`：

```text
ready_current_core ** (CurTid t ** R)
    ==> (INV existing_current_inv ** RDYINV existing_current_inv t) ** R
```

这里是有明确上下文条件的同一物理堆分离：所有 ISR 位为 false；仅当返回 IE=false 时，实际中断栈顶必须不大于 INUM。R 完整保留，不要求其为空、不用 Atrue 吞掉它，也不要求它含有某个执行或模拟证明。共享 core 内原有的半份当前任务指针与独立 CurTid 的另半份不复制。

## 两种返回状态的原定义分配

| 返回 IE | 原 INV 拥有 | 原 RDYINV 拥有 | 独立 R |
| --- | --- | --- | --- |
| true | 共享 core 和空的高层 ISR 段 | IE=true、isrclr 和半份当前指针 | 完整原样保留 |
| false | 空的高层 ISR 段 | SWINV 中的共享 core、flags 和半份当前指针 | 完整原样保留 |

IE=false 时，core 不在 INV 里；IE=true 时，core 不在 RDYINV 里。断言均来自原 `framework/logic/assertion.v`，不是为得到通过而弱化的替代定义。这是特定现有候选不变式的端点重组，不是整核所有状态的 Inv 保持。

## 实际执行与单因素对照

独立文件 `audit/probes/V293ReturnInvariantSplitProbe.v` 直接复用270的同一个 FWtasks/FWos 入口与实际完整调用，没有新造 skip 程序。`IPfull_call` 的前提只有原来的两个 fresh 条件，无执行成功或 ProgSim 前提；最终直接交付上述分离，并保留旧任务 saved 值、canary90=99，目标 saved98 四字节真实释放。`IPnonvacuous` 复用真实构造出的可满足入口和实际执行。

前瞻协议在实现前冻结于 `audit/logs/stage271-return-invariant-split/protocol.json`。`IPsaved_top_actual_ablation` 使用270的双执行：先从完整入口到达共同 switch 快照，再仅删除目标保存栈顶 false，其余物理堆、代码、任务表和非目标 aux 不变。

| 对照 | 原目标保存栈 | 返回 IE / 剩余保存栈 | 完整最终物理堆 | 原 INV 与 RDYINV 分离 |
| --- | --- | --- | --- | --- |
| 原路径 | false :: true :: vci | false / true :: vci | 同一个 Mf | 成立 |
| 仅删除第一个 false | true :: vci | true / vci | 同一个 Mf | 成立 |

两支实际执行均已存在，并非把较早的拒绝当作后续机制生效。变体只从共同达到快照开始，不声称两种不同栈由同一个完整初始执行产生。本步新证明的是它们均可交付原框架所需的资源分离，而非再次宣称新增了270已经证明的执行。

另有独立的必要条件检查：`IPdisabled_top_bound` 从任意原 INV 推出 IE=false 时 top<=INUM，`IPout_of_range_rejected` 证明栈顶3不能满足该条件（原 INUM=2）。这是断言适用边界检查，不是第二项实际执行消融。IE=true 分支没有加入不必要的 top 上界。

## 证据、反向审查与剩余工作

稳定编译两遍、10个新增证明根的 Print Assumptions 与递归 coqchk、完整测试及差分分别记录，最终实测以本步 verification.json 为准；文本检查不是 Coq 内核证明。旧失败、失败编译快照和旧冻结身份不改写。工程只登记新增生产文件；README 与状态文件仅前插，不改历史尾部。

本步没有证明 TaskSim、ProgSim、LINV 安装或任意交错安全。R 中包含旧 saved 和 RCframe；RCframe 的只读 lookup 仍不是任务私有 LINV。当前任务候选仍允许“缓存匹配或最高 ready”的析取，资源分离不是新的 cache 一致性结论。ISR 位全 false 是公开条件，不是完成实际中断安装。

原任务仍 blocked，不能借这次分离直接调度切回；尚需真实 ready/blocked 转换、调度选择以及保存的任务模拟义务。目标 pending 已存在、共同 si、typed high=88 而非初始化可达；原 IRQ builder 布局尚未统一，沿用 ADR-0010 的源码级边界，不声称外部 CPU port 细化。

**GOOD_OS、WFInt/WFIFun 的整核闭合、同程序 K1–K4 仍未完成，uCOS3 未开始，未提交／推送。总目标 active。** 下一步应将这份确切的 INV/RDYINV 分离接到原 TaskSim 的保存续体义务，不以新包装或人为环境切回替代它。
