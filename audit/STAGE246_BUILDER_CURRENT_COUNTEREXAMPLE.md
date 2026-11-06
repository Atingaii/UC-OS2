# 第246步：实际中断入口缺少当前优先级关联的反例

## 为什么先检查这个问题

第245步的 same 路径已经能使用框架原生规则消耗 `sched;;done`，但显式要求 `V293_current_task tasks t nc`。要扩展到所有实际中断入口，不能把这个附加条件当成已知事实；必须检查它是否能从当前 `BuildintPre` 推出。

本步结论：**当前候选 `RDinv` / `LDli` / `BCintspec` 组合不能推出该关联。** 这是一个由 Coq 检查的候选证明边界反例，不是发现了可达的内核漏洞。原 C、配置、AST、框架、Inv、函数规格、旧证明和旧失败均保持不变。

## 同一份资源上的单因素检查

文件：`audit/probes/V293InterruptBuilderCurrentCounterexample.v`。

| 固定或变化项 | 修改前 | 修改后 |
| --- | --- | --- |
| 当前优先级字节，块94偏移0 | 6 | 4 |
| 抽象当前任务 | `OwnershipWaiting` | 不变 |
| 该任务在同一任务表中的优先级／状态 | 6／waiting | 不变 |
| 最高就绪选择值 | 4 | 不变 |
| 其它 concrete 字节、抽象表、环境、中断元信息、抽象操作 | 原 fixture | 完全不变 |
| 实际 `BCpre` | 满足 | 仍满足 |
| 当前优先级与当前任务关联 | 成立 | 不成立 |

- `NCtyped_single_byte`：从已有 typed `JBmemory` 与 `RIabstract` 见证拆出入口资源；只写一个 `Tint8`，修改前后保持同一个 concrete frame 和 abstract frame 的 join 见证。完整内存和入口片段都具有 store 见证；所有其它地址逐点相等。
- `NCrelation_single_factor`：在同一个 `BCpre` 中检查关联条件的正／负结果。并非因入口被提前拒绝而把未检查的后续机制算作成功。
- `NCcurrent_relation`：从状态实际读取抽象当前任务、任务表和当前优先级字节，再要求 `V293_current_task`。不是把预期任务或预期优先级硬写进待验证谓词。
- `NCbuilder_not_current_relation`：同时给出字面的 `BuildintPre` 等式，并否定“所有满足 BCpre 的状态都具有关联”的候选蕴含。
- `NCcurrent_mismatch`：选择值4与修改后的当前字节相等，但当前任务仍是优先级6的等待任务；同一完整抽象表上的 `sched_self` 不成立。

`NCsnapshot` 复用旧 changed snapshot 的资源形状，不声称修改后满足 changed 的不等优先级有效性条件。这里调用的是仅关闭资源到 builder 的旧引理，不是把它当成已证 Hoare 前置。

## 这一步排除了什么，没排除什么

排除了直接沿用当前候选 Inv，从实际 builder 无条件提取第245步新增 current-task 条件的路线。ready bitmap 与 TCB 的对应关系没有丢失；缺的是 physical 当前优先级与 abstract 当前任务之间的约束。旧 storage 只要求字节有类型，值可以是4，也可以是6。

**不是两次完整 C 执行，不是初始化可达，不是所有 BuildintPre 的分支分类，不是 `WFInt`，不是 `GOOD_OS`。** 没有证明内核存在该可达状态，也没有证明所有可能的 WFInt 规格均不可成立；同程序 K1–K4 未闭合，uCOS3 未开始。

不能为了消除反例而直接加强一个纯条件、改旧规则，或者删除 fixture。下一步应先检验候选关联在真实 switch 边界的保持性，再设计最小可用入口契约：现框架 `GoodI` 的切换闭包更新当前任务指针／抽象任务，不自动写优先级字节。这个接口事实需与实际源代码的写入顺序一起处理。简单增加一个全程等式并不等于已证明 `GoodI`。

## 复现与证据

全部日志在 `audit/logs/stage246-builder-current-counterexample/`；`protocol.json` 在首轮编译前固定单因素、保持项和结论边界。旧第245步清单87项已逐条核验。

```bash
python3 -B audit/logs/stage246-builder-current-counterexample/compile.py \
  audit/probes/V293InterruptBuilderCurrentCounterexample.v unique-label
python3 -B -m unittest discover -s tests -p test_interrupt_builder_current.py -v
python3 -B audit/logs/stage246-builder-current-counterexample/checkpoint.py recheck
```

独立 `Print Assumptions` 与递归 `coqchk` 检查本步12个证明根及依赖；允许的旧逻辑公理仍仅限 classic / functional_extensionality_dep。最终 `probe16` 编译通过；此前失败快照全部保留，`probe14` 是裁减 imports 前的通过版本；删除12个无用直接 imports 后再次通过，不改变定理。

构建、项目审计和回归的实测退出码见 `verification.json`。新增5个结构回归测试；语义判据是 Coq 定理，不是 Python 文本匹配。旧423失败、1错误继续保留，并核对具体失败／错误的顺序；覆盖仍为94/1/1/1/1/0，不增加 full-target 覆盖。`make audit` 仍因旧 function evidence identity 过期失败；whitespace 仍是旧框架六行。未提交／推送。

一次性 Trust 驱动及其产物仅在核对清单后清理；恢复本步前的两个根目录算术缓存。保留源文件、可复用 Coq 产物、日志和全部失败快照。
