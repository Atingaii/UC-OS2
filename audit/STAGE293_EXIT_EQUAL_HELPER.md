# 第293步：最高优先级仍是当前任务时，从 helper 调用切点到返回

## 本步结果与边界

中断退出允许“不切换”。本步把已有真实 `OS_SchedNew` 调用与目标指针写入，连接到优先级相等时的 false 分支，再执行退出临界区、释放 saved、恢复调用者并返回。后置仍为原 storage 家族的 `RDYINV`，不是 Post=True。

**这是 helper 调用切点证明，不是 OSIntExit 完整客户端调用，也不是 GOOD_OS。** 外层 saved 已分配；从函数入口到此切点的 running、encrit、nesting/lock 前缀尚未接入本分支。此前 changed 分支与 running=0、nesting 未退尽、lock 非零的局部成果保持原样。

老师要求的最终顺序不变：整个 uCOS2 的固定配置源码级证明闭合后，才开始 uCOS3。uCOS3 未开始。

## 接口与内部执行

生产文件 `certiucos/v293/proofs/V293ExitEqualHelperTaskSim.v` 只有一个公开 Theorem：`V293_exit_equal_helper_TaskSim`。四个辅助 Lemma 分别完成局部资源、重闭合、比较/返回和目标赋值。

| 环节 | 本步实际连接 | 不由此声称 |
| --- | --- | --- |
| helper | 真实 scall、全部 fresh 局部分配、两赋值、释放及返回 | 外层 OSIntExit 入口可达性 |
| decoder | 返回后将两个只读半份合回完整 storage | 可以忽略权限或任意别名 |
| 选中任务 | 同一 ready/task 关系的唯一最高者，加 current_task 与 highest_ready，推出 next=t、nh=nc | 强 current guard 缺口已关闭 |
| target | 从完整 owned 单元构造真实 store，将旧目标写成当前任务 | target 初始值必须已正确 |
| 比较 | 从 owned 字节构造 load/eval，相等使 different 为 false | 不同优先级的这条后缀也能返回 |
| 返回 | 原 excrit、free、sret 与调用者恢复，原 `RDYINV G t ** LINV` 后置 | 统一 OSIntExit/WFIFun/WFInt |

公开接口要求函数/helper 绑定、变量名互异、全局/局部环境绑定、抽象任务表、current_task、highest_ready、ISR 全清和空间资源；没有执行结果、store/load/eval 结果或下游 TaskSim continuation 前提。内部使用的通用 helper continuation 在本模块消去。counter 的初值可任意；false 路径不执行 increment/handoff，但公开 storage 后置不额外断言每个缓存字节值。

高层停留在 `SKIP`/合法客户端尾部。这里连接的是分支专用 END None 的残余切点，**尚未消费抽象 sched 的 no-op，也没有统一 API 规格绑定**。不能把高层 SKIP 切点当成匹配两层 scall 的完整调用。

## 非空实例与前瞻单因素对照

`audit/probes/V293ExitEqualHelperTaskSimProbe.v` 独立构造 `EHmemory`：RTfull 的当前指针为 OwnershipReady，保留 ready/任务记录、完整 256 项 decoder、saved、current=4、high=4、任意旧 target（实例为 OwnershipWaiting）及 counter=Int.mone。它不是由一个已经完成的执行结果反推的前置堆。`EHbase` 构造资源，`EHentry` 调整临界栈，`EHnonempty_call_cut` 实例化原 RDYINV 后置；不证明 outer-entry reachability。

编写新源前冻结 `protocol.json`。`EHcurrent_byte_control` 只在同一非空 EH 堆把 current 字节 4 写成 6，保持 high=4。它证明真实 store/load、所有其他地址内容不变以及本地 different 表达式从 false 到 true。**不是完整调用执行消融**，不执行 helper、目标写入或整个外层前缀；不将局部比较变化当作所有下游机制必要性的证据。对照的缓存与当前任务记录不再一致，故不把对照堆宣称为公共定理的另一合法输入。

## 调试与审查

首次闭合最后一处目标时，`nh=nc` 已由 ready 关系证明，但返回资源仍含 nh。只把等式在资源中 rewrite，并显式给 op/oldtarget，即可应用返回后缀；没有添加额外前提、改变规格或削弱门槛。失败快照及单目标诊断保留，正式源不含诊断 tactic。

逐条限制：固定源码/配置/边界归一化 AST/框架不变；不是 C 前端或原端口 refinement；IE=false、si=nil、ISR 全清及空 LINV，top flag 任意；强 current guard 缺口不变。统一分支资源/规格、等优先级外层完整调用、WFIFun/WFInt、同程序 K1–K4 和 GOOD_OS 均未闭合。旧失败保留，不修改覆盖数据库充当 full_target_linked，不提交/推送，目标 active。

## 复验

`audit/logs/stage293-exit-equal-helper/` 保存前瞻协议、2206 项旧文件基线、准确 OSIntExit 源码身份/行锚点、逐次编译快照与失败日志、两次同 SHA 成功、逐根 assumptions、递归 coqchk、全库回归及只读封存检查。

```bash
PYTHONDONTWRITEBYTECODE=1 python3 -B audit/logs/stage293-exit-equal-helper/checkpoint.py
```

最终实测以 `verification.json`、`trust.json` 和 `test-delta.json` 为准。旧 gate 不改写；旧检查点对新增 `_CoqProject` 条目的拒绝单独记录。仅清理经逐一确认的一次性 Trust 源/编译产物及缓存备份；原有缓存恢复原字节，306 份既有 pyc 保持不变，交付源与复验材料保留。

## 下一步

将本后缀接入真实 running/encrit/nesting/lock 前缀与外层 saved 分配，得到等优先级完整客户端调用；再统一分支资源与抽象规格。局部定理数量不作为整核完成标准。
