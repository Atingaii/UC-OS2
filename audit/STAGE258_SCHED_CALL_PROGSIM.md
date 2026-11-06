# 第258步：OS_SchedNew 完整调用的条件 ProgSim

## 从上一步推进了什么

第257步的入口定理要求每一个合法新鲜块上的实际函数体 `ProgSim`；这是公开但未完成的函数体义务。本步独立证明两次实际赋值、返回、释放局部字节和恢复 caller 环境，并将其与原入口定理组合。稳定接口是 `V293_sched_call_progsim`。

```text
实际 scall → 保存 caller、清空局部环境 → 分配 Undef 字节 y
 → 读 unmap/group 得到 y → 读 unmap/rows/y 得到最高优先级
 → 写 OSPrioHighRdy → sret → free y → 恢复 caller → SKIP/caller 续体
```

现在只要求**返回后的 caller 后续模拟**，不再把 `forall b, fresh M b -> ProgSim body ...` 作为调用定理的前提。这是完整 `OS_SchedNew` 调用的条件组合定理，仍不是完整 `OS_Sched`、`OSIntExit` 或整核的无条件正确性证明。

## 固定源码身份

沿用配置后 `OS_SchedNew`，定位 `csrc/upstream/v2.93.01/checkout/Source/os_core.c:1751–1758`，完整文件 SHA-256 为 `96eef5dc1a519887499cffd8f9a6c8873b96978ed9646c42e52eb6992422fea5`。配置为 `OS_LOWEST_PRIO = 12u`，使用 `OS_LOWEST_PRIO <= 63u` 分支：唯一局部 y、两次赋值、void 返回；沿用既有 `V293OSSchedNew.v`，没有重新生成或改写 AST。源码、配置及冻结清单哈希逐项与第257步相同，记录于 `source-identity.json`，本步未重跑预处理器。

## 生产证明的关键义务

| 接口 | 实际检查的义务 |
| --- | --- |
| `V293_assign_byte_progsim` | 原表达式求值、地址和类型、真实 store；唯一 store 后继而非挑选轨迹 |
| `V293_sched_updates_progsim` | 两次实际表达式求值及赋值；第一次写入后仍可读 ready 表 |
| `V293_sched_storage` | 对所有合法新鲜块，释放后的**整个堆**等于只改最高优先级的原堆 |
| `V293_free_one_successor` / `V293_free_end_successor` | 分别分类原 free 与恢复 caller 的全部 cstep 后继 |
| `V293_sched_return_progsim` | 真实 sret、free、恢复局部环境；使用第257步的原全局后继族桥接 |
| `V293_sched_body_progsim` | 任意 fresh 块下的函数体、释放、返回组合；从实际读取得到不别名条件 |
| `V293_sched_call_progsim` | 入口与函数体组合；只保留 caller 端点条件 |

原分配不是唯一后继：这里没有重新假设唯一分配。每一个合法新鲜块均被覆盖；局部块地址可以不同，真正释放以后最终完整堆相等。局部环境恢复来自真实 `sfreeend_step`，而不是跳过返回或把 callee 环境视作 caller。初始局部字节仍为 Undef，没有插入初始化存储。

## 独立实例与对照

沿用原 `CEM = CGmemory OwnershipWaiting true 0 0`、实际代码绑定、非空 `HPpending` 和原 typed 所有权。原 ready 数据为 lo=16、hi=0、group=1，原最高优先级字节为88，计算后为4。这里 typed 只指实际字节类型和空间所有权，不是完整全局 Inv；旧输出88超过当前最低优先级12，因此该对照不是从生产初始化可达的整核状态见证。生产定理允许任意可写旧字节，实例只检验调用、计算与堆机制。

- `CFinput` 从空间所有权、子堆读取和 decoder 查询推出实际读取条件，不靠展开整个堆求值。
- `CFactual_call` 实例化原 `ProgSim`，仍公开 caller 后续模拟条件。
- `CFall_fresh_complete_execution` **没有任何 ProgSim 前提**，对每一个合法新鲜块独立执行原完整调用；它是可执行性见证，不替代生产定理的全后继证明。
- `CFall_fresh_return` 独立执行返回和释放；caller 原变量120恢复，callee 变量104不泄露到 caller。
- 只改变新鲜块：`CFfresh_choices_same_return` 得到相同完整返回堆。
- 只省略输出写入：`CFomit_high_rejected` 通过原88与目标4反驳原堆等于最终堆。
- 只省略局部释放：`CFomit_free_rejected` 保留正确输出4，但新鲜局部字节仍存在，完整堆不同。

后两项是固定实际堆表达式的单因素对照，**不是修改后程序的完整执行消融**，也不能推出任意 client 可观测差异。它们仅证明两个操作对这里的最终堆契约不可省略；没有从早期拒绝推断下游机制全部正确。

## 边界和未完成目标

- IE=false；高层零步停顿，要求当前任务匹配。没有证明中断开启下任意交错。
- caller 后续模拟仍是前提；实例执行见证不能消除这个模拟义务，也不能据此声称任意 client 正确。
- 不是完整 `OS_Sched`／`OSIntExit` 的组合；尚未将返回端点接入 Exit 后续比较、切换、被挂起任务恢复、退出临界区及完整中断返回。
- 沿用 ADR-0010 的源码级切换抽象；不声称原外部端口实现的 refinement。
- 不是 `WFInt`，不是 `GOOD_OS`；K1–K4 未闭合，uCOS3 未开始。
- 不改原 C/config/AST/framework、旧 Inv/LI/BDspec、旧证明、测试和冻结证据。未提交／推送。

下一步应从统一 caller 返回端点构造 Exit 真实后续模拟，把调度调用和既有 dispatch 接通，而不是再增加一个固定局部地址的运行例子。整个阶段一仍须完成源码级 GOOD_OS；随后才按老师要求推进 uCOS3。

## 证据与复查

日志目录：`audit/logs/stage258-sched-call-progsim/`。协议先于实现冻结，保留所有失败和最终源码快照。具体结果见 `verification.json`；局部检查通过不等于全仓通过，历史覆盖向量不作为本步重新验收结果。

编译调试中，直接展开原空间堆导致昂贵计算，改用所有权/包含引理；一次剩余目标误判通过输出实际目标定位，没有改变定理结论。最终实例的完整执行定理在 Qed 的转换检查仍约需44–50秒，未为了缩短检查而删去该独立见证。

## 本步实测结果

| 检查 | 结果 |
| --- | --- |
| 生产／独立实例证明根 | 8／9；两份最终源码均重复编译通过 |
| 逐根假设／递归 coqchk | 17 根通过；检查期间741个 Coq 输入／项目登记保持不变 |
| 信任边界 | 仅既有经典逻辑与依赖函数外延性，没有增加证明空洞 |
| 正常增量构建／project-audit | 通过／通过；活动目标证明文件334份；不是全量 clean build |
| 本步5项测试 | 全部通过；清理后再次通过 |
| 全量测试 | 2455项，428 failures、1 error；全仓未通过 |
| 与第257步差分 | 新增5项通过；原失败及 error 列表完全相同、失败顺序不变 |
| make audit | 仍因函数证据输入身份过期失败，未刷新旧证据制造通过 |
| git diff --check | 仍为旧 inferules.v 第581–586行六处空白；框架未改 |

核对1303个既有输入，仅 README、状态说明、项目登记和生成依赖四处获准前向追加。生成依赖仅新增当前生产模块的三行，剔除后旧内容逐字节不变。前步冻结 manifest 在当前快照上恰好这四处身份改变；旧检查点实际失败日志保留，未重写旧 manifest。

保留20次编译尝试的日志和源码快照（含15次失败／中断），保留所有回归与信任检查证据。逐项确认并校验后清理本步8项一次性信任驱动／产物与缓存备份，共708668字节；原 `.lia.cache`、`.nia.cache` 已恢复，源文件、失败材料及可复用编译依赖保留。
