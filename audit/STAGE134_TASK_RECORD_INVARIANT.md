# 第134步：让可实例化 GoodI 拥有同一任务映射的真实 TCB 字节

## 本步解决什么

第131步已证明：只有物理资源、却不拥有抽象槽的具体池 Inv 不能满足框架 GoodI。第132～133步也没有把初始化后的 NULL current 偷换成已创建任务。本步另行补上运行期接口的一块必要拼图：在已有四槽共享不变式中，分离拥有**同一抽象任务映射**的物理 TCB 字段，并证明该有限记录不变式的 GoodI。

`GoodI` 是框架对中断不变式和任务切换接口的适用性条件，不等于整个操作系统正确性。本步没有把新 Inv 宣称为最终生产全局 Inv，也没有把独立字节实例宣称为初始化可达状态。

## 定义和稳定接口

生产文件：`certiucos/v293/proofs/V293TaskRecordInvariant.v`。

- `V293_records_core`：存在 current、tasks、events、time，拥有实际 current 指针的半权限、四个抽象槽，以及 tasks 中每项对应的已选 TCB 字段；不是“任意物理表加任意抽象表”。
- `V293_records_inv`：0号槽为上述核心，其余槽为空；复用既有 `V293_scheduler` 和空 `V293_shared_li`。
- `V293_records_invariant_good`：闭合的 `GoodI V293_records_inv V293_scheduler V293_shared_li`，不接收假设式 GoodI 参数。
- `V293_records_store`：真实 current store 和对应 ghost current 更新后，新 SWINVt 仍成立；所有任务记录资源原样保留。
- `V293_records_switch_sound`：即使有任意 caller frame，从 SWINVt 提取的是**调用者完整实际内存**与其自己拥有的同一 tasks 映射的 `V293_task_records`，不是另选一份好内存。

先证明原字段所有权的精确性和非资源上下文稳定性；精确性复用既有 `V293_storage_precise`，不新增精确性公理。相同上层抽象资源强制四个存在见证一致；优先级范围与表示单射消除数值见证差异；pend 值不同不改变记录的类型足迹。

字段范围沿用 `V293TaskRecordOwnership`：优先级及其索引／mask、消息、状态；等待任务还包含所需 delay、pend、event 字段。不包含整个 TCB、空闲池、活动链或者所有内核对象。

## 非空正例：两条任务记录、两种 current

探针：`audit/probes/V293TaskRecordInvariantProbe.v`。

复用已独立编码的 literal fixture，不从本步 GoodI 结论反推入口：

| 对象 | 实际地址 | 抽象状态 |
|---|---|---|
| ready 任务 | block60，offset0 | 优先级4，rdy，消息NULL |
| waiting 任务 | block41，offset8 | 优先级6，等待 semaphore(block72,offset5)，delay=1，消息(block120,offset7) |
| current 指针 | block1，offset0 | 完整写权限 |

`RIliteral_spatial` 证明同一份指针＋记录字节确实满足新 SWINVt。`RIswitch_cases` 保持同一非空任务映射：live=true 时 current 是 waiting 成员，live=false 时 current 是不在表中的 block999；两者都选真正的最高 ready 任务 block60，并存在真实 current 指针 store。更新后的实际返回内存满足新 SWINVt 与同一任务映射的记录关系；所有非 block1 字节保持不变。

这里的“死 current”只指不在抽象任务映射中，不意味着完整删除流程已经验证。空 LocalInv 使 GoodI 的局部回收分支可实例化，不能推广为真实私有任务资源回收。

## 预先规定的单因素消融

协议在实现前写入 `audit/logs/stage134-task-record-invariant/protocol.json`。

对同一正例的 ready 优先级物理字节 `(60,50)` 做一次框架真实 `store Tint8`：4改为5。**抽象映射仍为优先级4，current、其余字节、权限、事件映射、时间和程序不变。**

`RIone_byte_ablation` 同时检查：

1. 原内存满足新记录 SWINVt，也满足弱四槽共享 SWINVt＋Atrue；
2. 实际 store 成功，目标字节由4读成5，其他全部地址的 get 不变；
3. 修改后，原弱四槽共享 SWINVt＋Atrue **仍可满足**；
4. 修改后，无论选择什么 current 和 caller frame，新记录 SWINVt 都不能成立：它会要求同一实际字节仍为4。

因此被检验的差异确实是“抽象 tasks 与实际记录字节的耦合”，不是缺少指针绑定、只读权限或早期路径拒绝。该实验不为 ready bitmap、表、Hook、初始化或任何下游机制授予信用。

## 可信检查与复现

```bash
make build COQBIN=/data/home/lucentzhou/.opam/default/bin/
PYTHONDONTWRITEBYTECODE=1 python3 -B -m unittest discover -s tests -p test_task_record_invariant.py -v
PYTHONDONTWRITEBYTECODE=1 python3 -B audit/logs/stage134-task-record-invariant/verify-checkpoint.py
```

本步稳定源码、每次编译结果及失败快照均保留。探针复用旧 `V293TaskRecordOwnershipProbe`；其源文件不改，仅补编译已有依赖。生产模块不依赖 audit。

最终实测以本步 `checkpoint-report.json`、`verification.json`、`trust.json` 和原始命令日志为准；本页不以预期替代实测。新增8项结构／证据回归不能替代 Coq 语义证明。全量回归应保留原423失败／1错误，并逐项比较失败 ID 集合，而不是只比数量。旧审计的 stale function evidence input identity 及原框架 whitespace 问题均保留，不改旧证据制造通过。

## 尚未完成，下一步如何接回主线

本步是**可实例化的有限任务记录不变式**，不是生产全局语义 Inv：

- 没有 ready bitmap／优先级表与同一任务映射的联合语义约束；最高 ready 是本探针对抽象映射证明的事实，不是从实际 bitmap 运行推出的完整调度证明。
- 没有有限 TCB 池／活动链／空闲链精确分区及任务创建、删除保持性。
- 没有真实初始化建立该 Inv，不能将三次初始化后的 current=NULL 当作它的入口；首个实际 TCB 调用仍停在第133步已定位的真实 Hook。
- 没有 Hook／栈初始化实现、WFIFun、活动 ISR、整函数联合前提或完整 OSTaskCreateExt 成功证明。
- 没有 `initst` 到最终 `GOOD_OS`，没有同程序 K1–K4；uCOS3 未开始，总目标仍 active。

下一步应把同一任务映射的 ready bitmap／优先级表关系接入该可实例化接口，并与已有初始化／任务创建字节入口会合；不能继续用相互独立的表、bitmap、记录见证拼装“全局已证明”。六门覆盖仍为94/1/1/1/1/0，不新增完整函数或整核覆盖信用。

## 本步实测与反向审查

- 稳定生产编译 `proof13`、探针编译 `probe13` 均退出0，输入／结束源码哈希一致。
- 31个新证明根的假设检查通过；依赖仅使用原框架已接受的 classic、functional_extensionality_dep。300个活动模块（197个目标模块＋103个框架／tactics模块）及20个附加探针根模块的完整 `coqchk` 退出0。
- 构建通过，新增8项回归通过；全量1765项仍为原423失败／1错误，失败和错误 ID 集合均无增减。不是全量测试绿色。
- `make audit` 仍退出2，原因仍是 stale function evidence input identity；`git diff --check` 仍只报告既有 inferules.v 第581～586行问题。本步不修改它们。

| 审查反对意见 | 本步证据或明确限制 |
|---|---|
| GoodI 可能只对空任务表成立 | ready 与 semaphore waiting 两个实际记录，共用同一非空映射，两个 current 成员性分支都有真实 store |
| 记录关系可能只对应另选的好内存 | switch_sound 输出 caller 的 getmem；单字节破坏后，对所有 current／frame 都拒绝 |
| 拒绝可能来自缺少权限或 current 绑定 | 原入口有完整写权限，真实 store 成功；修改后的同一状态仍满足弱共享 SWINVt |
| 两条记录可能冒充整个内核 | 只证明已选字段与有限记录接口；bitmap／表／资源池、初始化和 API／ISR 保持不在本步结论中 |
| 独立 fixture 可能被当作初始化可达性 | 明确没有此连接，真实首TCB调用缺少 Hook 的证据仍保留 |

清理、旧文件逐项复核与最终冻结结果见 `cleanup.json` 和 `verification.json`。失败编译快照、可复用编译产物、旧证据和用户文件保留；仅清理本步一次性信任检查产物并恢复原缓存。
