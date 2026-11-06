# 第139步：原调度分支、计数器与实际切换同码同内存连接

## 本步解决什么

第138步在同一份 Mtarget 内存上证明调用／目标赋值和真实 switch，但片段终点为 SKIP，switch 代码另作前提；原优先级分支和计数器还未接到这条控制流。本步保留真实源码的分支，补上这个缺口，不改 C、配置、既有手工 AST、框架或 tactics，也不是 C 修复。

固定目标仍为 uC/OS-II V2.93.01，上游提交 `0c4a48e6fbc6e915714e816196619a5481accf0c`。`Source/os_core.c` 第1702行起的原 `OS_Sched` 在两个锁定检查之后执行：

```c
OS_SchedNew();
OSTCBHighRdy = OSTCBPrioTbl[OSPrioHighRdy];
if (OSPrioHighRdy != OSPrioCur) {
    OSCtxSwCtr++;
    OS_TASK_SW();
}
```

这是固定配置后的相关片段，不是全文。源码／模型身份和依赖哈希见 `audit/logs/stage139-ready-source-tail/source-identity-check.json`。只主张既有手工 AST 的对应关系，不声称已有经过证明的自动 C 前端。

## 证明接口

生产文件 `certiucos/v293/proofs/V293ReadySourceTail.v` 共3个证明根，稳定上层接口为 `V293_ready_source_dispatch`：

1. 从同一 ready Inv 和真实 high／cache 两字节，执行**原优先级字节比较**，没有换成 TCB 指针比较。
2. 相等则直接结束；不等则从 counter 的完整所有权构造实际成功 store，执行原计数器赋值。成功 store 是结论，不是调用者提供的 oracle；不加“计数器不溢出”前提。
3. 在原 `OS_SchedNew` 的 continuation 中放入原目标赋值及尾段，构造从实际调用、局部分配、选择、返回、释放、目标写入到分支／计数器的**连续 cstepstar**。不等路径停在确切 `sprim (switch target)`，而非先停 SKIP 再额外假设另一段 switch 代码。
4. 高优先级／目标／cache／counter 与同一 Inv、原 frame 保留；counter 四字节外内存不变。任意额外 R 仍限 `GoodInvAsrt`；目标不作为跨任务恢复的私有 frame 保存。

探针 `audit/probes/V293ReadySourceTailProbe.v` 共9个证明根，以真实非空 ready＋waiting TCB、就绪位图、优先级表、只读 lookup、调用者 canary、输出单元构造联合入口；不把独立 load 或成功 store 当成执行前提。

- `STjoint_source_tail` 覆盖实际两个字节分支，包括 `UINT32_MAX + 1 = 0`。相等路径 counter 仍为 UINT32_MAX；不等路径真实 counter store 为零。
- `STjoint_source_switch` 将上述终点的**同码同内存**直接用于原 `pswitch_step`，实际 current 指针改为 Ready，ghost current 同步，任务记录、就绪资源及即时 frame 保留。这里仍是 `cstepstar + lpstep` 的混合执行，**不是全局 lpstep 闭包**，也不是完整 `OS_Sched`。
- `STjoint_no_switch` 给出入口 current=Ready、cache=4 的自然一致路径；原分支不切换，计数器不变。

## 单因素检查与没有解决的同步义务

`STcache_only_control` 固定 current、TCB、位图、表、目标、counter 和权限，只把地址 `(94,0)` 的 cache 单字节6改为4；其余全部地址的真实内存完全相同。这个**单因素**对照检查原分支确实读取实际缓存；它可能破坏 cache／task **一致性**，不是两条自然一致运行轨迹的比较。两条自然一致入口分别由 `STcoherent_current` 检查，不把同时改变 current 的对照称为单因素。

本步还在同一条实际调用／分支／计数器／切换路径上保留并加强了负结果：初始 Waiting 的实际优先级6与 cache=6 一致，切换后真实 current 指向优先级4的 Ready，但 cache 仍为6；`V293_current_task ... Ready 6` 被 Coq 排除。原框架 switch 只写 current，不写 `OSPrioCur`。有限 ready Inv 没有包含该缓存一致性，因此它保留并不代表所需全局一致性已经成立。不能用删掉不利结论、改比较条件、削弱门槛或擅改 C 来“修复”这项义务；需要继续接通源码级端口同步边界。

## 验证及证据

证据目录：`audit/logs/stage139-ready-source-tail/`。

- 生产与探针各有独立编译日志、源码快照及哈希；稳定标签由 `stable-compiles.json` 指向。失败尝试也保留，不覆盖。
- 12个根的逐项 `Print Assumptions` 及305个活动模块和25个额外探针的 `coqchk` 已通过。实际结果见 `trust.json`；实际假设仅与上一阶段相同的 classic 和 functional_extensionality_dep，不扩大已有框架假设白名单。
- 新增8项结构／证据身份回归全部通过；清理前后全量均为1805项，保留原423失败／1错误，逐项比较精确**失败 ID 集合**和错误 ID，不只比较数量。实测以 `post-cleanup-tests.json` 和 `checkpoint-report.json` 为准，未通过不得记为通过。旧423失败／1错误中仍存在共同的过期身份提前拒绝；ID不变只说明没有新增可见失败，不能据此认定这些旧门禁之后的每个机制已重新通过。本步新片段的语义信用来自独立 Coq 根检查，而不是旧提前拒绝。
- 六阶段覆盖保持 `94/1/1/1/1/0`，不给 `OS_Sched` 整函数信用。`make audit` 的旧证据身份过期错误和 `framework/logic/inferules.v` 581–586 的旧空白问题均保留。
- 收尾先逐项确认一次性 Trust 编译文件和两份缓存备份，再恢复原 lia／nia 缓存并删除一次性材料；源码、可复用 Coq 产品和失败证据保留。结果见 `cleanup.json`。

## 边界与下一步

这是无交错存在性片段执行；**不是生产全局语义 Inv**，没有证明初始化可达性、所有交错或所有分配选择。未连接 `OS_Sched` 的中断／锁定 guards、临界区进出、任务恢复后的栈／Hook、活动 ISR、完整 API 与 `WFIFun`。端口 cache 同步和片段到全局语义的提升仍开放。

`GOOD_OS` 和同程序 `K1–K4` 尚未完成；**uCOS3 未开始**，总目标保持 active。下一步先沿真实端口边界处理 `OSPrioCur` 同步，并将连续片段提升接入全局任务语义，不另外发明调度器。未提交／推送；历史冻结证据不改写。
