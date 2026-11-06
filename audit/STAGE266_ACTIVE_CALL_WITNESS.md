# 第266步：同一物理堆上的完整活跃 OSIntExit 调用实例

## 1. 解决哪一个缺口

第265步已有完整调用的生产条件接口，但其任意 fresh saved 分配、running/nesting、调度写入与目标 saved 释放尚未在同一个独立实例中同时成立。本步不增加生产封装，也不改工程登记；只新增 `audit/probes/V293ActiveCallWitnessProbe.v`，直接实例化既有主接口。

主定理 `FWcomplete_active_simulation` 只有 running 字节块的新鲜性条件，结论是框架原有 `ProgSim`，**没有 ProgSim 前提**。函数入口为 `sfexec 114 nil nil`，不是把内层 dispatch 入口改名为完整调用。它连接：

`sfexec → 查找函数 → 任意 fresh Tint32 saved 分配并初始化 → running=true → encrit → nesting 1→0 / lock=0 → OS_SchedNew 完整调用及局部释放 → 目标指针写入 → 优先级不同 → 计数增加 → 优先级复制 → switch → 目标已有 pending 的 excrit/sret/free → 目标 caller`。

`FWnonvacuous` 再证明这样的 running 块确实存在，且同时拥有所需 typed 分离资源和完整调用模拟，排除用不可能的入口条件制造“证明通过”。这仍是特定双任务、终止目标 caller 的实例，不是所有调用方与所有路径的通用结论。本步没有另立一个从完整入口开始的有限全局执行定理；不要把下层有限执行或原 ProgSim 改称该额外结论。

## 2. 同一物理堆与所有分配结果

初始堆是 `QPmemory br 1 1`：旧非空 typed 堆 `CEM`，nesting=1，再分配独立 running 字节并置1。`br` 对原堆新鲜；外层 saved 块 `bs` 对这个入口堆新鲜。证明对**每个**这样的 `bs` 构造资源，而不是选一个好分配。

| 对象 | 位置／初值 | 证明中作用 |
| --- | --- | --- |
| ready bitmap/group/table | 80/81/82 | 从分离资源和实际读取得到唯一 ready 任务，优先级4 |
| lookup/high/target | 92 / 91 / 93 | lookup 全256项；high 初始88，随后4；target 从旧任务写成 ready |
| current cache/counter | 94 / 95 | cache 6→4；32位计数 mone 加1 |
| nesting/lock | 96 / 97 | nesting 1→0；lock=0；实际分支求值 |
| 目标任务 saved | 98 | 已有零值 Tint32，与新外层 saved 分离，目标返回时实际释放 |
| running / 外层 saved | 任意新鲜 br / bs | running=1；外层 saved=0，切出后保留 |
| OSTCBCur | 1 | 指针从旧任务实际写成目标任务 |

`FWbase` 在真正入口全局环境上构造不变式，不假设更换全局环境后整个不变式自动成立。`FWinitial_owned`、`FWentry_frame`、`FWentry_observations` 接通新字节、分配/初始化、nesting 写入和原有输入单元。`FWdispatch_resources` 用实际调度调用、空间更新、复制、当前任务指针写入与 `V293_cpu_release` 构造后续堆。两组资源以同一条 `Mz → Mt → M1 → Mc → Msw → Mret` 链连接。

因此此处不是把几个互不相干的局部样例拼起来，也不是把实际 store/load/free 或最终 caller 模拟重新作为用户需提供的前提。最终 caller 由既有 `SPterminal` 对终止目标任务证明；高层对应调度步由 `HPschedule` 构造。

## 3. 预先约定的对照及其限度

实现前冻结 `audit/logs/stage266-active-call-witness/protocol.json` 及 SHA。`FWpending_contract_control` 只改变任务映射中的目标项：把原有 `RPpending` 换成 `SKIP/kstop`，程序和物理堆不变，证明主接口要求的 pending 等式不再成立。

这是**契约边界对照**，不是一个完整 mutant 程序执行；它只能说明不能照用原接口，不能证明下游机制出错，更不能据此前移验证计数、复制、switch、释放都必不可少。下游正向连接依靠各自真实内存资源证明；没有用早期拒绝替代它们。

## 4. 源码与适用边界

固定源码仍为 uC/OS-II V2.93.01 上游提交 `0c4a48e6fbc6e915714e816196619a5481accf0c` 加原授权修复。OSIntExit 位于固定哈希 `os_core.c:693–736`，OS_SchedNew 位于1751起；逐行锚点与文件哈希见本步 `source-identity.json`。未重新预处理，不提升历史函数覆盖数字。C/config/AST/framework/Inv/LI/BDspec、所有旧证明和测试均不改。

- IE=false，目标保存栈顶=false，沿用 ADR-0005 和 ADR-0010；不是原始外部 port/ABI/硬件精化。
- 目标 pending 已经存在；本步没有证明它如何由前次调用安装。
- 切出任务仍挂起；其外层 saved 和 pending 保留，未证明再次调度或旧任务返回，不承诺公平性。
- typed high=88，但固定最低优先级为12。该 typed 资源实例不是完整全局 Inv，不是初始化可达证据。
- 此处是完整归一化函数**特定活跃路径**的独立调用实例，不是所有路径 OSIntExit，不是任意 client 调用桥接，不是完整中断返回，不是 `WFInt`，不是 `GOOD_OS`。
- K1–K4 未闭合，uCOS3 未开始，未提交／推送。

## 5. 验证与当前仓库状态

稳定重复编译、逐根 Print Assumptions、递归 coqchk 和构建串行执行；信任检查期间禁止编辑任何 Coq 输入。新增5项 Python 回归核查来源/接口/边界，不替代内核证明。失败编译（含两次终止的过度展开）快照均保留。

全量测试必须对比第265步的**具体失败/错误 ID 和顺序**，不能只比较数量；不改旧测试、旧冻结证据来造通过。`make audit` 的旧函数证据身份过期与框架旧空白检查分别保留其真实状态。中文入口只前插本步说明，旧尾部不改。局部检查点不等于全仓通过。

实测数值和清理记录见下节。下一步优先把本实例接入真正共享 Inv/初始化与更一般 caller，并处理已有 pending 的来源及切出旧任务的恢复义务；保持源码级 GOOD_OS / K1–K4 为最终目标。

## 6. 实测结果

| 检查 | 本步实测 |
| --- | --- |
| 稳定编译 | probe37 / stable-probe，源码 SHA 一致，无证明占位 |
| 信任检查 | 11个独立证明根，递归 coqchk 通过；755项 Coq 输入检查期间未改 |
| 根假设 | 仅既有 classic / functional_extensionality_dep |
| 构建／项目审计 | 通过；340个活动 V293 文件、103个框架/策略文件；本步不新增生产文件 |
| 接口／新增回归 | 既有主接口5项、新增5项均通过 |
| 全量测试 | 2495项；429失败、1错误；与第265步失败/错误 ID 及顺序完全一致，无新增或删除 |
| make audit | 退出2：旧函数证据输入身份过期，未重写冻结门 |
| git diff --check | 退出2：既有 inferules.v:581–586 空白，未改框架 |
| 旧输入差分 | 2207项，仅 README/状态文档前插说明；旧尾部、工程与依赖登记不变 |
| 编译诊断保留 | 38份快照，其中30份非零退出，含probe26/probe28终止记录 |
| 清理 | 逐路径/大小/SHA确认后删除8项一次性驱动/缓存备份，共709595字节；既有缓存恢复原哈希 |

旧265检查点在开始前通过，本步中文入口前插后拒绝当前文档身份；原始前后日志保留，旧检查点/manifest 不改。完整证据见本步 verification.json / checkpoint.py；局部检查点通过不表示全仓通过。失败快照、源码、日志、可复用 Coq 产物及既有用户数据保留。
