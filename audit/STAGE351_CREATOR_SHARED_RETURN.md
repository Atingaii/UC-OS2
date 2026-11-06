# 第351步：把运行期创建前缀接到原强共享资源返回

## 这一步解决什么

第350步从已经求值的 `sfexec OS_TCBInit` 开始。本步复用它，不再让上层手工提供中间的物理预留槽现场：从实际 `OSTaskCreateExt` 成功分支前缀出发，执行优先级／中断嵌套检查、预留槽写入，经栈 hook 的返回契约、`psp` 真实赋值及七实参求值，接到相同 TCB 初始化／发布／释放／返回，再执行 `err=0`。

稳定接口是 `V293_OSTaskCreateExt_shared_return_under_hooks`，位于 `certiucos/v293/proofs/V293CreatorSharedReturn.v`。这是局部连续执行与抽象创建的条件式连接，不是整函数 `TaskSim`。

## 资源与任务身份没有换对象

- 入口优先级表该槽为 null，前缀把它改成真实 RESERVED 指针；其余12槽和旧任务记录保留。第350步的逻辑影子仅用于原 canonical 表不变量；没有把物理预留槽假装成 null。
- 到达 `Mbridge` 后才实际选择九个互异、新鲜局部块，并证明它们避开任务记录和返回存活单元。不要求调用者预先给出未知未来堆的新鲜地址，也不要求已分配局部单元。
- `target` 与 `argv` 同时用于实际栈初始化实参、原抽象 `spec_crt` 和客户入口定位；没有独立的抽象入口／参数见证可随意替换。
- 同一个最终物理 `Mf` 上保留原 `V293_shared_ready_records`、TCB 剩余字段、调用者局部字段及用户 frame；原 `hpstep` 实际构造客户参数分配、写入和读回，不把纯 map 更新当执行。

## 单因素对照与实际证明范围

预先冻结的协议只省略 `psp` 返回值赋值。闭合探针 `CSRLiteralEntry` 用编码字节构造入口；`CSRSpatialEntry` 将非空旧任务字段升为原拥有谓词。`CSRStackValueBridge` 在独立的栈返回现场执行真实赋值和七实参求值。`CSRBridgeLoads` 检查返回值、RESERVED 槽和 sentinel=77。`CSRStoreOnlyContrast` 比较同一初始堆：不赋值仍读取 null，不能满足期望的新 `psp`；实际执行后读取新值，同时保留预留槽、旧任务和 sentinel。

该 fixture 是独立的栈返回现场，不是从完整入口证明三个 hook 都可执行；也不给后续 TCB 发布、CPU hook 或抽象 commit 额外信用。候选编译失败不是消融实验结果，原日志与源码快照全部保留。

## 仍未解决的义务

1. 一个栈 hook 返回契约和两个原CPU hook契约仍为前提；本步没有实现或闭合 hook 函数体。两个 CPU 契约需对选择出的任意九个互异块成立。
2. 物理预留槽使用完整可写权限；并未接通 ADR0009 的并发 owner／半权限协议，不能据此宣布并发创建正确。
3. 仍需已有当前任务、`spec_crt`、任务入口定位和客户内存新鲜块等前提；不是冷启动引理。
4. 手工 C 前端、符号化 RESERVED 地址及既有分析 port 边界不变；返回后的调度／错误路径没有在本步执行。
5. 整个 `OSTaskCreateExt` 的 `TaskSim`、`OSInit`、全局 ISR 不变量、具体源码级 `GOOD_OS`、同程序 K1–K4 均未完成；uCOS3 尚未开始。

## 验证与失败保留

本步不修改旧 `.v`、旧测试、固定 C、配置锁或冻结证据。`_CoqProject` 只追加本步生产文件一行；README 与状态仅前置新记录。新增测试不豁免已有失败，必要注册若破坏旧快照同样计入新增失败。

实际编译、逐根假设、递归 `coqchk`、构建、两轮新增／全量回归和清理结果见 `audit/logs/stage351-creator-shared-return/verification.json`。此前全量基线是3057项、450失败、1错误；本步整体是否通过以实测记录为准，不以局部 Coq 成功代替全量成功。未提交、未推送，总目标保持 active。
