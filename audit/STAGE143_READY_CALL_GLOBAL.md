# 第143步：真实调度调用接入原全局执行语义

## 本步补什么

第142步完成原局部调用、分配、初始化、返回与释放；切换证据仍是局部前缀加一个全局步。本步复用同一完整调度函数 AST、ready＋waiting 非空实例及原 `loststep`／`lpstep`，将真实 `sfexec` 到返回或切换接成既有 `V293_global_steps` 闭包；不增加转移规则，不另加虚构的外层函数。

`sfexec` 是原 OS 执行边界，**不是 client 侧 scall**。本步没有证明 client 与 OS 两侧共享同一内存，也没有将 client 的 `scall` 混入 OS 内存轨迹。

## 从入口到实际结果

- `V293_sched_global_enter`：实际 OS 函数绑定，保存 caller 环境，清空 callee 环境，原分配四字节 `cpu_sr`，原初始化后进入临界区控制体。任意真正 fresh 的地址和成功初始化均可使用该接口。
- `FGenter`：复用第142步原 `free`／whole-block freshness／`allocb`／`store` 的精确重建，不预先假设 caller 已拥有 callee 局部对象；原 fixture 的 block 98 在调用前全空。
- `FGno_switch`：同一非空实例从实际 `sfexec` 连续执行至 `SKIP/kstop`。原 `sret`／`sfree`／`sfreeend` 释放四字节并恢复 `RTle`；两种 IE 和任意外层 critical stack 均原样恢复。目标实际 load 为 Ready4，counter 为原 UINT32_MAX，cache 为4。
- `FGblocked`：对任意合法非零 interrupt／lock guard，连续全局返回，caller 内存精确为原 `Mbase`，不是任意另选的终态堆。
- `FGswitch`：从同一实际入口连续执行至原真实 `switch` 及其全局后态；共享同一 `Mtail`，原 typed store 写入 current，得到 Ready4、counter 回绕0、cache6。旧 Waiting6 任务仍持有原 `cpu_sr`、真实调用帧与待执行 `excrit; sret`；旧任务 aux 保存 critical stack，新任务 aux 不被修改。这仍未恢复旧任务。

归类由真实函数绑定／真实 `kcall` 推出；通用单步提升接口明示单步 `InOS`，完整调用接口不要求调用者逐步提供分类 oracle。内存、局部环境、ir、aux 都使用原规则所得值，而非只更新任务 ghost 状态。

## 单因素对照：最后一次环境恢复

预先协议见 `audit/logs/stage143-ready-call-global/protocol.json`。

`FGno_switch_free` 先把原正例运行到已释放 `cpu_sr`、尚未恢复 caller 的最后边界。`FGrestore_ablation` 仅改变最后行政性调用帧保存的环境：从应恢复的 `RTle` 改为 callee 的 `CGle`。代码 `sfree nil None`、当前环境、已经释放的同一堆、ir、aux、函数绑定、其余 continuation 全部不变。

正反后缀均通过原全局 `sfreeend` 实际返回，并具有相同堆和 aux；没有依靠共同早期拒绝。正例恢复调用者已有的104号绑定，负例丢失它，且机器证明两环境不同；两侧 `cpu_sr` 四字节均已清空。因此该实验隔离的是环境恢复，不重复把内存释放的作用算成新贡献。

这是动态行政性调用帧故障，不是 C 源码变体；负例从变异后的返回边界起步，不声称它可从未修改程序的相同入口到达。第142步的独立释放对照仍保留，不改写或替代。

## 验证与未完成边界

新增生产接口7根＋联合探针6根；本步8项 Python 检查只检查接口、注册和证据身份，执行性质由 Coq 证明。独立逐根 `Print Assumptions`、活动模块与额外探针的 `coqchk`、全量构建、前后两次全量测试和清理的实测结果在本步 `checkpoint-report.json`／`verification.json` 中冻结。失败编译快照与日志保留。

这是有限实例的**存在性、无交错**执行，不是所有分配选择、初始化可达性、所有交错、活动 ISR 可达关系或函数 Hoare／`WFIFun`。内存与 ready/TCB 模型仍是既有手工 AST 对应，不新增自动 C 前端结论。通用入口有 fresh／成功 store 条件，联合探针构造了条件，但没有泛化为所有内存状态。

切换后的空间结论使用旧调用者环境，不冒充新任务 `CurLINV`。真实 switch 没有更新 `OSPrioCur`，current Ready4／cache6 的同步缺口仍开放；也没有旧任务恢复、hook／栈或者生产全局语义 Inv 证明。

该缺口的来源需分清：锁定的 `Source/os_core.c:1702` 中 `OS_Sched` 调用 `OS_TASK_SW()`；`csrc/analysis-port/os_cpu.h` 仅把它展开为未实现的 `OSCtxSw()` 声明。不能凭当前抽象 switch 就宣称所有端口效果已经对应。下一步应处理源码级端口契约与已有抽象边界的对应，不擅改冻结 C，也不扩大成汇编或硬件正确性证明。

六门保持 `94/1/1/1/1/0`，不把轨迹存在性记为新整函数信用。全量测试的旧423失败／1错误按**失败 ID 集合和长度**与第142步逐项比对，不以相同计数代替身份校验；原 stale identity 审计失败与旧空白失败仍保留。C／配置／旧 AST／framework／tactics／旧冻结证据不变，README 与状态页只追加本步前缀。

`GOOD_OS` 和同程序 K1–K4 未完成；uCOS3 未开始，总目标保持 active。下一纵向义务是旧任务恢复与 current／cache 的真实端口同步，再接生产不变量、初始化和全程序接口，不将本步结果写成整核验证完成。未提交／推送。
