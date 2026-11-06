# 第180步：原时间 API 的真实调用、函数体与返回

## 先用直白的话说明

第179步只把函数调用推进到入口：局部内存已经分配，setter 的实参也真的写入了参数槽，但函数还没有运行完。本步接着**同一次实际调用产生的内存**，执行原函数体并返回。不是另外造一个满足结果的状态。

| 环节 | getter：OSTimeGet | setter：OSTimeSet |
| --- | --- | --- |
| 起点 | 原 TRmemory，无 API 局部块 | 完全相同的旧堆结构，无 API 局部块 |
| 调用准备 | 真正分配 ticks、saved | 真正求值实参 n、分配并写参数，再分配 saved |
| 初始化 | 实际执行 saved=0 | 实际执行 saved=0 |
| 临界区内 | 从实际全局时钟槽读取到 ticks | 从实际参数槽读取并写入全局时钟槽 |
| 退出临界区 | 恢复进入前的中断快照 | 恢复进入前的中断快照 |
| 返回 | 实际读取 ticks，返回 clock | 返回 None |
| 局部内存 | 两个局部块各4字节均释放 | 两个局部块各4字节均释放 |
| 调用者 | 恢复原 caller 环境和 continuation | 同样恢复 |
| 其他物理字节 | 所有非局部块保持 | 除时钟块及两个局部块外全部保持 |

这是 Coq 中一条**无中断交错的有限执行路径**的存在性证明，不是全部并发执行正确性，不是原生端口／机器码正确性，也不是最终 GOOD_OS。

## 源码和不变的对象

- 固定 V2.93.01 上游提交、配置、两类授权修复不变。
- `csrc/upstream/v2.93.01/checkout/Source/os_time.c`，getter 237–250 行，setter 267–278 行；整文件与两个函数片段哈希在 `logs/stage180-time-api-lifecycle/source-check.json`，最终重新计算而非只比较旧报告。
- 使用既有 `V293_TimeGet_body`／`V293_TimeSet_body`，不修改 AST。`encrit`／`excrit` 仍为 ADR0005 的框架规范化，**不是新增真实 CPU 端口实现**。
- 探针继续用 `Cprogram = pumerge RAapi RAinternal`、JGE、JLE、TRmemory、TRabstract、Ccore、JgetPre／JsetPre；不换 Spec、Inv 或 LocalInv，不重新定义全程序。
- 不修改旧证明、旧测试、C／配置、框架、tactics、冻结证据和函数覆盖信用。

## 生产稳定接口

`certiucos/v293/proofs/V293TimeAPILifecycle.v`：

1. `V293_time_cell_store`：从真实可写所有权构造 store 和更新后的命名单元。不是把 store 成功当作前提。
2. `V293_time_local_layout`：真实 callee 环境恰好枚举两个局部地址，处理名称排序差异。
3. `V293_time_locals_return`：由这两个局部槽的可写权限构造真实释放、返回和 caller 恢复，同时给出逐字节消失／不变事实；不假定 free 或终点存在。
4. `V293_time_body_prefix`：两份原 AST 共用的 saved=0、进入临界区、复制、退出临界区。复制求值由实际槽所有权推导，不接受 evalval oracle。
5. `V293_time_get_body_return`、`V293_time_set_body_return`：完整原 body 到返回的接口；量化 P、caller、continuation、原堆、中断开关和栈、地址、值及空间 frame R。

中间 Mc 上的更新所有权与两次真实 store 暴露给上层；最终 Mf 的局部释放／非局部字节保持由实际返回步骤得出。R 在已有 callee 环境和原 aux 中评价；未宣称任意 R 在关闭中断的中间状态或切回 caller 后都可直接运输。

## 连接和事先确定的对照

`audit/probes/V293TimeAPILifecycleProbe.v`：

- `Lget_actual_lifecycle`／`Lset_actual_lifecycle`：从未分配局部块的 TRmemory 开始，执行第179步的实际调用准备；同一实际 Ma 满足 Ccore 与精确 caller pre，再从这个 Ma 进入原 body，最后真实返回 Mf。
- setter 的参数 load 在 **Ma** 检查；最终该槽已经释放，不能再宣称它持有 n。
- `Lset_two_argument_control`：初始机器状态、函数、环境和旧 clock 不变，只改源实参 n→bad。两次调用各自读到其真实参数、写出对应新时钟；bad 端点对旧 n 的时钟 load 被物理字节独立排除。不是 action 守卫早拒，也没有把一个成功端点复制改标签。
- `Lget_caller_shadow_control`：caller 的 ticks 与 callee 同名，但 caller 指向150、callee 指向160。完整返回后实际 caller 表达式读到150中的 clock，而160／161真实释放。不是仅把 caller 保存到 kcall。
- 两个生命周期定理均逐字节证明非修改块保持；生产接口还保留任意初始 IE／si／ci。探针的具体机器快照仍是 empisr／true／空栈，未声称覆盖实际 ISR 交错。

协议先于实现冻结于 `protocol.json`。四项控制的“保持不变／仅改变因素／可观察结果”见协议及上述定理；不把局部值检查通过算作抽象协议、ISR 或下游全程序环境有效。

## 对抗式复核与明确边界

| 怀疑／反例方向 | 处理 |
| --- | --- |
| 是不是独立拼一份合法终点？ | Ma 来自真实 call／alloc，body 从同一 Ma 开始，Mf 由实际 store／free／return 构造。 |
| 参数错了只是 action 拦住？ | 对照不使用 Jstate 作为负控条件；直接比较最终物理 clock load。 |
| free 是否偷偷删了 caller 同名块？ | callee getaddr 精确枚举160／161；caller 的150保持并实际求值。 |
| 返回值只是规格指定？ | getter 先实际复制，再从真实 ticks 求值，执行 srete 和返回步骤。 |
| 退出临界区是否只检查最终开关？ | 生产 trace 的入口／出口是相同 enabled、si、ci，包含进入与退出原语。 |
| 保留物理字节就等于强 Inv 恢复？ | **不等于。** 本探针把剩余资源投影到 Atrue，用逐字节 frame 检查实际机器存储；生产 body 接口仍量化 R。未证明整个最终强 Inv。 |
| setter 抽象时钟是否同步更新？ | loststep 不含抽象 action；本步 TRabstract 仍为旧 clock，不把新物理值冒充已完成抽象模拟。 |
| 有一条成功路径就证明并发 API 全正确？ | **不能。** 已有第177步 body Hoare 契约仍有效，但与本步有限 trace 不能自动拼成全程序并发模拟。 |

尚缺：抽象 action 与实际执行的同步连接、生产 LocalInv／完整函数环境、全局初始化、tick／hook／ISR 连接和同一最终程序上的 K1–K4。六阶段信用继续 `94 / 1 / 1 / 1 / 1 / 0`，无新增无条件整函数信用。

第一阶段整个源码级 GOOD_OS **未完成**；第二阶段 uCOS3 **未开始**；总目标 active。本步不是提交／推送操作。

## 验证入口

- `logs/stage180-time-api-lifecycle/stable-compiles.json`：最终源码对应的编译快照和子进程退出码；包装脚本自身返回0不代替 coqc 成功。
- `trust.json`：两新入口及递归依赖 coqchk、所有新增定理根的实际假设闭包；不是把全部历史入口重新检查一遍。
- `baseline-tests.json`、`full-tests.json`、`full-tests-final.json`：新增5项回归与两次全套结果，比较全部旧失败／错误 ID，不以只比数量替代。
- `verification.json`：最终旧文件、源码、原证据链、编译、构建、测试、清理与边界汇总。
- `checkpoint-evidence-manifest.json`：本步证据与交付表面冻结清单；失败日志、快照和诊断始终保留。

下一步优先把实际执行和抽象 action／返回资源连接到同一规格，再收敛生产 LocalInv 与全程序义务，不重复把已完成的 call-body-return 存在性当成新进展。

### 已完成的机器检查

- 生产 `body09`、探针 `probe11` 稳定编译成功；14个新增根的实际假设仅沿用 classic 和 functional_extensionality_dep，没有扩大旧允许集合。
- 两个新入口及递归依赖 coqchk 通过（约299.52秒）；检查期间575份 Coq 输入不变。
- 新增5项回归通过；`make build` 与 project-audit 通过。
- `make audit` 仍因旧 function evidence input identity 过期失败；`git diff --check` 仍报告既有 inferules.v 第581–586行六处空白问题。不重写冻结证据或更改门来消除失败。
- 全套从2058项增至2063项，仍为旧423失败／1错误；已比较完整失败与错误ID，未新增或替换失败。最终文档状态下再跑一次，结果由 full-tests-final.json 和 verification.json 核对。
