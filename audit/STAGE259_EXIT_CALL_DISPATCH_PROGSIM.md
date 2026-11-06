# 第259步：从实际调度调用连接到 Exit 切换的原 ProgSim

## 本步真正消除了什么

第258步停在 OS_SchedNew 返回点，要求 caller 后续模拟；第256步从优先级比较开始。本步连接中间真实的目标指针赋值，随后组合既有比较、计数、复制和 switch 证明。没有把前缀执行轨迹当作全后继模拟，也没有跳过 OSTCBHighRdy 的存储。

```text
真实 OS_SchedNew 调用（全部合法 fresh 分配、计算、释放、恢复 caller）
 → OSTCBHighRdy = OSTCBPrioTbl[OSPrioHighRdy]
 → 比较最高／当前优先级
    ├ 不同：UINT32 计数加一 → trace skip → 优先级复制 → 原 switch
    └ 相同：skip，保留调用／目标更新后的堆
```

稳定接口 `V293_exit_call_dispatch_progsim` 不再要求调用返回点或比较入口的中间 ProgSim，只要求最终切换端点模拟与明确的高层匹配。`V293_exit_call_same_progsim` 处理相等分支，仍要求最终 caller 端点模拟。两者都是条件组合定理，**不是完整 `OS_Sched` 或 OSIntExit 函数证明**。

## 固定源码和抽象边界

沿用固定 V2.93.01、官方提交和 OS_LOWEST_PRIO=12u 配置。OSIntExit 内层语句位于 `csrc/upstream/v2.93.01/checkout/Source/os_core.c:708–724`；OS_SchedNew 为1751–1758行，文件 SHA-256 为 `96eef5dc1a519887499cffd8f9a6c8873b96978ed9646c42e52eb6992422fea5`。8项源码／配置身份逐项与第258步相同，详见 source-identity.json；未重跑预处理器。

直接复用 `V293_exit_boundary_dispatch`，没有新建一个替代 AST。仍沿用 ADR-0010 的源码级端口调用边界：OSIntCtxSw 调用位置映射为优先级复制和框架原 switch。不声称已证明原外部汇编端口实现的 refinement。C/config/AST/framework、Inv/LI/BDspec、旧证明、测试和冻结证据不改。

## 生产接口及公开前提

| 接口 | 已闭合的连接 |
| --- | --- |
| `V293_assign_pointer_progsim` | 原指针赋值的类型、值、地址和真实 store；分类所有存储后继 |
| `V293_sched_target_then_progsim` | 真实调用、返回、目标指针更新，进入实际 caller tail；从类型化指针数组读取推导表达式，不要求复合表达式 oracle |
| `V293_exit_call_dispatch_progsim` | 前缀与实际不同分支全后继组合；消除中间模拟前提，只留最终端点与高层匹配 |
| `V293_exit_call_same_progsim` | 前缀与实际相同分支组合；不执行计数和 switch |

生产仍公开：函数／变量绑定、初始 ready 字节读取、可写 high、数组范围与指针读取、各实际 store、当前任务匹配、最终高层端点及其模拟。它们不是初始化或完整全局不变量的替代证明。区间 IE=false，未证明任意中断交错。全部 fresh 选择的覆盖来自第258步原调用定理，未假设分配唯一。

## 独立实例：消除空前提及不同堆拼接的疑问

`XPscheduled_canonical` 从原 typed `CEM` 独立构造真实调用／目标更新见证。它先用调用的逐字节 frame 性质和 high 的完整写权限，证明返回后**整个堆**恰为第258步统一端点 CFfinal，再把真实目标指针 store 接在这个同一堆上。不是只比较输出数值，也不是把两个不相关的存在堆拼在一起。

`XPtable` 从原空间子堆读取数组第4项得到 Ready 指针；high 写入只改变91号块，不改变82号数组。`XPactual_call_dispatch_simulation` 从同一个原始 CEM 建立完整内层调度区间的原 ProgSim，**没有任何 ProgSim 前提**：实际计数由 mone 回绕到0、实际复制、物理 switch 存储和有限 client 的 HPpost 均独立构造；保留非空 HPpending。它同时保留原 GHinv 在复制后中间态拒绝的事实，没有修改不变量制造闭合。

这里的 typed 是字节类型和空间所有权，不是完整全局 Inv；初始 high=88 超过配置上界12，故不是从生产初始化可达的整核状态。client 为既有有限纯 skip client，不支持据此推导任意 client。不同分支的无模拟前提实例已建立；相等分支本步只完成生产条件接口，独立控制复用第256步 `EPsame_single_byte_control`，不冒充从修改后完整初始堆出发的无条件调用模拟。

## 前瞻单因素对照

保持 CFfinal 上已计算的 high=4、所有其他字节和控制不变，仅省略目标指针更新：`XPomit_target_rejected` 证明目标仍指向 Waiting，不满足 Ready 的精确读取契约。这个对照**不是修改后程序的完整执行消融**，没有断言有限纯 client 能观察该存储，也没有从拒绝该契约推断后续计数／切换机制全部正确。

所有分配选择与释放对照沿用第258步；相等分支仅改当前优先级字节的控制沿用第256步。旧对照及失败证据不改。

## 未完成的最终目标

不是 `WFInt`，不是 `GOOD_OS`；K1–K4 未闭合，uCOS3 未开始。未提交／推送。尚需把本区间接入真实外层 OSIntExit 控制流、临界区恢复和完整中断返回，迁移相应函数环境与不变量；生产最终恢复端点仍是显式前提，任意暂停 client 尚未覆盖。阶段一必须先完成源码级 GOOD_OS，再按老师要求推进 uCOS3。

## 验证与复查

日志位于 `audit/logs/stage259-exit-call-dispatch-progsim/`，协议先于实现冻结，编译失败及完整源码快照保留。最终编译、逐根假设、递归 coqchk、构建、全量测试与旧失败的精确差分均记录于 verification.json。不得把局部检查点通过描述为全仓通过；历史覆盖向量不作为本步重新验收结果。

调试中发现 fid 与 var 虽可转换，重写匹配仍可能暴露不同 get 类型参数；已把变量声明改为标准 var，而非改框架重写规则或削弱绑定前提。单次指针数组见证／对照的 Qed 转换检查约12–14秒，保留这一成本，没有删掉真实堆实例。

### 实测结果

| 检查 | 结果 |
| --- | --- |
| 稳定编译 | 生产 prod12/prod13、独立实例 probe04/probe05 均通过；每对源码哈希相同 |
| 信任检查 | 4个生产根、5个实例根逐根检查；递归 coqchk 通过，耗时约512秒；743项 Coq 输入身份未变 |
| 假设 | 仅既有 `Classical_Prop.classic` 和 `FunctionalExtensionality.functional_extensionality_dep` |
| 增量构建／静态边界审计 | 均通过；335个活动 V293 Coq 文件 |
| 新增回归 | 5项全部通过；清理后重跑仍通过 |
| 全量测试 | 2460项，428个失败、1个错误；相对第258步新增5项，失败／错误 ID 及其顺序完全相同 |
| `make audit` | 退出2：沿用的函数证据输入身份已过期；未刷新或削弱旧验收门 |
| `git diff --check` | 退出2：既有 `framework/logic/inferules.v:581–586` 行尾空白；未修改旧框架 |
| 旧证据 | 1415项旧输入仅4项允许的文档／构建元数据变化；其余源码、测试、失败日志不变 |

第258步冻结检查点在当前工作树因 `_CoqProject` 前向登记而拒绝，通过 `previous-checkpoint-current.log` 保留；没有回写旧 manifest。构建依赖仅增加新模块的3行，旧行原样保留。覆盖向量 `94/1/1/1/1/0` 仅作历史记录，本轮未重新验收，不表示 `full_target_linked` 完成。

按路径、字节数和 SHA-256 确认后，已删除本任务一次性 Trust 入口、其产物及缓存备份共8项、708141字节；既有 `.lia.cache`／`.nia.cache` 原样恢复。源文件、所有编译失败快照、验证日志及可复用 Coq 产物保留。完整清单见 `cleanup-inventory.json` 和 `cleanup.json`。

只读复查命令：

```bash
python3 -B audit/logs/stage259-exit-call-dispatch-progsim/checkpoint.py
```

本步是**局部检查点通过，全仓仍未通过**。下一步应连接外层 nesting／lock 分支和临界区恢复，再处理完整中断返回与不变量／函数环境连接，而不是提前开始 uCOS3。
