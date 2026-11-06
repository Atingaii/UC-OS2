# 第265步：完整活跃 OSIntExit 调用的条件模拟接口

## 1. 本步连接的对象

固定 V2.93.01 配置后 `os_core.c:693–736` 的 OSIntExit，仍使用 ADR-0005 临界区原语和 ADR-0010 中断切换源码级抽象。C/config/AST/framework/Inv/LI/BDspec 均不修改。源码哈希和逐行定位保存在 `audit/logs/stage265-exit-active-call-progsim/source-identity.json`；本步未重新预处理。

第264步独立实例从内层 OS_SchedNew 调用前开始；它没有外层函数的分配、running 判断和 encrit。本步新增生产接口 `V293_exit_active_call_progsim`，接通以下归一化实际语义：

`sfexec（或 OS caller 中 scall） → 函数绑定查找 → 任意 fresh Tint32 saved 分配 → saved=0 → running=true → encrit → nesting 饱和减一 → 更新后 nesting=0 且 lock=0 → 实际 OS_SchedNew 调用及释放 → 目标指针写入 → 优先级不同判断 → 计数增加 → 优先级复制 → switch → 目标已存在 pending 的 excrit/sret/free → 目标 caller`。

## 2. 稳定接口及仍公开的条件

生产模块 `certiucos/v293/proofs/V293ExitActiveCallProgSim.v` 只有3个证明根：

- `V293_exit_active_critical_prefix_progsim`：推入 false 保存位，执行实际 nesting/lock 分支，连接内层 dispatch。
- `V293_exit_active_body_prefix_progsim`：加上 saved 初始化与 running=true 判断。
- `V293_exit_active_call_progsim`：加上函数调用入口、**每个任意 fresh 分配结果**，直接接到既有完整 dispatch/目标 pending 返回接口。

前两个是实现内辅助连接；上层使用第三个。主接口只有最终 caller 端点模拟与入口模拟两处 ProgSim，不要求中间 dispatch、switch 后或 pending 入口 ProgSim。有限实际执行不是 ProgSim 的替代品。

它仍是**条件定理**：实际内存读写、分支取值、目标已有 pending、目标 saved 释放、最终 caller 端点模拟、高层 `hpstepstar` 匹配均明确公开。资源见证按 `forall bs, fresh M bs` 提供，不能只选一个好用的分配结果。`scall` 仍要求已有 InOS 上下文；并非任意 client 调用。

入口 IE=false，encrit 保存 false；目标保存栈顶也为 false。活跃条件为入口 nesting<=1、更新后 lock=0、running=true、优先级比较不同。没有证明切出任务最终被再次调度并返回；它的局部环境和 pending 续体仍保留。

## 3. 独立核查与单因素消融

协议在实现前冻结，见同目录 `protocol.json` / `protocol.sha256`。新 probe 没有 ProgSim 前提，也没有把该主接口原样当作独立实例：

1. `APfresh_storage`：对任意 fresh 块执行真实 allocb/store 和赋值 cstepstar；目标原有 Tint32 saved 块与新块不别名，目标 load 保持，其他块逐字节保持，释放新块后回到完整旧堆。
2. `APnesting_control`：同一非空物理堆，其余地址、程序、环境、续体和 dispatch 均不变，只改 nesting 字节1→2。真实 decrement+guards 分别到 dispatch 入口／SKIP，后者内存为 nesting=1；有其余地址一致的显式等式。**守卫拒绝不能证明下游调度、切换或返回**。
3. `APtyped_resource_family`：在 nesting=1/2 的既有 typed 分离资源上实例化任意 fresh 分配；目标 saved=98，保持其值并证明新块与98不别名。typed high=88，而固定配置最低优先级12；不是完整 Inv 或初始化可达证据。

旧第264步同堆完整 dispatch/switch/返回实例原样保留。**不能把本步的分配局部实例、守卫实例与旧内层实例拼成一个独立完整调用见证**：它们尚未证明是同一条完整全局运行。本步尚无独立完整 OSIntExit 活跃调用实例，这是下一步优先义务。

## 4. 验证方法及旧门

本步串行稳定重复编译，逐根 Print Assumptions、递归 coqchk，全量构建、项目审计、全量测试与旧输入字节差分。新5项 Python 回归只检查接口/来源/证据边界，证明有效性由 Coq 与 coqchk 检查，不以文本扫描替代。

新增生产文件必须登记 `_CoqProject`，依赖文件仅允许新增对应3条规则；旧尾部原样保留。第264步测试曾冻结“工程列表不变”，本步登记后可能新增该身份失败，必须实测保留，不能改旧测试或将其报告为无差异。旧检查点也不应在新元数据上冒称通过。所有失败编译和旧失败证据保留。

## 5. 验收边界和下一步

这是完整归一化活跃调用的**生产条件接口**，不是独立完整函数实例，不是所有路径 OSIntExit，不是完整中断返回，不是 `WFInt`，不是 `GOOD_OS`。K1–K4 未闭合，uCOS3 未开始，未提交／推送。历史覆盖94/1/1/1/1/0不在本步重新验收；不涉及原始 port/ABI/硬件精化、公平性或无限干扰。

下一步优先构造一个同时包含任意 fresh saved、running/encrit/nesting、完整调度和目标 saved=98 分离的同堆实例；然后继续消除上层真实 Inv/初始化和最终 caller 模拟义务。最终仍按完整源码级 GOOD_OS 与 K1–K4，再进入老师指定的 uCOS3 阶段。

## 6. 实测结果

| 检查 | 结果 |
| --- | --- |
| 稳定编译 | prod09/prod10、probe04/probe05；各对源码哈希相同 |
| 信任检查 | 3个生产根、3个局部核查根；递归 coqchk 通过，约531秒；754项输入未改 |
| 假设 | 仅既有 classic 与 functional_extensionality_dep |
| 构建／项目边界 | 通过；340个活动 V293 Coq 文件、103个框架/策略文件 |
| 新增回归 | 5项通过 |
| 全量测试 | 2490项；429失败、1错误；原428失败和1错误ID及相对顺序全部保留 |
| 新增旧门失败 | 第264步 test_existing_production_and_project_unchanged：工程登记身份变化；旧测试不改 |
| make audit | 退出2：旧函数证据输入身份过期，未刷新旧门 |
| git diff --check | 退出2：既有 inferules.v:581–586 六行空白，未改框架 |
| 旧输入 | 2107项，仅中文入口前缀、工程追加一行和依赖追加3行变化；旧尾部不变 |

旧264检查点开始前通过，新元数据下因只允许README/状态文档变化的旧身份断言拒绝；保留前后原日志，不回写其 manifest。旧 Coq/C/config/AST、旧测试、冻结证据与失败均未改。历史覆盖不重新声称有效。

清理前逐路径/大小/SHA确认，删除8项一次性信任产物和已恢复缓存备份，共708893字节；保留全部失败快照、源码、日志和可复用 Coq 产物。局部检查点通过不代表全仓通过。
