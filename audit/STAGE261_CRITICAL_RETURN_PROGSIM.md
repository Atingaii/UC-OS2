# 第261步：非调度临界区到真实 void 返回

## 本轮补上的缺口

第260步已证明更新 nesting 后的实际调度判断，但临界原语和完整返回仍在区间之外。本轮在**原 ProgSim** 上纵向连接：

`encrit → 原 nesting/lock 禁用分支 → excrit → sret → free Tint32 → caller`。

生产稳定接口为 `V293_exit_quiet_return_progsim`。它从 running 判断后的实际临界区子树开始，续体是 `kseq sret (kcall ... caller ks)`，没有重排原 AST。生产只有最终 caller 端点模拟与起点两处 ProgSim；不再让调用方假设 encrit 后、nesting 后或 excrit 后的中间模拟。仍须提供最终 caller 的后续模拟，不是任意 client 已闭合。

固定源码：`csrc/upstream/v2.93.01/checkout/Source/os_core.c:701–724`，SHA-256 `96eef5dc1a519887499cffd8f9a6c8873b96978ed9646c42e52eb6992422fea5`。8项源码／配置身份和原行锚点由 source-identity.json 逐项复核；未重跑预处理，也未改源码或 AST。

## 准确前提和可观察结果

- 入口 IE=false，临界栈可带任意前缀，中断栈保留；进入临界区压入 false，退出时弹出该位。整个 quiet 路径恢复原辅助任务映射，其他任务不变。
- nesting、lock 为合法字节。减一仍由第260步真实饱和减一和更新后 guard 解释；禁用条件是 `2<=n` 或 lock 非零，仅在 `pred n=0` 时需要 lock 的绑定和读取证据。
- 通过原全局执行关系覆盖所有后继、输出和异常义务；不是只展示一条成功 trace。excrit 的通用助手允许恢复 true，但 true 端点的中断模拟义务仍留在端点，未被 IE=false 的原语入口假设消除。
- 返回经过真实 `sret/free/freeend`，要求当前局部布局恰为一个 Tint32，并实际释放成功；恢复 caller 环境和原临界栈。
- 沿用 ADR-0005 / ADR-0010 的源码级显式抽象。物理 saved 字节不被当作读取硬件 IE 的证据；没有新增端口函数实现、C 修复或语义规则。

## 非空、非循环实例

`CPtyped_updated` 从既有空间所有权堆构造 `NPinitial n` 的完整 typed frame；包含实际 nesting、lock、Tint32 saved 局部、ready 资源、指针、计数器等。实例取 nesting=2，减一结果对**整个堆**证明等于 `NPinitial 1`。调度被实际 nesting 分支关闭，未要求运行不可达的 dispatch。

`CPquiet_return_simulation` 无 ProgSim 前提：实际释放全部四个 saved 字节，证明其他块不变，再独立用原终止 client 规则关闭 caller 端点。函数上下文绑定实际 normalized OSIntExit 函数，caller 为空局部环境、终止续体；这不是从完整函数入口的可达性证明。原 typed high=88 超过配置最低优先级12；typed 非空不等于完整 Inv，也不是初始化可达。

## 前瞻单因素对照

协议先冻结于 `audit/logs/stage261-critical-return-progsim/protocol.json`。

1. 固定堆、原语、IE=false、中断栈和续体，只把 excrit 栈顶 false 改 true；两者都真实执行，分别恢复 false / true，并排除“栈顶 true 却恢复 false”的后继。这只是原语边界对照，不是完整变异程序的执行消融。
2. 同一 excrit 入口删除最后一个栈元素，证明原 loststep 无后继，并进一步建立原 `lpstepabt`；不是语法早拒绝。正控是上述带一个 false 的实际 excrit。
3. 实际 quiet 正例从 nesting=2 减至1；0不回绕及 guard/lock 单因素表达式对照继承第260步，不重复授信为本步完整执行消融。

## 边界与下一步

调度切换会挂起旧任务的 excrit/return/caller；本步**不把旧任务的返回强接到新任务上**。新接口目前只关闭不发生调度的返回分支，调度后旧任务何时恢复仍须单独证明。入口 IE=true 的可中断区间也未闭合。

不是完整 OSIntExit，不是完整中断返回，不是 `WFInt`，不是 `GOOD_OS`；K1–K4 未闭合，uCOS3 未开始。C/config/AST/framework/Inv/LI/BDspec、旧证明、旧测试和原失败均保留，未提交／推送。下一步应补运行判断／初始化入口及调度后旧任务恢复连接，随后才能归入完整函数、全局环境与初始化证明。

本步数值结果由 verification.json 记录；编译失败快照和被终止的重计算尝试也保留。检查材料入口：`audit/logs/stage261-critical-return-progsim/`。

## 实测结果

| 检查 | 结果 |
| --- | --- |
| 稳定编译 | 生产 prod09/prod10、实例 probe08/probe09；各对哈希相同 |
| 信任检查 | 17个生产根、7个实例根；递归 coqchk 通过，约521秒；747项输入未改 |
| 假设 | 仅既有 classic 与 functional_extensionality_dep |
| 构建／静态边界 | 通过；337个活动 V293 Coq 文件 |
| 新增回归 | 5项全部通过 |
| 全量测试 | 2470项；428个失败、1个错误；相对260步失败／错误 ID 及顺序不变 |
| make audit | 退出2：旧函数证据输入身份过期，未刷新旧门 |
| git diff --check | 退出2：既有 inferules.v:581–586 六行空白，未改框架 |
| 旧输入 | 1636项只有4项允许的文档／构建元数据变化 |

前一检查点在前向元数据登记后的拒绝保留，旧 manifest 未改。依赖只增新模块3行，旧字节不变。历史覆盖94/1/1/1/1/0未重新验收。清理前逐路径、字节、SHA确认，删除8项一次性信任产物与已恢复的缓存备份，共711196字节；保留源码、日志、全部失败和可复用 Coq 产物。重计算被终止的 probe02 也保留，未改写为成功。

只读复查：`python3 -B audit/logs/stage261-critical-return-progsim/checkpoint.py`。本步是局部检查点，不是全仓通过。
