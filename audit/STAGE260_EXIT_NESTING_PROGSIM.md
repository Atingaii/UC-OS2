# 第260步：把实际 nesting / lock 分支接到 Exit 调度模拟

## 从哪里继续，向哪里推进

第259步从实际 `OS_SchedNew` 调用开始。本步把起点向外推进到 `V293_OSIntExit_nesting_dispatch`，保留原语句，不改写为替代模型：

```text
if (OSIntNesting > 0) OSIntNesting--;
if (OSIntNesting == 0)
    if (OSLockNesting == 0)
        实际调度调用 → 目标指针更新 → 比较 → 计数 → 复制 → switch
```

`V293_exit_nesting_progsim` 覆盖全部字节 nesting 0..255；0不写入，正数恰减一。实际分支读取的是更新后的堆，而不是仅用纯布尔模型预设结果。只有更新后 nesting=0 才要求 lock 的绑定和读取；深层嵌套不要求不可达的 lock 或 dispatch 证据。`V293_exit_nesting_disabled_progsim` 把 nesting>=2 或 lock>0 的实际程序接到 skip 端点。

稳定接口 `V293_exit_nesting_dispatch_progsim` 对 nesting=0或1且 lock=0，把外层控制流连接到第259步真实调用至切换接口；**没有内层调度入口的 ProgSim 前提**。最终端点模拟与高层匹配仍公开，不能把条件组合定理当作整核闭合。

## 精确来源和边界

固定 V2.93.01，OS_LOWEST_PRIO=12u。原 C 位置 `os_core.c:701–724;1751–1758`，SHA-256 `96eef5dc1a519887499cffd8f9a6c8873b96978ed9646c42e52eb6992422fea5`。8项 C/config 身份与第259步逐项相同，未重跑预处理器。本步重新核对实际行号：positive 判断703行、减一704行、更新后 nesting/lock 判断706–707行（旧报告区间定位不精确，原文保留）。既有 AST `V293OSIntExit.v` 未改；C/config/framework/Inv/LI/BDspec、旧证明、测试、失败和冻结证据均保留。

IE=false，起点在进入临界区以后，尚未接上 running 判断、临界区恢复和完整返回。沿用 ADR-0010 的 normalized port-call 边界，没有证明原外部汇编端口 refinement，也没有覆盖任意中断交错。不是完整 `OSIntExit` 或 `OS_Sched` 函数模拟。

## 独立实例和前瞻对照

独立初始堆 `NPinitial 1` 只改既有 typed CEM 的 nesting 字节。`NPzero_cells` 从原空间所有权读取 nesting/lock；`NPdecrement_canonical` 逐地址证明真实1到0存储后的**整个堆**等于原 CEM。因此没有把不同运行的存在堆拼接起来。

`NPactual_nesting_dispatch_simulation` 从这个初始堆经新稳定接口建立原 ProgSim，没有任何 ProgSim 前提；非空 HPpending、实际指针 store、UINT32 从 mone 回绕到0、实际复制和物理 switch 均保留。有限两条 skip client 的端点由既有 HPpost 独立闭合。它不是任意暂停 client 的恢复契约。typed 只代表类型和空间所有权；原 high=88 超过配置上界12，不是初始化可达或完整全局 Inv 的证据。复制后原 GHinv 的拒绝仍保留。

前瞻协议先于实现冻结，单因素控制为：

1. 同一 `NPinitial 1`，仅省略减一，实际 nesting==0 guard 读1为假；真实减一后在同一规范堆读0为真。
2. 保持更新后 nesting=0，仅将 lock 字节0改1，实际 lock guard 由真变假；其他字节不动。
3. nesting=0 时整个堆保持不变，不做模256减一；nesting=2 时不要求未知 lock 的绑定，直接进入 skip 端点。

这些是实际表达式及精确堆契约控制，**不是完整变异程序的执行消融**。前置 guard 拒绝不作为下游调用／计数／切换正确性的证据；后者来自独立正向实例和生产全后继证明。禁用分支的模拟仍公开调用方端点；没有伪称其为无前提的任意 client 模拟。

## 当前目标状态

不是 `WFInt`，不是 `GOOD_OS`；K1–K4 未闭合，uCOS3 未开始，未提交／推送。下一步应接通临界区的中断开关恢复、running 外层和真正返回，并闭合相应函数环境、全局不变量和任意 client 义务。完整源码级 GOOD_OS 完成后才进入老师要求的 uCOS3。

## 验证

本步日志：`audit/logs/stage260-exit-nesting-progsim/`。失败编译和源码快照保留。局部证明检查与全仓构建、测试、审计分别记录，不能把局部通过描述成全仓通过。实测结果见本步 verification.json 与下方结果表；不会刷新旧失败或削弱验收门。

### 实测结果

| 检查 | 结果 |
| --- | --- |
| 稳定编译 | 生产 prod12/prod13，独立实例 probe06/probe07 均通过，同对哈希相同 |
| 信任检查 | 7个生产根、7个实例根；递归 coqchk 通过，约526秒；745项 Coq 输入不变 |
| 假设 | 仅既有 classic 与 functional_extensionality_dep |
| 构建／静态边界 | 均通过；336个活动 V293 Coq 文件 |
| 新增回归 | 5项全部通过 |
| 全量测试 | 2465项，428个失败、1个错误；相对259步只增5项，失败／错误 ID 及其顺序完全相同 |
| make audit | 退出2：旧函数证据输入身份过期；未刷新旧门 |
| git diff --check | 退出2：既有 inferules.v:581–586 行尾空白；未改旧框架 |
| 旧输入 | 1522项仅4项允许的文档／构建元数据变化 |

第259步当前工作树复查因前向元数据登记而拒绝，原日志保留，未回写旧 manifest。依赖只增加新模块3行，旧字节原样保留。历史覆盖向量94/1/1/1/1/0未重新验收。按路径、字节数和SHA确认后清理8项一次性产物，共709125字节；既有算术缓存恢复，源文件、日志、全部失败快照及可复用 Coq 产物保留。

只读复查：`python3 -B audit/logs/stage260-exit-nesting-progsim/checkpoint.py`。本步是局部检查点，不是全仓通过，更不是整核完成。
