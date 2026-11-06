# 第319步：阻塞任务实际进入调度调用并发布目标指针

## 这一步解决什么

第318步证明当前任务执行非零延时后从就绪位图移除，但停在 `OS_Sched()` 调用前。此时 current 仍是阻塞任务，不能复用要求“当前任务就绪”的前提，更不能直接改 current 冒充切换。

本步稳定接口为 `V293_sched_call_to_change`，从实际 `scall` 推导：

1. 为 `OS_Sched` 分配新 CPU 保存单元并执行零初始化；
2. 执行 `encrit`、中断嵌套及调度锁两道零值判断；
3. 实际调用 `OS_SchedNew`，分配新局部字节 `y`，查表计算最高优先级；
4. 执行 helper 的 `sret/free`，恢复调度器 caller，局部字节不再分配；
5. 执行 `OSTCBHighRdy = OSTCBPrioTbl[OSPrioHighRdy]`，读回目标指针。

结论还给出 CPU 单元四字节可写，以及除 CPU／最高优先级／目标指针块以外的逐字节 frame。前提只是绑定、数值范围、读写权限和表数据，不要求 caller 当前任务就绪，不把 callee 执行或后继模拟当作前提。`V293_schednew_raw_call` 另给出 helper 的精确净堆变化：只写最高优先级字节。

## 源码身份

固定 V2.93.01 提交与两类授权修复、配置不变；独立重新物化源码并预处理，三函数逐项比对库存记录。证据在 `audit/logs/stage319-time-delay-sched-call/source-identities.json` 与 `.source.c.snapshot.txt`／`.configured.c.snapshot.txt`。

| 函数 | 源码定位 | 配置后定义 SHA-256 |
| --- | --- | --- |
| OSTimeDly | os_time.c:53–81 | c8626621a399e6f622e6d311d943d098e182b4cdcd5aaa5ccf21d7215be08519 |
| OS_Sched | os_core.c:1702–1732 | 59d34e6ebeb338b71ea2e2969fb66a28c413acc71835430b35334bc15ab8a61d |
| OS_SchedNew | os_core.c:1751–1776 | 6d156edfff0548ed63fdff59a400e8d0ca0e69813ef6bf0142d0ce1902443d71 |

`function-boundary.json` 记录这只是局部连接，不将片段成果升级为三函数完整覆盖。AST 仍为人工源码建模；身份核对和预处理重放不是自动 C 翻译正确性证明。

## 同堆非空实例

`DSblocked_run` 不假设执行结果，而由完整空间所有权构造实际执行：

- 两任务分别为优先级4（当前）与6（另一已就绪任务），任务记录完整；
- 当前执行 ticks=3，实际清除优先级4就绪位，原抽象 `spec_step` 把它记为等待；
- 相同程序 `DSprogram` 对两种初始 IE 均执行真实调度调用，选中数值6，再发布其表项指针；
- 末端同一块堆保留全部任务记录、位图关系、值为99的 canary、CPU 可写权限及 helper 已释放事实。

`DSblocked_current` 明确 current **仍指向阻塞任务**。`DSboth_IE` 连接同一程序的两种 IE 输入，不是两份定制程序。

## 预先冻结的单因素对照

协议在执行前冻结。只把 wrapper 中 `DSwrong := false` 改成 `true`：优先级表第6项由另一任务指针改成当前阻塞任务指针。`DSonly_slot` 证明其他表项不变；程序、局部变量分配、guards、查表、数值6、目标存储语句、两份任务记录与 canary 均不变。

两者都先完成实际执行、全部任务记录／位图、数值6、canary、CPU 可写与 helper 释放门。基线最后证明目标是另一任务；变体在最后目标身份门被拒绝。重放两次，保存两者源码快照、退出码与失败上下文，不以早期导入／语法失败代替消融结果。

`DSmutant_outside_table` 明确证明变体不满足任务与优先级表的一致性不变量。该实验检验“数值正确但指针错误”的晚门，**不是全局优先级表不变量保持证明**。这里只比较指定字段及真实轨迹；没有另证跨两次分配选择的末端全堆逐字节对应。

## 边界与未完成工作

- 不是完整回切：止于原比较／计数器／switch continuation，尚未执行比较、计数器或物理切换，也没有返回或恢复旧任务。
- 不是完整 `OSTimeDly` API：入口仍在其 CPU 初始化之后；本步只补齐实际调度调用的分配／初始化。
- 不是全局记录不变量：资源来自非空输入所有权，轨迹不包含任意中断交错。
- 不是从之前真实 Waiting 状态唤醒：另一任务已ready是输入条件，不篡改其状态。
- 不是 raw port／二进制证明：沿用规范化临界原语及框架切换边界。
- 尚未建立统一 WFInt／全局 ProgSim、初始化、最终源码级 GOOD_OS 与同程序 K1–K4；uCOS3未开始。总目标保持active。

## 验证、保留与下一步

真实编译、递归信任复核、回归、审计与清理结果统一记录于本步 `verification.json`，该文件不存在时不能宣称验收完成。失败尝试保留，尤其不透明地址判等导致的四次终止：换成透明判等及其原条件解释证明后，原字面空间检查快速通过，没有降低检查条件。

旧源码／测试／证据不改写；顶层文档只前置说明，`_CoqProject` 只尾加生产证明。原有缓存与306份字节码保留，临时 wrapper／信任检查产物逐项审查后清理。不提交／推送。

下一步应消费此接口，执行原比较与计数器，再连接实际调度切换和后继资源；不能将已发布的目标指针直接当成 current 已切换。

### 本步实际复核结果

| 检查 | 结果 |
| --- | --- |
| 生产／实例重复编译 | 两轮通过，各轮输入／结束源码哈希相同 |
| 18个证明根与递归 `coqchk` | 通过；仅既有 classic／functional extensionality 边界；递归检查约240秒 |
| `make build JOBS=1` | 当前工作树增量构建通过，不冒充独立净目录重建 |
| 新增回归 | 8项、两轮通过 |
| 完整回归 | 2804项；438个旧失败、1个旧错误，ID及顺序与318步相同，无新增失败 |
| 项目范围审计 | 通过：394个活动V293文件、103个framework／tactics文件；数量不是函数覆盖率 |
| `make audit` | 保留原 `stale function evidence input identity` 失败 |
| `git diff --check` | 原六处空白问题，输出与318步逐字相同；新增交付文件另行检查行尾空白与末尾换行通过 |
| 清理 | 逐项确认后删除18个本轮一次性文件；保留原缓存、306份原pyc、可复用证明对象及所有失败快照 |

首组消融包装因缺少 `V293_tcb_type` 导入而提前失败，**不计作机制验证**；有效两组为 `gate-*-02` 和 `gate-*-final`。

在仓库根目录可核对冻结后的局部结果：

```bash
PYTHONDONTWRITEBYTECODE=1 python3 -B audit/logs/stage319-time-delay-sched-call/verify.py
PYTHONDONTWRITEBYTECODE=1 python3 -B -m unittest discover -s tests -p test_time_delay_sched_call.py -v
```

Python 检查核对保留的证据与接口，不代替 Coq 内核检查；真实命令和输出在 `trust.json`／`trust-coqchk.log`。
