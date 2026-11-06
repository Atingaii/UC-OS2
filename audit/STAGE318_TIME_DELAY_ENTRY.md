# 第318步：延时函数入口判断、临界区与提前返回

## 本步接上了什么

此前第317步只连接 `OSTimeDly` 的临界更新。本步沿同一固定配置后的函数体向外连接：

1. 先判断 `OSIntNesting`；非零就返回，不读取后面的锁和 ticks。
2. 再判断 `OSLockNesting`；非零就返回，不读取 ticks。
3. `ticks == 0` 直接返回；其余 **无符号32位** 值都进入阻塞分支，包括 `0x80000000`。
4. 执行原框架 `encrit`、真实位图／延时更新和 `excrit`；到达 `OS_Sched()` **调用之前**。
5. 三条提前返回路径实际执行 `sret`、局部块释放和 caller 环境恢复，不只是停在 return 语句。

生产文件：`certiucos/v293/proofs/V293TimeDlyEntry.v`。

稳定接口：
- `V293_OSTimeDly_body_to_sched_refines`：从入口资源推出实际执行、原 `spec_step`、同一末端堆的全部任务记录／位图关系和 frame；不把执行或后继模拟作为前提。
- `V293_OSTimeDly_early_return`：短路拒绝条件和局部写权限推出实际返回、非局部字节保持及全部局部块释放。

## 为什么没有把等待任务直接改成 ready

正分支结束时，当前任务的延时字段已写入，ready 位已清除，抽象任务状态为 `wait os_stat_time duration`，但 `curtid` 仍指向该任务。后续必须运行真实 `OS_Sched` 及任务切换，不能直接修改 current 或把其他等待任务改成 ready 冒充调度。

实例包含两个真实物理任务记录、就绪位图、三个局部变量和独立 canary=99。较低优先级任务在输入时已经 ready；**不是从之前真实 Waiting 状态唤醒**。初始 IE=true/false 均可实例化；实际临界栈 push/pop 恢复原辅助状态。

## 单因素对照

实验前冻结 `ablation-protocol.json`。只把正分支的 `excrit` 换成 `SKIP`，其余入口判断、更新、非空输入堆、抽象阻塞一步、目标调用点与 continuation 不变。

两种程序分别实际执行到相同 `OS_Sched()` 调用点，并得到阻塞任务记录、位图及 canary=99。最后才要求辅助状态恢复：正常版本通过；省略退出后 IE=false 且临界栈多保留一项，最后一门失败。即使原 IE=false，栈泄漏仍可检测。

这只验证 normalized AST 上的临界退出机制，**不是 raw port C 变异、真实调度调用或全交错中断安全证明**。不会把入口提前拒绝当成下游机制全部通过的证据。

## 严格边界与下一步

- 入口在 `cpu_sr = 0` 初始化之后；不是函数调用分配及 initializer 的完整执行证明。实例 y 单元具有已知初值，不能声称证明未初始化自动变量入口。
- 使用已有 normalized 临界原语边界；不是 raw method3 的具体移植层实现。
- 正分支停止于调度调用前；不是完整回切，也不是完整 `OSTimeDly` API。
- `spec_step` 是第317步的局部阻塞契约，尚未注册为全程序 API 契约；全部任务记录是同堆后置条件，**不是全局记录不变量**。
- 统一 WFInt、全局 ProgSim、初始化、源码级 GOOD_OS 和同程序 K1–K4 仍开放，uCOS3 未开始；目标保持 active。

下一步应把同一个末端堆交给真实 `OS_Sched` 调用执行和切换，再连接延时结束后的恢复、返回与调用分配。不能另造一块满足后置条件的堆，也不能只增加统计条目。

## 复现与结果

详见 `audit/logs/stage318-time-delay-entry/` 下的编译日志、失败快照、独立源码重物化、假设闭包与递归 `coqchk`、单因素门和 `verification.json`。旧失败保留，不通过修改旧测试、降低门槛或重写冻结证据制造全绿；本步不提交／推送 Git。

### 实测结果

| 检查 | 本步结果 |
| --- | --- |
| Coq 8.18.0 生产／实例重复编译 | 两轮均通过，源码哈希不变 |
| 22个证明根假设闭包与递归 `coqchk` | 通过；仅使用既有 classic／functional extensionality 边界 |
| `make build JOBS=1` | 通过，属于当前工作树增量构建，不冒充独立净目录重建 |
| 新增回归 | 8项通过 |
| 完整回归 | 2796项；保留438个原失败、1个原错误，ID及顺序与第317步完全相同，无新增失败 |
| 项目范围审计 | 通过；393个活动 V293 文件、103个框架／tactics 文件；文件数不是函数证明覆盖率 |
| `make audit` | 仍因旧 `stale function evidence input identity` 失败 |
| `git diff --check` | 保留原六处空白问题，输出与第317步逐字一致 |
| 清理 | 逐项确认后删除17个本轮一次性包装／对象／备份；原缓存、306个原pyc及所有失败快照保留 |

最初两组实验包装因缺少 import 提前失败，证据保留，**不计作机制对照通过**；有效对照为 `gate-*-03` 与稳定源码后的 `gate-*-final`。

### 对抗复核后的限定

- `V293_local_steps` 给出实际有限执行的存在性；不是任意中断交错下都正确。
- 外部 frame 在相同入口／末端辅助状态快照下保持；没有把依赖辅助状态的任意断言无条件搬进临界区中间。
- AST 仍是已有的手工源码建模；源码身份和重物化检查不等于自动 C 翻译正确性证明。
- 对照保持输入堆、更新和物理观测不变；没有另行证明跨两次运行的末端堆逐字节相等，不作这一额外宣称。

在仓库根目录可只读核验本检查点：

```bash
PYTHONDONTWRITEBYTECODE=1 python3 -B audit/logs/stage318-time-delay-entry/verify.py
PYTHONDONTWRITEBYTECODE=1 python3 -B -m unittest discover -s tests -p test_time_delay_entry.py -v
```

这两条命令核对已保留的证明／实验身份及新增回归；递归内核复核的实际命令与输出另见 `trust.json`／`trust-coqchk.log`，不能把 Python 文本检查当成 Coq 内核复核本身。
