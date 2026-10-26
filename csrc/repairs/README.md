# V2.93.01 授权修复材料

本目录仅保存 `PROJECT_SCOPE.md` 授权的两类修改。第三阶段已将原先的算法片段接入真实源码，并以完整 unified diff 交付。测试在一次性源码副本中应用补丁；**不改写原始 checkout，不表示最终源码级证明已完成**。

| 补丁 | 唯一修改的上游文件 | 作用 |
| --- | --- | --- |
| `0001-nested-mutex-restoration.patch` | `Source/os_mutex.c` | 基础优先级保存、剩余贡献重算与状态保持的重定位 |
| `0002-locked-current-self-delete.patch` | `Source/os_task.c` | 删除前拒绝已锁定调度的当前任务 |

当前状态为 `C_SOURCE_FROZEN_COQ_CORRESPONDENCE_OPEN`。[冻结记录](FROZEN_SOURCE.json) 与 [修复后完整清单](../../audit/repaired-source-inventory.json) 已建立，输出哈希与第三阶段 [执行证据](../../audit/c-regressions.json) 相同。94 个定义均已定位，C 到 CoqImp 对应及全部源码级证明仍未完成；第二阶段清单仍只代表原上游。

原 `protocol.c` 与 `locked-current-delete.guard.c` 片段已由补丁取代，不再保留第二份实现；历史内容可从 Git 查看。

## 1. 嵌套互斥锁优先级恢复

区分任务基础优先级与当前有效优先级。获取互斥锁时保存所有者基础优先级；释放或删除时，根据基础优先级和仍持有的全部互斥锁贡献重算有效优先级。恢复不能覆盖其他活动任务占用的优先级表槽位。

保存基础优先级覆盖 Accept、自由获取的 Pend，以及 Post 将锁交给新所有者三个入口。Post、Del 的 ALWAYS／NO_PEND 成功分支均使用同一重算规则；NO_PEND 有等待者时仍按上游拒绝删除。

重定位保留原有就绪位与单事件等待位；不会把挂起／等待的所有者无条件设成就绪。只有被移动的任务确为当前任务时才改 `OSPrioCur`。不新增公共 API、TCB 字段或第三类修复。

## 2. 调度锁定期间删除当前任务

在破坏性修改前，`OSTaskDel` 检查目标 TCB 是否为 `OSTCBCur`，且 `OSLockNesting > 0`。若成立，退出临界区并返回已有错误码 `OS_ERR_SCHED_LOCKED`（50）。

任务、TCB、资源、就绪状态与锁计数保持不变，不新增错误码。

## 重跑与理解

```sh
make source-freeze-check # 从实际源码重放补丁、清点并只读比较冻结记录
make check-c            # 23 场景 × 四种补丁组合 × 两个编译器 × 两种优化
make check-c-evidence   # 重跑后与已提交 JSON 逐字比较，不改写证据
make test              # 含逐机制消融与边界拒绝检查
```

这些命令需要 Linux 的 32 位可执行支持、GCC、Clang、Git 和源码清单工具；无 libc、网络或 root 安装步骤。测试用模拟 CPU 边界，不执行实际任务栈，不构成硬件或编译器正确性证明。

初学者阅读 [第三阶段教学](../../docs/阶段/03-真实C回归与授权修复.md)；实测结果与边界见 [第三阶段报告](../../audit/STAGE03_C_REPAIRS.md)。
