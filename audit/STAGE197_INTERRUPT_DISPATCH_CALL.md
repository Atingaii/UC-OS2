# 第197步：最后一层中断的完整同任务调用

## 本步究竟补了什么

第196步停在 `OSPrioHighRdy != OSPrioCur`。本步把“当前任务已经是最高就绪任务”这条路径接成完整抽象函数调用：

```
scall → sfexec（替换 caller 局部环境）
→ fresh 分配 cpu_sr 的4字节 → cpu_sr := 0 → running == 1
→ encrit → nesting: 1→0 → 两级 guards
→ 真实 OS_SchedNew 调用、分配、计算、返回释放
→ 更新 high/target → 从同一 task map 推导实际比较为 false
→ excrit → return → 释放 cpu_sr → 恢复 caller
```

上层接口是 `V293_OSIntExit_same_task_call_execution`，文件为
`certiucos/v293/proofs/V293OSIntExitDispatchCall.v`。

它不要求调用方提供整段 trace、callee 执行、分配/store/free 或比较求值证明。当前任务的优先级关系与最高就绪关系必须来自**同一个** task map；通过原 ready/task/table 关系推出选择结果等于当前优先级，而不是直接假定比较 false。

## 结论的精确范围

- 实际 `V293_local_steps` 从无实参调用到返回后的 skip；恢复任意入口 IE、既有临界栈尾与 caller 局部环境。
- high 为当前任务优先级，target 为该 TCB，nesting=0/lock=0；ready/task/table 资源和 frame 保持。
- 本次 fresh 局部块的4字节均释放。
- 字节 frame 排除 fresh **整个块**、target **整个块**、high 单字节、nesting 单字节；不声称更强的全堆更新方程。
- **空间前/后置明确使用 IE=false 的逻辑视图**。执行 trace 的 IE 可以为 true 或 false；这不等于证明 IE=true 的真实状态也满足生产 `SWINV`，更不能据此宣称生产 ISR/LocalInv 闭合。

## 独立入口与事前对照

冻结协议：`audit/logs/stage197-interrupt-dispatch-call/protocol.json`。

probe 不从成功执行反推入口，而由原非空任务图、ready bitmap/table 和独立 owned cells 构造入口。当前任务 priority4 是唯一 ready 任务；waiting priority6 仍存在。high 旧值88、旧 target 为 waiting TCB；真实调度将它们更新为4和 ready TCB。

| 检查 | 保持不变 | 改变/设置 | 实际观察 |
| --- | --- | --- | --- |
| 完整正控 | 非空 task/ready/table、真实 OS_SchedNew | nesting=1/lock=0/current=4 | 整条调用结束，target 更新、两层局部调用均返回 |
| IE 单因素 | 同一 program、物理堆、caller、临界栈尾 | 入口 IE=false→true | 两侧均完整返回，分别恢复原 IE 与栈尾；4字节释放 |
| caller 遮蔽 | 同一完整正控 | caller 中同名 saved 为 Tint8/旧值23，局部 running=0，全局 running=1 | callee 实际读取全局，返回恢复 caller；saved23/local running0/counter19/canary99保持 |
| 唯一 lookup 删除 | 其他所有函数定义 | 只删除 OS_SchedNew 的107号 lookup | 实际 sfexec 没有下一步；其余 lookup 逐一相等 |

lookup 删除只证明调用边界阻塞，**不是**下游临界区、分配和恢复的消融证明。下游机制由独立完整正控验证；不能把早期拒绝当作它们正确的证据。IE 对照不是原端口保存字节与硬件寄存器的仿真。

## 证据与复现

目录：`audit/logs/stage197-interrupt-dispatch-call/`。

- `body08` / `probe04` 是稳定编译身份；之前失败的快照、日志、真实退出码均保留。
- 两次新鲜重建精确配置后 `OSIntExit` / `OS_SchedNew`，核对函数体、源行及锁定哈希，临时源码目录自动删除。
- 本步19个生产/probe 根逐根 `Print Assumptions`，递归 `coqchk` 两入口；结果与原允许信任集合比较。
- 新增5项结构回归，不能替代 Coq 的语义证明，不声称严格语义 TDD。两轮全量共2149项；旧423失败、1错误及有序ID必须保持。
- build/project-audit 与旧 audit/whitespace 失败分别记录，绝不改弱门槛。具体退出码与旧文件哈希核对见 `verification.json`。
- `baseline.json` 在本步新证明之前冻结；历史文档仅前插，工程清单仅追加。最终清单排除自身，重检脚本检查证据未漂移。
- 清理前逐一登记一次性信任驱动/产物与原缓存备份；恢复原缓存字节，保留失败证据和可复用编译产物。

可执行只读复核：

```
PYTHONDONTWRITEBYTECODE=1 python3 audit/logs/stage197-interrupt-dispatch-call/recheck-checkpoint.py
```

## 距最终目标还差什么

本步仍只证明 ADR-0005 显式抽象程序的局部、不交错、当前任务继续运行路径。它不是原始端口调用的语义保持证明，也不是完整内核调用环境或初始化可达性。

不同优先级路径的 counter++ 与真实 OSIntCtxSw 效果、生产 ISR/LocalInv、WFFunEnv、初始化和全局模拟仍未闭合；最终 `GOOD_OS` 与 K1–K4 同程序回归仍未完成。六门仍是 `94 / 1 / 1 / 1 / 1 / 0`，不以新增证明文件提高覆盖。

下一步沿真正任务切换分支连接框架接受的切换边界，不能用 identity callee 或未实现的 lookup 冒充切换。第一阶段完成后才按照老师附件开展 uCOS3；当前目标仍 active，未提交或推送。
