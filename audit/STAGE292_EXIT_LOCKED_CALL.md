# 第292步：调度锁非零时的 OSIntExit 完整客户端调用

## 这一步在做什么

中断退出不一定引起任务切换。原函数先检查内核是否运行，再进入临界区，把非零中断嵌套计数减一；只有递减后的计数为零且调度锁为零，才执行调度。本步证明：**running=1、nesting 为任意字节 0..255、lock 为非零字节 1..255 时，调用能安全返回原客户端，并恢复原 storage 家族的 RDYINV。**

不是整个 OSIntExit 或 GOOD_OS 的证明，也不是 Post=True。老师要求的顺序不变：先完成整个 uCOS2，再开展 uCOS3；uCOS3 未开始。

## 与前两步的关系

| 分支 | 已连接的完整客户端调用 | 本步关系 |
| --- | --- | --- |
| running=0 | 第291步，不进入临界区 | 保留原证明，不改冻结证据 |
| running=1，n=2..255，lock=0 | 第290步，递减后非零，跳过调度 | 保留原证明 |
| running=1，n=0/1，lock=0，changed | 第289步，调用 helper 并切换 | 保留原证明；不声称覆盖等优先级 |
| running=1，n=0..255，lock=1..255 | **本步**，全部 nesting 字节 | 实际递减和双 guard 后直接退出 |

这些接口仍采用不同的资源布局及分支专用规格，不能把表格拼成统一规格或整核覆盖声明。

## 证明接口与执行链

生产文件：`certiucos/v293/proofs/V293ExitLockedCallTaskSim.v`。

唯一公开 Theorem：`V293_exit_locked_client_call_TaskSim`。

1. 两层相同客户端 `scall f nil`，高层通过显式 API 绑定走分支专用 `END None`。
2. 低层按真实函数绑定进入 `sfexec`，覆盖全部 fresh saved 局部分配后继；没有预分配 saved 前提。
3. saved 从 Vundef 写为零，running=1 判断为真。
4. 真实 `encrit` 压入 false；n=0 不写，n>0 写入 `pred n`。
5. `pred n>0` 时外层 nesting guard 为假，不访问锁；`pred n=0` 时读取非零 lock，内层 guard 为假。
6. 走真实 `excrit`、saved 释放、函数返回及调用者局部环境恢复；后置仍为原 `RDYINV G t ** LINV`。

公开接口只要求范围界、saved 与三全局变量名不等、三全局类型绑定、函数/API 绑定、合法客户端尾部、ISR 全清与空间资源。**没有执行结果、store/load/eval 结果或下游 TaskSim 前提。** 辅助 prefix 的 continuation 在内部用真实 storage 返回后缀闭合，不转嫁到公开接口。

资源仅包含 running=1、nesting=n、lock=l 的完整 typed owned 字节，既有 ready-storage core 与 CurTid；不插入强 current guard。三字节更新后统一回收进既有 storage，保持所有权、目标指针及任务/就绪记录。

## 独立非空堆与单因素对照

Probe：`audit/probes/V293ExitLockedCallTaskSimProbe.v`。

`LCmemory n l` 独立合并原 RTfull 就绪/任务记录与四个输出单元：nesting=150、lock=151、running=152、target 指针=93。`LCbase` 对任意合法字节证明此资源可满足；`LCnonempty_client_call` 对全部 n<256、0<l<256 证明同一完整调用，而非用几个边界样例替代全称。没有 helper 绑定、decoder 表或预分配 saved。

前瞻协议在编写新源文件前冻结：只在 `LCmemory 1 1` 上把 lock 字节从 1 改为 0。`LClock_control` 构造真实 store/load，逐地址证明其他内容不变，锁 guard 从 false 变成 true。**这不是完整调用执行消融**：该 probe 的程序根本没有 helper 绑定，不证明 lock=0 的完整调用能完成，不据此推论下游 helper/切换机制的必要性。输入 nesting=1 的控制对应递减后零的分支，但实验本身仅运行锁 guard，不冒充完整前缀执行。

## 范围与未解决问题

- 仍限定 IE=false、si=nil、ISR 全清和空 LINV，不推广到任意中断栈/开启中断状态。
- 是既有边界归一化 AST，不是新增 C 前端或原端口 refinement。
- 同一源码版本、配置、AST、框架与 ADR-0010 均不改。
- 等优先级与强 current guard 缺口、统一 OSIntExit 规格、WFIFun/WFInt、同程序 K1–K4、GOOD_OS 仍未闭合。
- 不修改源码覆盖数据库把局部结果冒充 full_target_linked；不提交/推送，目标 active。

## 复验与证据

目录 `audit/logs/stage292-exit-locked-call/` 保存前瞻协议、2104 项旧文件基线、源码定位、每次编译源码快照/原始失败日志、两次同 SHA 编译结果、逐根 assumptions、递归 coqchk、全库回归和检查点。旧失败保留，原有测试及冻结记录不改。

源码准确定位：`os_core.c:693-736` 的 OSIntExit，身份和行锚点见 `source-identity.json`。本步直接记录准确函数/分支，不继承旧历史报告的错误函数描述。

复验命令（仓库根目录）：

```bash
PYTHONDONTWRITEBYTECODE=1 python3 -B audit/logs/stage292-exit-locked-call/checkpoint.py
```

最终实测以 `verification.json`、`test-delta.json` 和 `trust.json` 为准；局部通过与全库失败分别报告。封存直接运行 seal，待日志写入者全部关闭后记录长度与哈希，避免把正在写入的自身输出纳入 manifest。清理仅限列明的一次性 Trust 文件及缓存备份，保留原缓存、既有字节码、依赖与交付验证产物。

## 下一步

接等优先级“不切换”分支，再把资源与分支规格统一到 OSIntExit 的函数级接口。随后仍需完成整个固定配置程序的 WFIFun/WFInt 与 GOOD_OS，而不是以证明文件数量验收。
