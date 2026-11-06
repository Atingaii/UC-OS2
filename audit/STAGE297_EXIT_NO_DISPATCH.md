# 第297步：三种不调度原因共用完整调用接口

## 本步解决什么

固定对象仍为 uC/OS-II V2.93.01 的 `OSIntExit`，源码身份和行定位记录在
`audit/logs/stage297-exit-no-dispatch/source-identity.json`。
不改 C、配置、边界归一化 AST、框架或前步证明。

上一轮只把 running=0 分支接到了可调度分支使用的同一个存储不变量。
本步进一步把三种**不调度**原因连接成一个接口：

| 原因 | 准确条件 | 真实低层行为 |
| --- | --- | --- |
| 内核未运行 | running=0 | saved 分配/写零，跳过临界区，然后释放/返回 |
| 中断嵌套未退尽 | running=1，初始 nesting=2..255 | 进入临界区，递减后仍非零，不调用 helper，退出/释放/返回 |
| 调度锁定 | running=1，初始 nesting=0..255，lock=1..255 | 饱和递减；若嵌套归零，再由锁 guard 阻止 helper，退出/释放/返回 |

嵌套与锁定可以同时成立，不要求两者互斥。
临界前缀以 `nesting≥2 ∨ lock>0` 表示二者的并集，且两个输入都是有效字节。
nesting=0/1 且 lock=0 **不属于该活跃分支接口**。

## 对上层的接口

生产文件：`certiucos/v293/proofs/V293ExitNoDispatchCallTaskSim.v`。
唯一公开 `Theorem` 为 `V293_exit_no_dispatch_client_call_TaskSim`。

- 高低两层从相同客户端 `scall f nil` 出发。
- 三种情况都固定绑定 `fun _ => END None`，不是可任选调度的规格。
- 三种情况都使用同一个 `V293_ready_storage_inv` 和原 `RDYINV` 后置条件。
- storage 允许 `prefix ++ [nesting; lock; running] ++ suffix`，正好容纳原 enabled 调用的排列。
- 不把两个逻辑等价的断言直接当作同一个 `Inv`：实际证明 storage 拆分、重排和重新闭合。
- 公开前提没有 store/eval/cstep 执行结果或下游 `TaskSim` continuation。
- saved 仍由函数真实分配，覆盖全部 fresh 后继；不是调用者预分配。
- 不需要 helper 的程序绑定；被阻止的分支确实不执行它。

复用原 typed guard resource、nested/locked 前缀、分配、返回和 storage 后置引理；
没有新增 ready 模型、Inv 模型或资源 Definition。中间 body/entry 引理内构造的 continuation
不泄漏到公开接口。旧文件已封存，保留不动；新文件重用其具体遍历结构，以闭合不同位置的同一 storage。

## 非空输入与单因素对照

探针：`audit/probes/V293ExitNoDispatchCallTaskSimProbe.v`。

1. `NDsame_invariant` 是 Coq 值相等式：新 storage 排列精确等于原 `ACinv`。
2. `NDnested_original_input_call` 直接在原 `ACmemory n` 上构造完整调用（n=2..255）。
3. `NDlock_single_factor_complete_call` 只把原 `ACmemory n` 的 lock 字节从0写为 l。
   它证明 store 成功、更新后的 load、所有其他地址保持原值，以及更新输入上的完整调用。
   范围为 n<256、l<256 且 n≥2 或 l>0；因此也包括所有有效嵌套值上的非零锁。
4. `NDquiet_original_API_call` 将上一轮已证可构造的 `QSresource` 接到本轮公开接口。
   quiet 资源的非空存在性和单 running 字节输入对照沿用第296步，不另造新堆。

这些调用使用原 `ACpo`、`RCprogram`、`QCspec`、`ACinv` 和原抽象任务/事件/时间/current。
current/high/counter、两半完整 decoder、target、nesting、running 和任务记录所有权保留。
**其他地址相同描述的是调用前输入对照，不是新增逐字节返回后置条件。**

对于 n=0/1，lock=0 与 lock>0 的 guard 结果确实不同；对于 n≥2，外层嵌套 guard
已经阻止调度，锁不影响该决定。不把后一种相关早拒绝当作锁 guard 已执行的证据。
锁表达式的独立 eval 不冒充完整函数在所有 n 上都读取锁。
Python 测试穷举65536对有效字节，对照饱和递减后的 C guard 与 Coq 条件；这只是边界回归，
完整调用仍以 Coq 和递归 `coqchk` 为准。

## 尚未完成的整核义务

**本步统一的是全部三类不调度分支，不是整个 OSIntExit。**
enabled dispatch 仍使用 `sched ;; END None`。没有将两种不同 API 冒称成同一个，
也没有引入 `END ?? sched` 等任选行为。

当前抽象状态没有 running/nesting/lock 字段；如何使一个固定高层 API 精确判断是否调度，
并连接完整程序，仍需解决。已有 InfRules 的 logicvar 条件证明不等于这个缺口自动闭合。
限制仍为 IE=false、si=nil、ISR 全清、空 LINV；强 current guard、一般中断上下文、
统一规格和初始化、`WFIFun`、`WFInt`、源码级 `GOOD_OS`、同程序 K1–K4 都不能据此宣称完成。
uCOS3 尚未开始；目标保持 active，未提交或推送。

下一步回到 `framework/proof/toptheorem.v` 的实际整核入口 `verified_os'`：
先检查已有 `V293_OSIntExit_all_exact_dynamic_contract` 能否在同一内部函数环境、
同一 Inv 下供 `WFIFun` 使用，以及它与真实 ISR 的连接条件。
`OSIntExit` 的内部函数合同不能靠新增客户端 API 包装代替；
已有小环境的 `WFIFun` 也不能记为固定完整程序的 `WFIFun`。
缺失的抽象 guard 信息和强 current guard 需按实际连接点处理，不能用任选调度或放宽 guard 消掉。

## 验证记录

证据目录：`audit/logs/stage297-exit-no-dispatch/`。

| 检查 | 实测结果 |
| --- | --- |
| 最终生产证明与探针 | 同一源 SHA 各两次串行编译通过 |
| 全部新增证明根 | 12 根假设检查及递归 `coqchk` 通过；递归检查约566秒 |
| 假设依赖 | 仅既有 `classic`、依赖函数外延性；未新增公理 |
| 新增测试 | 5/5，通过65536对字节边界及完整接口/来源/内核证据检查 |
| `make build`，Coq 8.18.0、JOBS=1 | 通过；这是现有产物上的增量全工程检查，不是 clean build |
| 项目结构审计 | 通过，371个活动 V293 文件、103个 framework/tactic 文件 |
| 最终全量回归 | 2651项，434失败、1错误；失败/错误 ID 及顺序与第296步完全一致 |
| `make audit` | 仍失败，原 `stale function evidence input identity` 未解决 |
| `git diff --check` | 仍报告原 `framework/logic/inferules.v:581–586` 尾空白；本步未改该文件 |
| 旧检查点 | 原样运行后因新增 `_CoqProject` 追加而拒绝，未修改旧门槛 |

首次全量回归为2651项、443失败、1错误，**该结果保留在 `full-tests.json/log`，没有覆盖**。
多出的9项均报告 `.lia.cache` 与冻结基线字节不符。
先以一个原测试复现失败，再仅恢复 `.lia.cache` 原字节，保持证明、测试和项目注册不变；
这9个原测试全部恢复通过。随后完整重跑结果另存 `full-tests-after-cache.json/log`，
回到原434失败、1错误，且逐项、逐顺序比较一致。
这修复的是编译缓存漂移，不是解决了那434项历史失败。
单因素输入哈希和红/绿结果见 `cache-diagnosis.json`、`cache-red.json`、`cache-green.json`。

全部10次编译快照保留，其中5次失败：缺少直接 import、断言析取记号错误等。
`probe-02` 与 `probe-03` 是同一缺失 import 的重复失败，不给予额外独立验证信用。
最终同源成功记录、逐根假设和递归内核检查才是新证明的有效性证据。

清理前逐项核验并删除8个本步临时 Trust 产物和缓存备份；
原 `.lia.cache`、`.nia.cache` 字节及306个既有 Python 字节码保持不变。
源文件、探针、失败快照、日志与仍用于交付验证的编译产物保留。
未提交、未推送。只读复验命令：

```sh
PYTHONDONTWRITEBYTECODE=1 python3 -B audit/logs/stage297-exit-no-dispatch/checkpoint.py
```

本步检查点通过仅表示上述局部交付及其证据一致，**不表示全仓回归通过或整核完成**。
