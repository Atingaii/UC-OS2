# 第161步：原 OSTimeTick 后 hook 路径的直接 Hoare 连接

## 1. 本步与最终目标的关系

目标仍是先闭合固定 uC/OS-II V2.93.01 的源码级 `GOOD_OS` 和同程序 K1–K4，再按老师附件推进 uCOS3。本步没有改变目标、版本、配置或授权修复，也不为六门 `94/1/1/1/1/0` 增加函数信用。

第160步已经有原 `while` 的 `InfRules`。本步把它向上连接到原 CPU tick hook 返回之后的完整剩余语句：

```text
encrit;
OSTime = OSTime + 1;
excrit;
if (OSRunning == 1) {
    ptcb = OSTCBList;
    while (原 guard) { 原 iteration; }
}
```

这里的“完整剩余语句”不等于完整函数：CPU hook、函数局部分配／初始化／返回及生产共享资源边界没有因此闭合。没有把 hook 关闭、换成 skip，或新造一份 AST。

## 2. 交付接口与不变条件

生产文件：`certiucos/v293/proofs/V293TimeTickPostHookHoare.v`。

- `V293_tick_clock_assign_hoare`：真实全局时钟 load、32 位加一、store，任意 `int32`，不要求“不发生回绕”。
- `V293_tick_head_assign_hoare`：从真实全局 head load 写入局部扫描指针，允许入口 scan 不是 head。
- `V293_tick_running_guard_owned`：从拥有的 `Tint8` 字节推导实际 `OSRunning == 1`，不接受外部给定 guard 值。
- `V293_tick_running_branch_hoare`：直接组合真实 `ift`、赋值和第160步原 while。
- **上层稳定接口** `V293_tick_post_hook_hoare`：结论直接使用既有 `V293_tick_post_hook`；原右结合 `encrit;(increment;(excrit;branch))` 不改。
- `V293_tick_post_hook_semantics`：仅经已有 `RuleSound` 正向导出，不把独立操作执行结果当成 Hoare 前提。

资源断言保留原 head、running 字节、完整选定任务字段、idle 字节、两行 ready bitmap 及任意合法 frame。运行值恰为 1 才把 scan 写到头部并遍历；其他字节值保持入口 scan、任务链和 bitmap，**时钟仍递增**。

两个局部交换引理只调整分离资源排列，使三个全局单元成为 while 的 untouched frame；不改变语句或执行语义。临界区在初始 IE 为真／假时分别复用原框架规则；任意取得的 `invlth_isr I` 原样保留、归还。

## 3. 非空入口与单因素检查

探针：`audit/probes/V293TimeTickPostHookHoareProbe.v`。

`PHspatial` 先从真实 encoded bytes 构造六个混合任务及两行 bitmap，再合并独立 readonly current 和 canary。初始 scan=idle，实际非空 head 指向另一个地址；不是把 head 赋值的效果预先放进扫描指针。`PHentry` 与 `PHrules` 联合表明同一字节入口满足公开规则的前置条件。

中断栈为 `[1]`、框架 `INUM=2`；对初始 IE 全称量化。该入口使用测试 `V293_witness_li`，不宣称它是初始化后可达的生产内核状态。

独立检查使用既有 `V293_tick_post_hook_owned_execution` 从**同一入口字节、同一合法控制栈**执行原后缀，不是运行新 `RuleSem`：

| 固定入口因素 | 观测 |
| --- | --- |
| `run=1`，时钟 `0xffffffff` | 时钟归零；指定任务 delay 3→2；group 0→3；全部选定循环字段、idle、两行 bitmap 有预期 load；canary=99 |
| `run=0` 或 `run=255`，其他条件不变 | 时钟仍归零；指定 delay=3、group=0、scan=idle、canary=99 |
| 只中和 head 赋值的效果，保留原入口 scan | `PHguard_before_head` 证明真实原 guard 为假，因 scan=idle 无法进入六任务链；实际 run1 输出则确实改变其 delay |
| 停止分支只把“时钟应递增”改成“保持旧值” | 同一个实际 `Mf` 拒绝旧时钟值；scan、bitmap、canary仍正确 |
| 运行分支只把“任务 delay 应更新”改成“跳过 head／while 的旧值” | 同一个实际 `Mf` 拒绝旧 delay；时钟、group、canary仍正确 |

最后两项是**结果单字段负控**，不是执行一份删除语句后的新 AST；不能由其中一项通过推断每个下游机制都正确。head 中和检查直接使用原 guard 的实际字节求值，不新增语义 oracle。

## 4. 信任边界与尚未完成的义务

caller 在进入后缀前就拥有 raw 全局／TCB／bitmap 字段。任意 IRQ invariant 被原样借还，**尚未证明从生产 Inv 借出这些共享字段再放回**；同样没有完成生产 LocalInv 的跨 API／ISR 连接。

框架规则是部分正确性／simulation，不据此声称一般并发调度总终止性。完整 tick 函数／API／ISR、CPU hook、初始化／WFIFun、GOOD_OS、同程序 K1–K4 仍开放，第一阶段未完成，uCOS3 未开始。

具体复现与实测结果见下一节。失败编译与旧测试失败不得删除或改写；旧 coverage identity 问题、旧 whitespace 问题如仍存在就如实保留。

## 5. 复现

```bash
make build COQBIN=/data/home/lucentzhou/.opam/default/bin/
PYTHONDONTWRITEBYTECODE=1 python3 -B -m unittest discover -s tests -p test_tick_post_hook_hoare.py -v
PYTHONDONTWRITEBYTECODE=1 python3 -B audit/logs/stage161-tick-post-hook-hoare/verify-checkpoint.py
```

`run-trust.py` 为首次封存脚本，拒绝覆盖既有日志；不要用它重写冻结证据。独立复核命令、新根、假设集合和源码稳定性见 `trust.json`；失败快照全部留在同目录。源码、配置和旧证明按 `baseline.json` 逐文件对照。

## 6. 实测结果

| 项目 | 实测结果 |
| --- | --- |
| 构建／清理后重建 | 退出0，原命令及日志保留 |
| 稳定编译 | 生产post08、探针probe07退出0，编译期间源哈希不变 |
| 独立内核检查 | 28个新增根；331活动＋51探针模块通过；coqchk 859.742秒 |
| 信任边界 | 实际classic／funext_dep／Eqdep未超既有allowed；537份Coq输入在检查期间不变 |
| 新增回归 | 7项全部通过；此前6项静态smoke不代替第7项内核门 |
| 全套回归 | 三轮均1958项、423失败／1错误，完整旧失败及错误ID集合保持 |
| 审计 | PROJECT PASS；旧coverage证据identity过期，make audit仍退出2 |
| 空白检查 | 仅旧framework/logic/inferules.v:581–586六行，退出2；新源／测试／说明无行尾空白 |
| 历史材料 | 核对26677份旧文件，仅README／状态／项目入口／生成依赖有预期差异 |
| 编译证据 | 保留15次快照和日志，包括12次真实失败；未删除不利结果 |
| 清理 | 逐项确认后删除8个一次性文件，共676050字节；恢复两份既有缓存，保留源码、失败证据和可复用Coq产物 |

10项对抗复核见 `adversarial-review.json`。验收以 `verification.json`、`checkpoint-report.json` 及身份清单为准，不以本表代替机器证据。
