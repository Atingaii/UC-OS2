# 第149步：原 tick 单次循环接入同一任务表与 ready bitmap

## 这一步解决什么

第148步已连接共享时钟，但没有把运行中的 TCB 更新与共享抽象任务表接上。本步的稳定接口是
`V293_tick_wait_iteration_refines`，对象仍是冻结 `V293OSTimeTick.v` 中的原 `V293_tick_iteration`，不另造执行程序。

这里的“原循环”指已有冻结语句 AST（临界区使用 `encrit/excrit` 原语）；本步没有验证新的 C 前端翻译，也不等于 raw enter／exit 调用、CPU hook、局部分配及 ISR 封装已闭合。

该接口从可写字段所有权构造原循环的真实局部执行，输出的**同一个 `Mf`** 同时满足：

1. 目标任务的实际字段与更新后的抽象任务记录相符；其余任务记录保留。
2. 更新后的任务表仍满足原优先级表关系；实际新 ready 行与新任务表相符。
3. 原 `spec_prim_step` 执行一次组件抽象动作，只更新 `abstcblsid`；其他抽象槽位不变。
4. 新任务表重新放回原 `V293_shared_fields`，其余物理与抽象 frame 保留。

这不是从成功的 loads 反推可写权限：入口提供 full-permission 空间断言，原存储的存在性由旧节点执行定理构造。

## 精确范围

- 优先级 `p<13` 且 `p<>12`，基址及字段偏移不越界；输入两行均为字节。
- 等待原因为 time／sem／mbox／q／mutex，**不带挂起位**；倒计时为任意 uint32。
- `Dly=0` 不推进，`Dly=1` 到期并 ready，其他正值减一。
- event 等待的 timeout 清 pending 状态、更新独立 pend 字段；event 指针仍在 frame 中拥有，不假定它自动消失。
- 抽象记录本身尚不记录独立 pend result；不能因此声称 Pend API 的超时返回证明已闭合。
- `V293_tick_wait_step` 是单节点组件动作，不等于整个生产 tick 规格。

本步还做了一项有实际结果的简化：从 `V293_tick_wait_bitmap_tasks` 删除未使用的优先级表参数／前提，编译仍通过。优先级表仅在最终需要证明其自身保持的接口处保留。

## 入门时容易混淆的一点

`ready` 表示“可以获得 CPU 继续执行”，不表示“已经收到消息／等待成功”。本段 tick 在倒计时到期后也会让未挂起任务进入 ready；事件等待的结果另用 `OSTCBStatPend` 标记 timeout。因此，“还没收到消息”不意味着任务在超时后仍必须保持 waiting。挂起位是另一项独立条件：有挂起位时，到期也不能在 ready bitmap 中加位。

本步还没有证明任务恢复后整条 Pend API 如何读取并返回这个结果，不能把上述节点级字段更新等同于 API 全链路证明。

## 入口非空与消融

探针 `V293TimeTickTaskBridgeProbe.v` 先用独立 encoded bytes 构造空间入口，再调用生产接口。入口包含一项信号量等待任务（优先级10、非零TCB偏移）、原局部指针、两行 bitmap、消息／event 指针、非空共享抽象槽和 canary99。它**没有 idle task**，不是初始化可达内核状态；非空入口只排除本接口前提不可满足这一问题。

| 检查 | 保持不变 | 唯一变化／观察 | 已建立的结论 |
| --- | --- | --- | --- |
| 倒计时对照 | 同一真实执行及 `Mf`、其余任务字段 | 新抽象 delay=2 与旧 delay=3 | 新记录成立，旧任务表记录不成立 |
| 漏设 ready 位 | 同一到期执行、更新后的任务表 | bitmap 行4改为0 | 正确对应成立，缺位对应被拒绝 |
| 漏改任务表 | 同一到期执行、bitmap 行4 | 新表改回旧等待表 | 对应被拒绝 |
| 挂起边界 | 旧原节点执行、输入 Stat=9、Dly=1 | 观察实际输出 Stat=8、Pend=1、group=1、row=128 | 保留挂起且不唤醒；不能塞入无挂起节点表示 |
| 抽象 frame | 同一抽象输出任务表更新 | 查看非 `abstcblsid` 槽位 | 值全部不变 |

前两项漏更新是**执行后的关系对照**，不是两个不同 C 程序的执行比较；不存在“入口先拒绝，所以所有后续机制都通过”的推断。实际正确执行后的 group=2、row=4 也从同一 `Mf` 的空间所有权读出。

## 验证与证据

固定输入身份、前瞻协议、逐次成败快照、构建、全测试、原审计、独立 `Print Assumptions`／`coqchk` 和最终只读复核集中在：
`audit/logs/stage149-tick-task-bridge/`。

本轮实际结果：

| 检查 | 结果 |
| --- | --- |
| `make build` | exit 0 |
| 新增身份／接线检查 | 6／6通过 |
| 新证明根 `Print Assumptions` | 16根；仅沿用 classic／dependent functional extensionality，无新增公理 |
| 独立 `coqchk` | 317活动模块＋38额外探针模块，共355个显式目标，exit 0 |
| 全量回归 | 1876项；旧423失败、1错误，失败／错误 ID 集合与第148步完全相同 |
| `make audit` | exit 2；保留 `stale function evidence input identity` |
| `git diff --check` | exit 2；保留旧 `framework/logic/inferules.v:581–586` 空白问题；新增源和文档另查无行尾空白 |

以该目录最终 `verification.json`／`checkpoint-report.json` 为完成核对依据。新增字符串／身份测试不代替 Coq 语义证明。失败或被终止的尝试保留，不覆盖成成功结果。

本轮收尾已逐一核对并移除8项一次性 Trust 文件／缓存备份，恢复原 `.lia.cache` 与 `.nia.cache`；保留源文件、全部成败证据及可复用 Coq 产物。清理后构建及全量回归已复跑，结果与上表相同，并纳入最终只读复核。

## 还差什么、下一步怎么做

1. 先把返回的单节点资源重组为列表尾部可继续使用的 owned-task/list invariant；尤其处理多节点更新时 `del tasks t` 的变化。
2. 将本接口嵌入原 while 的归纳，明确链表遍历、任务唯一性及全部任务（含 ready、idle、挂起、flags）的表示与保持。
3. 将运行分支与第148步的共享时钟放回同一生产 Inv／ISR 路径；不能用两个独立 fixture 的成功代替这一连接。
4. 补初始化、全生产 WFIFun／Inv 和同程序 K1–K4，再闭合源码级 `GOOD_OS`。其后才开始老师要求的 uCOS3。

当前不增加源码函数覆盖信用，六门仍是94/1/1/1/1/0。旧423失败／1错误及审计身份失败如实保留；未提交／推送，总目标 active。
