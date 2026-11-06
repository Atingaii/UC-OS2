# 第71步：任务创建成功后缀的实际分支与返回值

## 本步接通什么

固定 V2.93.01 配置后的 `OSTaskCreateExt` 在 `err = OS_TCBInit(...)` 之后还有实际源码，不能把它替换成空语句。本步保留并建模：

```c
if (err == 0) {
    ;
    if (OSRunning == 1) OS_Sched();
} else {
    /* enter critical */
    OSTCBPrioTbl[prio] = NULL;
    /* exit critical */
}
return err;
```

`V293OSTaskCreateExtSuffix.v` 定义完整后缀和拼接后的函数体。配置源码经重新展开、Clang AST 定位；94个函数身份与冻结清单一致。该映射仍是手工前端，沿用 ADR0004/0005/0007，未验证 C 前端、CPU_SR 字节效应、函数指针 ABI。

## 上层可以使用的稳定接口

`V293_OSTaskCreateExt_success_suffix` 从已写入 err=0 的真实后缀入口出发，实际执行 err 判定、空语句、`OSRunning == 1` 判定：

| 输入 | 实际停止位置 | 已做 / 未做 |
| --- | --- | --- |
| OSRunning=0 | `sskip (Some (Vint32 Int.zero))`，`kret ks` | 已求值 `return err`；尚未释放创建函数自己的局部对象、恢复它的调用者 |
| OSRunning=1 | `sfexec sched nil nil`，携带 `return err` continuation | 真实调度器调用入口；尚未查询、分配、执行调度器函数体 |

`V293_OSTaskCreateExt_success_dispatch_under_hooks` 将它与第70步从函数体入口到真实 err 写入的条件轨迹连续组合，不另造一份结果内存。两条后缀都保持同一最终 Mf；TCB 调用已释放的9对象29字节仍为 None；调用者 frame 和43项 typed 读取保留。OSRunning 全局字节加入 Hook 必须保持的 frame，显式要求局部环境不遮蔽该全局变量，不假设 Hook 保持整个内存不变。

仍有三个真实 Hook 返回契约：栈初始化、TCB 初始化 Hook、任务创建 Hook。本步没有实现或假造 noop；固定缺 Hook 的程序仍真实到达缺失入口后无下一步。

## 实例、消融和反例

- 独立字面函数体/返回入口可满足；完整条件实例为 p12、旧链头 NULL、非空栈、OSRunning=0，读回43项。结果列表共享生产公式，不作为独立结果语义 oracle。
- 生产定理泛化到 OSRunning=1，但没有声称存在完整函数体 running1 字面实例。本步 true 分支的独立可执行例是三字节后缀锚点。
- 前瞻单因素比较：仅把 `(33,0)` 的运行态字节从0改成1，其余全部地址完全相同，err=0 和 caller=77 均保持；两侧实际执行同一后缀而到达不同终点。信用只限成功后缀的调度决策，不扩展到 Hook、函数体前缀或整条创建路径。
- 正控先编译通过，再保持证明体不变，仅分别更改返回值、调度目标、caller 数据、已释放对象结果；四份类型正确的负控均在相应终点被拒绝。
- code01 缺少类型定义模块导入、proof02 的 Ltac 分支空格、dispatch01 缺 byteval 定义模块导入等失败均原样保留；最终身份为 code02/proof03/probe01/dispatch02。

## 验证和可信边界

234活动源（131目标源+103框架/tactics）增量构建，复用1160旧产物；不是冷构建。60个 Print Assumptions 根及 coqchk 的最终结果、5项新测试、全量1331项测试结果、旧396条诊断的顺序和分类比较、缓存恢复与清理数据均以本步 `audit/logs/stage71-task-create-suffix/final-report.json` 及 manifest 为准。既有395失败和1错误不能删除或改判为通过；默认 audit 退出2仍保留。

错误分支完整保留并做 AST 顺序核对，但没有证明错误清理的执行。本步不是 local Hoare、全执行 safety、无条件完整创建或 GOOD_OS。存在性无交错轨迹不等于所有执行正确。

五个端口实现（OSTaskStkInit、OSTCBInitHook、OSTaskCreateHook、OSInitHookBegin、OSInitHookEnd）仍缺；创建自身局部对象分配/释放和调用者恢复、实际调度器、OSInit 七调用连续内存尚未接通。六门保持94/1/1/1/1/0，同程序 K1–K4 开放。目标保持 active：先最终源码级 GOOD_OS，再按老师附件推进 uCOS3；没有提交或推送。
