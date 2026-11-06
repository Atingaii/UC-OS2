# 第284步：原 helper 赋值、释放与调用的 TaskSim 连接

## 这次究竟前进了什么

固定对象仍是 V2.93.01、固定配置和原 `OS_SchedNew` AST。
源码位于 `os_core.c:1751–1759`；当前分支实际保留：

```c
y             = OSUnMapTbl[OSRdyGrp];
OSPrioHighRdy = (INT8U)((y << 3u) + OSUnMapTbl[OSRdyTbl[y]]);
```

第282步只证明调用与分配前缀，并要求调用者证明全部 fresh 分配后的函数体。
第283步只连接释放/返回。本步把两个原始赋值的实际表达式求值、真实字节 store、
释放和返回接到同一个 TaskSim，再覆盖全部合法 fresh 分配后继。
生产文件只有一个公开 `Theorem`：`V293_sched_helper_full_TaskSim`。

| 义务 | 当前结果 |
| --- | --- |
| 根据 ready 资源、unmap 字节所有权导出实际读 | 已证明 |
| raw Vundef 局部变为计算后的 y；high 改为实际选择优先级 | 已逐步接入 TaskSim |
| 在兼容外部 frame 下释放真实局部字节，恢复 caller 环境 | 已证明 |
| 所有 fresh block 的分配分支 | 已覆盖，不固定单一 block |
| 公开前提要求函数体 TaskSim、求值/store/free/执行结果 | 已消去这些前提 |
| 恢复后的 caller continuation TaskSim | 仍是组合前提，不是无条件 WFIFun |
| 原完整活跃调用入口非空 TaskSim | 尚未建立 |
| GOOD_OS、同程序 K1–K4 | 尚未闭合；uCOS3 未开始 |

## 资源与环境：没有放宽中断条件

资源是 `SWINVt ready ** (owned_high ** (read_unmap ** R))`，外部 `R`
要求 `GoodInvAsrt R`。不能把整个 SWINVt 当成任意中断状态都稳定的 GoodInvAsrt：
它包含真实的 `Aie false`。本步初稿对此的错误尝试和编译失败全部保存。
修正只使用 lenv 变化的稳定性，保留原 ir/aux/abstract state，不修改框架或 invariant。

真实局部所有权保证可写/可释放；raw Vundef 不是合法已初始化 typed byte，
因此不把它偷换成 typed old-y 前提。fresh 与已占用输入字节的区别由实际 load 推导。

## 非空实例与单因素对照

`HBall_fresh_body` 对同一已有非空 RH 堆上的**任意 fresh block**，从 raw Vundef
局部建立原函数体 TaskSim。`HBnonempty_body` 再由真实 fresh block 存在性得到存在实例。
这里终点 caller 是 `SKIP/kstop`，函数体入口位于真实 helper 的 kcall 内。
**这不是原完整活跃调用入口**，也没有用它冒充公开完整调用前提的非空见证。

`HBhigh_omission_control` 只把 high 的原赋值改成 `sskip None`：

- 两边相同 RH 初始堆、相同 fresh b、相同 raw Vundef 局部、相同原 kcall、相同 caller；
- y 的原赋值与真实释放/返回均保留，两边都实际执行到恢复后的 caller；
- 原程序 high 从 88 变为 4；省略 high 赋值后仍是 88；
- canary 两边均为 99，除 high 地址外整个最终物理堆相同；局部分配已释放。

这是原函数体加返回的单因素执行对照，**不是完整外层调用执行消融**。
本步没有单独消融 y 赋值，也不由 high 对照推断 y 或外层机制的必要性。
任意兼容 frame 的结论来自一般生产证明；canary 只是独立实例，不替代一般证明。

## 检查与保留的失败

前瞻协议、逐次源码快照、两次稳定编译、逐根 Print Assumptions 和递归 coqchk
均落在 `audit/logs/stage284-helper-body/`，以实测 `verification.json` 为准。
允许的既有基础只限 classic 与 dependent functional extensionality；不新增公理或占位证明。
直接计算整个大堆的两次慢检查被中断并保留退出码，改用已有子堆与所有权推导读取。

旧 C、配置、AST、框架、ADR-0010 和第283步以前的冻结材料不改写。
原有 434 个失败与 1 个错误必须保留，逐项比较身份及顺序，不能宣称全仓库通过。
首次全套 `full-tests.json/log` 为 2586 项、443 失败、1 错误：多出的9项全部
指向本轮编译更新的 `.lia.cache` 哈希，而非证明源码变化。诊断及完整原始结果保留，
恢复任务开始前备份的原有缓存后，重新运行同一全套，正式回归证据为
`full-tests-after-cleanup.json/log`，不覆盖首次结果、不修改旧测试。
`verification.json.full_tests_evidence` 显式指定正式文件，后续阶段不得误用首次结果作基线。
README 与状态文件仅前插本步说明；没有提交/推送。

## 下一步

把公开 helper 调用结论的恢复后资源接入已有目标指针赋值 TaskSim，
然后继续连接外层 guard、等优先级分支和临界区返回。仍保留 ISR、强 current guard、
空 LINV 与 ADR-0010 的已有边界；直到同程序 GOOD_OS 和 K1–K4 闭合前不开始 uCOS3。
