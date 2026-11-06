# 第118步：预留半权限接真实优先级槽写入

## 本步的实质进展

`OS_TCBInit` 首个 Hook 后，原代码再次进入临界区，把新 TCB 指针写入 `OSTCBPrioTbl[prio]`，随后退出临界区。本步用真实 `encrit1_rule`、物理赋值规则和 `excrit1_rule` 连接这一段，不把写入替换为后置假设。

生产文件：`certiucos/v293/proofs/V293TCBOwnedPriority.v`。供成功后缀向上组合的接口为 `V293_OS_TCBInit_owned_suffix_after_first_hook`：

```text
本步后缀接口：首个真实Hook调用 → encrit → 优先级槽写入 → excrit
唯一剩余Hoare前提：第二个Hook → 任务链/ready发布 → 返回0
```

名称中的 `after_first_hook` 指本步推进的边界；接口结论仍包含首个 Hook，使用第117步同一种类型化契约。它不是原完整函数体接口：与第117步分配后参数/局部视图的转换尚未连接，不能声称完整函数体已经无条件推进到第二个 Hook。

## 权限为什么足够，又没有多拿

| 时点 | 创建者 | 共享池 |
| --- | --- | --- |
| IE=true、首个Hook前后 | RESERVED槽的半权限、私有已初始化TCB及局部参数 | 同槽另一半及原共享资源 |
| encrit后 | 两份半权限重拼完整写权限；读取真实prio和ptcb单元 | 资源暂借给当前临界区 |
| 物理写入后 | 槽位实际变为新TCB指针 | 准备归还新值 |
| excrit后 | 私有TCB、原调用者frame；不残留旧owner半权限 | 原同一个Inv接收新指针的完整槽权限 |

复用第112步既有 `HalfPermMap` 与值决定权限的池；同地址的两份半权限通过 `join` 合并，而非错误地声称内存地址不相交。新指针不等于 RESERVED 是显式前提，尚未从生产分配器不变量导出。若新值仍是 RESERVED，池只接收半权限，不能套用本步归还引理。

写入地址由真实 `prio` 字节、局部/全局变量绑定及数组索引推导，写入值从 `ptcb` 真实局部单元读取。调用者的局部绑定留在 `GoodFrm` frame，未塞进要求环境无关的 `GoodFunAsrt` Hook 资源。首个调用仍使用 `call_rule`；Hook函数体不是已完成部分。

## 可满足性与单因素对照

`audit/probes/V293TCBOwnedPriorityProbe.v` 复用原 `ROInv`，构造局部变量、预留槽、head、counter和保留值的真实字节内存。它证明同一物理状态满足调用者半权限与共享不变量；`OPBracketChecked` 无额外Hoare前提地闭合原三条语句，`OPSameInvariantBeforeAfter` 使用同一个Inv接收前后不同槽值。

对照计划在控制源之前保存。两组固定物理输入、实际ptcb参数、旧槽读取、期望指针和最终证明脚本，仅改变 `OPObserve` 中是否执行一次 `store`：正常组取得新指针；省略组仍读到 RESERVED，先通过共同输入检查，再在最后错误期望处编译失败。正向定理 `OPOmittedSlotDiffers` 独立证明两者不同。

这只隔离一次类型化物理写入/读取，**不是完整函数执行或Hook实现变异实验**。字面非空实例覆盖临界区写入片段，没有构造完整首Hook加已初始化节点的成功后缀可达实例。

## 验证与边界

本步日志、全部失败编译快照、单因素对照、全新增证明根的 `Print Assumptions`、活动模块和两个探针模块的 `coqchk`、增量构建及测试位于 `audit/logs/stage118-tcb-owned-priority/`。终态以 `checkpoint-report.json` 为准；没有该报告时不算冻结完成。增量构建不是clean build，旧失败记录不覆盖。

尚未完成：

- 与原分配后完整局部/参数视图连接；生产分配器的freshness约束。
- 第二个Hook、发布、成功返回0及标准完整函数契约。
- 两个Hook函数体、`WFIFun`、生产全局Inv、初始化可达性。
- 源码级 `GOOD_OS`、同程序K1–K4；uCOS3未开始。

原C、AST、配置、框架和冻结源码身份不变；本步核验实际上游切片和模型哈希，未重新replay修补后的逻辑源码树。六门仍为 `94/1/1/1/1/0`，不因新增条件后缀接口增加整函数覆盖。全量测试旧423失败/1错误、旧身份过期审计和6行旧空白问题如实保留。

Git未提交/推送。清理只涉及本步一次性控制/信任检查源及产品，先逐一确认全部清单，再删除；保留交付源、可复用探针依赖、产品、失败快照及日志，恢复原算术缓存。
