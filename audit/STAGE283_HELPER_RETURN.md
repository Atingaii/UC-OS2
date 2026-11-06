# 第283步：helper 字节局部释放与真实返回的 TaskSim

## 当前结果

唯一最终目标仍是固定 uC/OS-II V2.93.01 的整核源码级 GOOD_OS 与同程序 K1–K4，完成后再进入 uCOS3。本步没有更改范围或把局部成功当作最终验收。

生产文件 `certiucos/v293/proofs/V293SchedHelperReturnTaskSim.v` 已登记 `_CoqProject`，唯一公开接口 `V293_sched_helper_return_TaskSim` 从以下资源开始：

- 原始 `OS_SchedNew` 函数绑定及其一字节局部环境；
- `Amapsto (b,0) Tint8 true v ** R`，其中 `R` 不依赖局部环境、包含当前任务指针资源；
- **恢复后调用者 continuation** 对 `R` 的 TaskSim。

结论覆盖原始后缀的四步：`SKIP;kseq sret` → `sret` → 释放一字节 → 空释放列表恢复调用者环境 → 调用者 continuation。没有插入新的程序步骤。内部从空间所有权推导实际 free，公开接口不要求 free、trace、任意 frame 的成功步骤或这段返回后缀本身的 TaskSim。

任意兼容共享/外部 frame 都由 `free_mono`、`join_free` 扩展并保留。使用已有真实后继唯一性与 `V293_invariant_cstep_TaskSim` 逐步连接；不改动内核 AST、C 或框架。

## 独立控制及其证据范围

独立文件 `audit/probes/V293SchedHelperReturnProbe.v` 不登记生产工程。

- `HRnonvacuous_return`：使用既有非空当前指针资源堆，真实 fresh 分配一字节 raw `Vundef`，构造返回后缀 TaskSim；调用者 post 保留 `CurTid ** Atrue`，不是无条件 True。该 raw 实例用于资源接口非空性，**没有声称 raw Vundef 是执行完 helper 两个赋值后可达的值**。
- `HRchoice_erased`：任意两个不同的合法 fresh 选择，在两次字节写入所表示的堆上，各自执行真实四步返回，最终得到同一个完整物理堆（只更新 high，无局部泄漏），恢复同一 caller。`HRtwo_choices_exist` 保证不同选择确实存在。这里调用已有 `V293_sched_storage`，不是新增分配消除机制；此控制本身**不证明这些写入堆从原函数体可达**，原两赋值的 TaskSim 仍需连接。
- `HRowned_boundary`：保持整体堆不变，仅把任务拥有部分改为空、原堆全作 frame，则拥有堆上的 free 失败，字节所有权断言不成立。这是分区/所有权控制，不是完整程序执行消融。
- `HRframe_preserved`：拥有字节时，对任意兼容 frame，真实释放前后仍与同一 frame 相连。fresh 选址被占用排除的控制沿用第282步 `HAframe_excludes_old_choice`，不以本步释放检查冒充新的分配覆盖证明。

## 验证与现有问题

详见 `audit/logs/stage283-helper-return/verification.json`。稳定编译两遍、逐根假设和递归 coqchk 检查当前模块及依赖；完整测试保留旧失败身份与顺序。已有审计证据身份过期、历史空白错误不改写，不通过降低 gate 制造全库通过。

预注册协议第二项若按“原两个赋值已执行并可达”解释，目前并未完成：本步只对构造出的写入后堆证明返回与选址消除；占用排除沿用282的已有证据。因此记录局部返回检查点通过，但 `protocol_fully_completed=false`，保留真实函数体可达性为后续义务，不改写冻结协议。

限制：`ie=false`、`si=nil`、沿用空局部候选 `V293_shared_li`。非空资源见证只覆盖返回后缀，不是原完整活跃调用入口的非空 TaskSim；没有任意中断交错、初始化可达性或完整执行消融结论。

## 下一条必须连接的义务

第282步的调用/分配前缀仍要求每个合法 fresh 块上的 helper 函数体 TaskSim；本步只闭合了这段函数体尾部的释放和返回。接下来必须从 ready invariant 与局部/high 字节所有权证明原两个赋值的 TaskSim，组合本步返回，再对接第281步目标赋值后缀，最后消去第282步的函数体前提。

**完整 helper 资源闭合尚未完成；完整入口 TaskSim、GOOD_OS、同程序 K1–K4 未完成，uCOS3 未开始。** C/配置/AST/框架/ADR-0010 与282及以前证明和冻结日志不变，本步不提交/推送。
