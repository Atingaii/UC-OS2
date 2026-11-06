# 第200步：从完整中断退出调用到实际切换

## 这一步解决什么

第199步停在原 `OSIntCtxSw()` 的调用入口。分析端口只有声明，没有函数定义，不能由声明编造可执行函数体。原框架 `pswitch_step` 会写当前 TCB 指针、挂起旧任务并切换执行者，但不更新 `OSPrioCur`。因此，裸指针切换不足以证明优先级缓存一致。

依据 [ADR-0010](../docs/adr/0010-中断切换调用点采用显式源码级抽象.md)，本步新增一个独立、显式的源码级调用点解释：

```text
OSIntCtxSw() → OSPrioCur := OSPrioHighRdy; switch OSTCBHighRdy
```

这不是端口 C/汇编实现，也不是原外部调用到原语的 refinement。原 C、配置、AST、临界抽象、框架规则及旧证据均不改写。

## 主接口与实际结果

[V293_OSIntExit_boundary_switch](../certiucos/v293/proofs/V293OSIntExitBoundarySwitch.v) 从真实已有的 `T/les/aus` 和空间所有权出发，构造一条原 `lpstep` 下的完整、不交错执行：

1. 实际函数调用、fresh saved 分配、初始化、进入临界区。
2. nesting 1→0、两级 guard、真实 OS_SchedNew 调用与返回、目标更新。
3. 从同一 task map 推导不同优先级，计数器递增。
4. 正常程序实际执行缓存赋值，再执行原 switch；执行者变为最高就绪任务，物理当前指针和缓存同步。

主接口不以 trace、分配、store、求值或逐步分类作为答案前提。为避免只在抽象 task map 中存在“幽灵目标”，要求每个抽象任务确有 code/env/aux 绑定；最终目标任务的这些绑定保持原值。当前指针和目标指针使用相同 TCB pointee type，以满足原 switch 规则。

**切换不等于旧任务返回。** 旧任务挂起的 continuation 明确保留 `excrit / sret / kcall / kint`，新分配 saved 的四字节仍存活。空间后置的 localenv/aux 是旧任务的逻辑视图，虽然抽象 current 已更新；不能据此声称新执行任务 IE=false，更不能声称它已满足生产 ISR invariant。

## 独立正控与单因素消融

[探针](probes/V293OSIntExitBoundarySwitchProbe.v) 重建非空 waiting6 / ready4 资源。为满足原切换的同 pointee 要求，仅在新见证中对齐全局类型环境；使用原 `SXmemory 1 6` 物理字节，旧见证不改。

| 检查 | 保持不变 | 可观察结果 |
| --- | --- | --- |
| 初始 IE=false / true | 同程序、物理堆、任务与调用者；ci 任意 | 两侧均完整切换；旧任务保存各自原 IE，counter=20，saved 四字节存活，caller 同名 saved=23/local running=0 保持 |
| 仅删除缓存赋值 | 同输入堆、code/env/aux 及其余源码 | 两侧均实际切换到 ready4，当前指针均为 ready4，counter 均为20；正常 cache=4 一致，消融 cache=6 不一致 |
| 原始缺失端口模型 | 仍使用原 GXprogram / 原 sfexec | 关中断时仍无全局下一步；新抽象不冒充原模型的可执行 trace |
| 归一化边界 | 指定无实参调用有正控 | 指定端口的非空实参、值返回和 runtime 内部语句被拒绝 |

`sync:bool` 是两个静态程序的选择，不是新增 C 输入。消融两侧保存的 kcall body 自然不同；没有声称两个端点代码逐字相同，也没有声称任意程序的完整翻译器正确。拒绝控制不替代完整执行正控。

## 验证与证据

- [前瞻协议](logs/stage200-interrupt-switch-boundary/protocol.json) 在本步证明前冻结。
- [源码重建](logs/stage200-interrupt-switch-boundary/source-check.json)：OSIntExit 配置后定义 SHA-256 `eface83f6f4b0aa36685c3996ec8df5d48091ea2ccb2f62918fb03a91f3bd789`；OS_SchedNew 为 `6d156edfff0548ed63fdff59a400e8d0ca0e69813ef6bf0142d0ce1902443d71`。
- [稳定编译](logs/stage200-interrupt-switch-boundary/stable-compiles.json)、逐根假设与递归检查、结构回归及全量测试的最终实测以 [verification.json](logs/stage200-interrupt-switch-boundary/verification.json) 为准；失败编译快照、旧失败和审计失败全部保留。
- 独立重检：`python3 audit/logs/stage200-interrupt-switch-boundary/recheck-checkpoint.py`。

## 当前边界与下一步

本步只证明显式源码级抽象下存在的一条不交错执行。不包含真实端口实现/语义保持、旧任务恢复后的完整返回、生产 ISR 安装与 LocalInv、全交错保持、WFFunEnv、完整初始化或 GOOD_OS。六门仍为 `94 / 1 / 1 / 1 / 1 / 0`，uCOS3 未启动，总目标 active，未提交或推送。

下一步将挂起的旧任务现场与恢复规则相接；不能跳过恢复义务直接宣布中断退出闭合。全局生产环境及顶层模拟仍须逐项连接。
