# 第305步：同一 builder 驱动 EOI/Enter，并保留后继资源

## 本步解决什么

第304步只取原始 `BuildintPre` 的环境、内存投影来执行 Enter 调用，尚未连接输入 task state 的中断上下文，也没有证明调用后仍拥有原 ready/TCB/storage 资源。

本步稳定接口是 `V293_builder_enter_prefix`。它从同一份未过滤 builder 开始，构造实际的局部运行：

`handler wrapper → EOI → 完整 OSIntEnter 调用 → OSIntExit 调用入口`

结果中的执行轨迹、canonical snapshot、控制状态读取及内存 frame **共用同一个 `Mf`**。保留的资源不是调用结束后由前提重新假定的另一份堆。

## 如何理解这段证明

1. **从资源中读上下文。** `V293_builder_snapshot_context` 得到实际局部环境为空、ISR、IE、中断栈、临界区栈和抽象操作。主定理没有要求调用者另外提供这些事实。
2. **连接实际 EOI。** `V293_builder_snapshot_isr` 先证明 physical payload 的 `GoodFrm` 传输；主定理再用 `eoi_step` 建立真实语句执行。二者不能互相替代。
3. **执行与资源更新用同一内存。** `V293_builder_snapshot_enter_memory` 用实际 store 更新 nesting 字节，再用 store 结果唯一性把资源更新的内存等同于执行使用的 `V293_control_enter_memory`。未启动或饱和时保持原内存。
4. **组合完整调用。** 主定理调用既有完整 Enter 调用定理，按真实语句步骤推进到 Exit 入口；在该位置读回固定前端的 Enter 结果，并保留除 nesting 字节外的内存。

输入 ISR 不需要额外假设 `ir i=false`。结论忠实保留 `isrupd (isrupd ir i true) i false`；不能在没有条件时把它说成还原整个原 ISR。输入抽象状态始终是同一个 `getabst st`，不是任意重新选择的状态。

## 非空实例与单因素对照

`audit/probes/V293InterruptBuilderEnterResourcesProbe.v` 从既有非空 ready/TCB/storage 资源构造原 `BQpre`，实例化深度 0、254、255，对应 Enter 后 1、255、255。实例同时包含完整局部前缀、后继 snapshot、控制读取、固定前端一步和字节外 frame。

对照在编译前冻结协议和源身份，仅把后置观察 `ExpectedEOI=false` 改为 `true`；程序、地址、输入、完整证明后缀均不变。两侧都先完成 `Completed : BRrun 254`，变体在最终 ISR 观察处被拒绝，失败上下文仍包含实际 `Trace`、`After`、`Read` 和 `Frame`。

**这是后置观察的反事实敏感性检查，不是删除 EOI 语句的执行消融，也不验证后续 Exit。** 首次生成对照存在分词错误，原协议、源及失败日志保留；第二版协议在两侧重新编译前冻结，没有改写首次失败。

## 验证入口

- 生产模块：`certiucos/v293/proofs/V293InterruptBuilderEnterResources.v`。
- 默认构建登记：仅向 `_CoqProject` 追加上述生产模块。
- 新测试：`tests/test_interrupt_builder_enter_resources.py`，6项。
- 实测证据：`audit/logs/stage305-builder-enter-resources/verification.json`、`trust.json`、`stable-compiles.json`、`full-tests.json`、`ablation-results.json`。
- 只读复核：在仓库根目录执行 `PYTHONDONTWRITEBYTECODE=1 python3 -B audit/logs/stage305-builder-enter-resources/checkpoint.py`。

Coq 的源输入在每次运行中保持不变；递归内核检查与全部新结论的依赖报告分别保留。旧失败、编译开发失败和错误变体日志不删除；未通过的旧审计不改成通过。缓存恢复和一次性文件清理有逐项清单。

## 仍未证明的部分

- 输入是 **handler-entry** 的 `BuildintPre`，不是证明初始化可达的普通任务状态经过 `pint` 到达该入口。
- 本步是有限局部执行存在性；不是 `TaskSim`，不提供所有交错的 safety。
- 后继拥有 canonical snapshot，但尚未重建完整旧 `Inv`／统一 `WFInt`，也没有完成整个 Exit 和上下文返回。
- 输入 `aop` 尚未与统一旧中断规格的完整模拟连接。
- 整核源码级 `GOOD_OS`、同程序 K1–K4、初始化连接仍开放，uCOS3 尚未开始。目标保持 active，不提交或推送。

下一条纵向连接应消费本步实际得到的 snapshot 和同一个 `Mf`，继续完整 Exit/返回及旧规格连接；不能再用另给读值、另给可写权限或另给后继资源来绕开连接义务。
