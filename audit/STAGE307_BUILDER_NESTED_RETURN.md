# 第307步：同一 builder 连接实际嵌套中断返回

## 本步解决什么

306步停在 `exint` 前，不能把该终点当作已经返回。现在从框架原 `pint_step` 保存任务上下文，执行完整 `EOI → OSIntEnter → normalized OSIntExit` 嵌套分支，再用原 `exint_step` 消费入口创建的 `kint`。同一有限路径的最终全局状态严格等于原输入：任务代码、表达式 continuation、语句 continuation、caller 环境、整块内存、ISR、任务辅助状态及当前任务均恢复。

生产文件：[V293InterruptBuilderNestedReturn.v](../certiucos/v293/proofs/V293InterruptBuilderNestedReturn.v)。主接口是 `V293_builder_nested_global_roundtrip`。

## 推导顺序

1. 从 `BuildintPre` 打开真正的资源，不另给读取、写入、分配或执行成功的 oracle。
2. 复用306步同一后继堆的 snapshot 与 off-cell frame；从原/后继 `Amapsto` 分别推出嵌套字节的编码及 true 写权限，以映射外延性证明**整个后继内存等于原内存**，不从较弱的解码读数反推整堆相等。
3. 从原 builder 推出返回所需的低位 ISR 清空。对同一执行后继构造旧 `BuildintRet`，不额外要求所有 ISR 位为 false。该断言只在 `exint` 前的返回切点成立，不声称它在弹栈后仍以原形式成立。
4. 用原入口创建的 `kint` 封装局部轨迹，在全局语义执行；最终 `exint` 恢复原上下文。入口一步和返回一步都在主定理结论中明确要求，不能只拿自反多步闭包的零步证明冒充 roundtrip。
5. `V293_exint_kstop_blocked` 另证 `exint + kstop` 本身不能执行：306的终点确实缺少本步补上的保存上下文。

## 非空实例与单因素对照

[新 probe](probes/V293InterruptBuilderNestedReturnProbe.v) 复用原 ready/TCB/storage 非空资源；深度1和254、交叉 shadow 两个控制变量的非空 caller、非平凡表达式 continuation、非空语句 continuation，以及另一个保持 true 的 ISR 位，均实例化同一接口。两次真实调用使用306明确的二函数 `BNprogram`，没有换成函数体不同的 `RDprogram`，也不是完整 kernel program。

事前协议见 `audit/logs/stage307-builder-nested-return/protocol.json`。后置观察对照仅把已完成路径的 caller 期望从 `NGcaller` 改为 `emp`；两侧先获得同一 `Entry/Body/Return` 与同一非空堆。它检验**完成后的上下文观察敏感性**，不是删除 `exint` 的执行消融，更不是证明所有机制必要的证据。首对观察双方缺直接 `RIabstract` import 而提前失败，不计有效实验；协议02在两侧相同补齐 import 后冻结，旧失败和快照不覆盖。

## 核查与历史失败

全部实测、耗时、稳定编译、递归 `coqchk`、完整回归、缓存恢复和逐项清理以本步日志目录的 `verification.json` 与 checkpoint 为准。新自动化测试为 `tests/test_interrupt_builder_nested_return.py`；文本守卫只是回归，不代替 Coq。

306基线全回归为2711项、437失败、1错误。305历史测试精确锁死旧 `_CoqProject`，306合法追加注册已触发该历史失败；本步不修改旧测试、不漏注册、不改旧证据以制造通过。构建通过与全仓回归通过必须分开报告。`make audit` 的旧函数证据 input identity 失配和旧六行尾空白同样保留。

本步实际核查已完成：

| 核查 | 实测结果 |
| --- | --- |
| 生产与 probe 稳定重编译 | 各两次通过，输入源码哈希一致 |
| 串行增量构建 | 通过 |
| 递归 `coqchk` | 通过，9个根结论，437.260秒；仅保留既有两项逻辑假设 |
| 新自动化测试 | 6项全部通过 |
| 全仓回归 | 2717项，437失败、1错误，88.514秒；失败及错误的ID和顺序与306完全相同 |
| 项目审计 | 通过，381个活动 V293 文件、103个 framework/tactic 文件 |
| 综合审计／空白检查 | 保留上述旧失败；空白检查日志与306逐字节一致 |
| 检查点 | `verification.json` 的局部检查通过；整目标仍未完成 |
| 清理 | 逐项确认后删除17项本步观察／信任检查临时文件；保留失败快照、日志、交付源码及可复用编译物 |

根缓存已恢复到本步开始时的哈希，原306个 Python 字节码文件保持不变。306证据清单中非可变项保持原字节；`README.md`、`VERIFICATION_STATUS.md` 只前插，`_CoqProject` 只追加新生产文件，不能宣称306清单中这三项当前仍与旧哈希相同。Git HEAD 保持 `1f57743c638c7e1ccdcc594e51dc90c0c7406789`。

## 仍未完成

- 分支范围：running=1，原嵌套深度1..254；锁字节在 builder 原范围内，不另加 quiet/最高就绪过滤。
- 原深度0、255、未启动、外层调度切换不在本接口内；255饱和时不能声称 Enter/Exit 恢复原深度。
- 输入资源在 `pint` 产生的 handler-entry 同一堆上给出；没有证明它从初始化可达。另一个 ISR 位为 true 的实例也不是初始化可达性的证明。
- `intspec i` 仍限 `END None`；不代表任意中断高层规格已经统一。
- 这是特定有限执行存在性，不是全交错 safety、`TaskSim`、统一旧完整 `WFInt` 或整核 `GOOD_OS`。
- 临界语句遵循已有 ADR-0005 normalized 边界，不证明 raw port 实现。
- 源码级 `GOOD_OS`、同程序 K1–K4 尚未闭合，阶段一未完成；依老师附件，uCOS3仍未开始。

本步只保留本地工作，不提交或推送；旧冻结文件及失败记录保留。
