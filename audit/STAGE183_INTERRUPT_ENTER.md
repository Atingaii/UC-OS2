# 第183步：原 OSIntEnter 的饱和计数与真实函数契约

## 这一步解决什么

上一步把 tick、调度器和三个时间 API 接到共同环境，但真实 CPU tick hook 和 ISR 义务仍未闭合。本步选择固定源码中真实存在的中断入口服务 `OSIntEnter`，先完成其函数体纵向连接，不用空函数替代缺失 hook。

源码为固定上游 `Source/os_core.c:663–671`；在只施加两类授权修复的临时源树中重放真实预处理，定义及函数体字节偏移／哈希与冻结清单逐项一致。`source-check.json` 保存定位和配置后全文。`OS_TRACE_ISR_ENTER()` 在当前 `os_trace.h` 展开为空语句，因此 AST 保留 `sskip None`。这不意味着 CPU tick hook 也为空。最初误把清单逻辑路径当成磁盘文件的失败保留在 `source-location-initial.json`，不计为通过。

## 初学者先看这张表

`run` 是调用前的 `OSRunning` 字节，`nest` 是调用前的 `OSIntNesting` 字节。

| 调用前条件 | 调用后 nest | 其他保持项 |
| --- | --- | --- |
| `run=1` 且 `nest<255` | `nest+1` | run、抽象 action、frame |
| `run=1` 且 `nest=255` | `255`，不回绕 | 同上 |
| `run=0` 或任何其他非 1 字节 | 原 nest | 同上 |

例如 `run=2` 不是“真就运行”：源码比较的是 **恰好等于 OS_TRUE=1**。证明覆盖所有 `run,nest<256`，不是只覆盖表中几个例子。递增与最终字节转换的实际表达式从拥有的字节堆推导，不将求值结果当作外部前提。

## 交付接口

- `certiucos/v293/code/V293OSIntEnter.v`：配置后原函数 AST，包括整数提升、饱和判断、字节转换及 void 返回。
- `certiucos/v293/proofs/V293OSIntEnterInternal.v`：原 updates/body 的 Hoare 推导、真实 `BuildPreI/BuildRetI` 契约及单函数 `WFFunEnv`。
- 稳定接口 `V293_OSIntEnter_internal_contract`：量化任意 `vl/lg`，直接接收真实 builder 结果；非法逻辑快照的入口为假，无效实参列表被原 builder 拒绝。合法入口的非空性另由物理见证验证，不用假入口充当主体证明。
- `V293_OSIntEnter_WFFunEnv`：原 `Tvoid/dnil/dnil/body` 的真实声明、domain、类型和所有 builder/body 义务。
- `audit/probes/V293OSIntEnterProbe.v`：独立构造三个不相交块，分别拥有 run、nest 和 CurTid 指针；空 local env、`IE=false`，action 固定为 `spec_done None`。

这里使用框架 internal-function 规则描述中断上下文中的普通 C 服务；冻结源码的分类仍是 **public / external**。局部 map 不是完整 API 分类、ISR 安装表或生产函数环境，未据此提升六阶段覆盖信用。

## 预注册对照及反向检查

协议在实现前固定，见 `protocol.json` 与 identity。

1. 固定 `nest=254` 只改变 run 为 1、0、2：原表达式分别读取真、假、假；结果分别为255、254、254。
2. 固定 `run=1` 只改变 nest 为254、255：room 表达式分别读取真、假，结果均255；255不发生字节回绕。
3. `IEnonempty_builders` 使用真实 byte heap 接受实际 builder 的完整入口，`IEactual_eval` 从空间所有权和空 local domain 推出原表达式读取，不设求值 oracle。
4. 同一实际堆 `IEmemory 1 255`、同一局部 domain、同一 run/action/IRQ：正确 post（调用前254）接受；仅将候选 post 的计数改为254（对应调用前253）时，由同一物理 `load Tint8` 与255冲突而拒绝。不是在入口 domain 或 run 处提前拒绝后冒称后置语义有效。

输出堆是独立构造的后置资源见证，不是这次从入口到出口的具体执行 trace。函数体正确性来自单独完整 `InfRules` 推导；没有把候选输出当作执行关系。探针空 LocalInv 只用于可满足性测试，生产接口仍量化任意良构 LocalInv。

调试保留全部失败编译快照和日志。其中一次探针的隐式 `apply` 在庞大空间断言转换上长时间运行，主动中断后改用已确定实参的 `exact`，未改变任何目标断言。builder 连接过程中发现分离合取是右结合，已按真实 builder 形状修正接口，未更改框架规则。

## 验证与边界

稳定编译、所有新定理根的假设打印、两入口递归 `coqchk`、完整测试两轮的旧失败 ID 对照和清理记录，以 `audit/logs/stage183-interrupt-enter/verification.json` 为准。所有失败编译证据保留，旧记录不重写。

| 实测项目 | 结果 |
| --- | --- |
| 稳定 code/body/probe 编译 | 全部退出0，当前源码与各自冻结编译快照哈希一致 |
| 全部新引理／定理根 | 34根；实际假设只有 classic 与 dependent functional extensionality |
| 两入口递归 coqchk | 退出0，约228秒；582个 Coq 输入在检查期间未变 |
| 新增回归 | 5项全部通过 |
| 全套回归 | 2078项，仍为423失败／1错误；与2073项基线的失败、错误 ID 精确一致；最终再跑一轮核对 |
| make build／project-audit | 均退出0 |
| make audit | 退出2，保留原 stale function evidence input identity |
| git diff --check | 退出2，仅原 inferules.v:581–586 的六处行尾空白；旧文件不重写 |

本步不提交或推送，也不把“仍有旧失败”改写为整套通过。收尾先输出逐文件清理清单，再删除本步临时假设驱动／产物及新生成的 Python 缓存，并恢复原有 lia/nia 缓存；证明源码、失败日志、快照和可复用 Coq 编译产物保留。


源码注释要求调用时已经关闭中断。本契约用 `Aie false` 明确保留这一前提；它**不证明**调用者已经正确关中断、嵌套计数等于实际硬件嵌套深度、与 `OSIntExit` 配对或资源具有生产全局初始化来源。没有证明完整 ISR 或中断交错 simulation，没有实现缺失 CPU hook，没有完整生产 LocalInv、整环境／初始化、同程序 K1–K4 或最终 `GOOD_OS`。

六门保持 `94/1/1/1/1/0`；第一阶段未完成，uCOS3 未开始，总目标仍 active。下一步从实际 `OSIntExit` 与中断调用资源继续接，而不是把局部饱和计数结论称为整核完成。
