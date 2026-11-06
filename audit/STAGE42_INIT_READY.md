# 第42步：实际就绪表循环与启动前空指针

## 这一轮解决什么

`OS_InitMisc` 清零运行标志之后，还必须初始化就绪位图及两个 TCB 指针。本轮连接固定 V2.93.01 的完整 `OS_InitRdyList`：真实循环、局部变量分配与释放、调用／返回。不借用已经运行的 `CurTid` 或 `CurLINV`。

目标仍是同一个固定程序的初始化相连 `GOOD_OS` 和同程序 K1–K4；之后才开始 uCOS3。本轮不是上述总目标完成，也不是完整 `OSInit` 的可达性证明。

## 源码身份与最小表示

- 上游、配置、两项授权补丁均未改。新鲜物化后重新预处理／Clang AST 检查全部94函数身份。
- `Source/os_core.c:1434–1449`，internal static `void OS_InitRdyList(void)`。
- definition SHA-256：`0bb8efa6f5d060f257ffc1dcbb82ba719bbd9456fa1289a0084f930cdfe55fe8`。
- body SHA-256：`e5d28a42c994bfbcea0cd6a6884ef033f4e77b6340cdd026c74f8ee19e80bcaf`。
- 完整配置后函数体和原始 Clang 子树见 `audit/logs/stage42-init-ready/protocol.json` 与 `gate01/source/result.json`。

| 实际 C 操作 | 模型／可观察结果 |
| --- | --- |
| `INT8U i` | 1字节局部；调用分配为 Vundef，退出释放 |
| `OSRdyGrp=0u` | 实际8位 store |
| `i=0u; i<12u/8u+1u; i++` | 固定界2；原生 `swhile`，不是把结果直接当成前提 |
| `OSRdyTbl[i]=0u` | i=0／1各写一次；退出i=2，没有访问第2行 |
| `OSPrioCur=0u; OSPrioHighRdy=0u` | 两个实际8位 store |
| `OSTCBHighRdy=(OS_TCB*)0; OSTCBCur=(OS_TCB*)0` | 两个实际指针 store，结果均 Vnull |

C 整数提升、常量折叠、for→while 和 void fall-through→sret 为显式手工建模；新鲜 C 文本和独立字面 AST 检查不等于已验证前端。没有把旧端口／hooks 替换为空实现。

## 生产稳定接口

源码：`certiucos/v293/code/V293OSInitRdyList.v`；证明：`certiucos/v293/proofs/V293InitRdyList.v`。

1. `V293_OS_InitRdyList_execution`：给真实名称绑定与8个可写原始单元（7个全局单元＋局部i；旧值允许 Vundef），从分离所有权推导 store 成功；完成真实两次循环和全部赋值，得到同一 Ms 的完整最终单元及分离 frame。没有把成功 store／期望最终值作为入口 oracle。
2. `V293_OS_InitRdyList_call_return`：给实际程序函数绑定、新鲜局部块和7个原始全局单元，执行 scall、sfexec、1字节 salloclv、完整函数体、真实 sret／free，恢复 caller。给出返回内存 Mf、局部字节已不存在，以及 Mf 与 Ms 在局部块之外逐字节相等。

**环境与 frame 边界：** 任意 R 从入口起就在最终 callee 环境解释，保留到函数体退出的 Ms。释放后不无根据地声称任意 R 在 caller 环境继续成立，只提供局部块以外的字节相等。调用前不要求局部字节已经存在。

这是存在性的、无交错的具体执行轨迹，不是 `local_hoare`／所有执行安全、不包含 ISR 交错，也没有连接完整 `OSInit` 的顺序组合、对象池或 `OSStart`。

## 独立非空样例

`audit/probes/V293InitRdyListProbe.v` 不导入前轮 probe：

- 明确有限内存：group=7，row0=3，row1=Vundef，prio=5，high=9；两个初始指针分别非空91／92。
- 两行共享同一块的偏移0／1，分离性按字节证明，不错误地假设不同数组元素必须在不同块。
- 局部块87在调用前确实 fresh，返回后 `(87,0)` 确实不存在。
- 另有32位哨兵123；入口可满足、环境映射和 fresh 都实际证明。
- 独立完整字面 AST 右侧不使用生产循环／序列生成器。
- 返回后的同一个 Mf 逐项读回7个全局单元和哨兵123，不只检查释放前的 Ms。
- 局部i=2仅在释放前读回；不把已释放局部当作仍可读对象。

## 前瞻单因素控制

协议在实现前保存；成功和失败快照／日志均保留。

| 控制 | 唯一变化 | 需要观察 | 严格信用 |
| --- | --- | --- | --- |
| `wrong-current-nonnull` | 独立最终读回 OSTCBCur 从 Vnull 改为非空92，所有 Proof 与生产 AST 不变 | 正常模型已通过，错误读回在后置连接拒绝 | 只授后置读回连接，不授语义执行或下游 |
| `loop-bound-one` | 生产循环界2改1，其他生产源不变；独立字面消费者及其 Proof 不变 | 正常字面消费者编译通过、突变代码编译通过、同一消费者在 AST 等式拒绝 | 只授字面 AST 对应，不授循环运行时或下游 |

拒绝点必须在各自连接处；不能把缺模块、语法错误或较早的生产证明不兼容当作负控通过。

## 未改变的边界

- 还没有完整 TCB／idle／stat／事件／标志／内存／队列初始化链、OSStart 可达性或真实运行 Inv。
- 零就绪表与空当前指针是启动中间状态，不满足运行期“存在当前任务”的条件。
- 物理／抽象时钟同步不由这个无抽象动作的函数建立。
- 不晋级正式六门；默认 audit 的身份过期失败和历史测试诊断必须保留。
- 复用已有生产依赖，不称为全仓 source-only 构建；不提交／推送或清理既有缓存。

下一步连接真实 `OS_InitTCBList` 和任务／对象资源，再组合 OSInit／OSStart 与运行 Inv。后续 hook、切换和 ISR 边界仍须逐项连接。

## 实际收尾结果

正式 gate01 九命令退出码 `0／0／0／0／1／0／0／1／0`：生产代码／证明／独立实例 coqc、独立 coqchk 三模块通过。生产2根／实例4根仅既有 classic／functional_extensionality_dep；字面 AST 为 closed。错误当前指针在第120行后置连接拒绝；界1在第16行独立AST等式拒绝；均不授语义执行／下游信用。

曾在 coqchk 尚未结束时过早运行测试：新8测试为1失败／2错误，全量1130为377失败／3错误，原日志保留，不计负控。待正式检查完成后重新运行同一测试：新增8项清理前后全过，全量1130为376失败／1错误；与上轮相同377项诊断全部保留，无新增／删除，前后 multiset 相等。没有删测试或弱化门禁。

范围／冻结C／diff检查0；默认audit仍exit2，stale function evidence input identity。正式六门保持94／1／1／1／1／0，不晋级。旧183活动源／915依赖及既有缓存未变；现185＝82目标＋103框架／tactics。既有基线仅README、状态、教程、project四条声明路径改变，缺失0；HEAD不变，未提交／推送；此前六份冻结manifest逐项无漂移。

清理前逐项确认类型、大小、hash／链接目标和目录成员，全部重查后才首次unlink：删除614项（553软链接、61实文件／1669774字节）及77目录，仅本轮3个控制工作树、2个新鲜C临时树和probe5产物。基线删除0；源文件、成功／失败快照与日志、既有缓存和依赖、10个新增可复用生产产物保留。不是全仓source-only构建。

最终报告：`audit/logs/stage42-init-ready/final-report.json`；冻结证据：同目录 `final-evidence-manifest.json`。本轮仅progress；GOOD_OS／同程序K1–K4／uCOS3尚未完成，总目标继续active。
