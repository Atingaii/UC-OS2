# 第65步：从 OS_TCBInit 调用入口连到成功返回（显式两个 Hook 义务）

## 本轮真正新增了什么

稳定接口 `V293_OS_TCBInit_success_call_under_hooks` 从七个实参已经求值的 `sfexec` 入口开始，连接实际参数/局部分配、空闲链取出、18字段初始化、第一个Hook的真实返回义务、优先级表写入、第二个Hook的真实返回义务、任务链/ready位图/计数发布、return 0、9对象29字节释放，最后恢复 caller。

与第64步不同，本轮不再从第二Hook已返回的锚点起步，也不要求调用者挑选9个fresh块或另给存活块Away：由输入内存有界性与存活字段地址上界一起构造。因此同一最终Mf可以同时保证全部已列字段/frame读回和29个callee字节不存在。15个不被发布修改的TCB初始化字段通过显式footprint交接，不会只证明发布字段而丢掉其余初始化结果。

## 必须保留的“如果”

两个 Hook 不是空操作。每个契约都要求从实际 `sfexec Hook` 到精确continuation上 `sskip None` 的真实 `local_steps`，并恢复所有列出的可写单元。允许未拥有内存变化，不要求整个输入输出内存相等。完整路径使用同一个P与连续内存 M→Mi→Mr→Mh→Mc→Ms→Mf，没有独立fixture拼接或中间执行结果前提。

**固定源码只声明而未实现 OSTCBInitHook、OSTaskCreateHook 等五个端口Hook。两个返回契约尚未兑现，本定理不是固定程序已经成功执行。** 独立probe使用任意P加显式契约作条件实例，不从缺Hook推导矛盾来伪造成功。同一四份有限入口另有无条件见证：实际到达第一个缺失Hook后没有下一步。

## 独立检查与证据入口

- `audit/probes/V293TCBCallSuccessProbe.v` 不导入旧audit probe；p12/p11 × 旧链头NULL/非NULL四份literal有限输入，入口所有权可满足性独立检查。
- 条件输出分别31/32项typed读取：15个其它初始化字段，9/10个发布字段，空闲链头后继、实际优先级表槽、邻槽与caller保护字/同名变量；IE任意，si/ci不变。它们是条件结论，不是已经执行的成功run计数。
- 终点负控在相同证明体中分别改变return/count/frame/free；只证明条件接口对错误结论敏感，不证明Hook可实现。
- 单因素消融仅改变P502查询是否有测试sentinel定义，比较相同第二Hook锚点的一步查询可用性；不执行sentinelbody，锚点未证可达，不授参数分配、Hook body、优先级写入、发布、return/free的独立消融信用。
- 成功与失败尝试、最终build/trust/回归/清理及sha身份见 `audit/logs/stage65-tcb-call-success/`，最终状态只看 `final-report.json` 与 `final-evidence-manifest.json`。

## 不能据此声称的结论

手工前端与ADR0005宏归一化仍擦除CPU_SR字节效应；未证明外层七个实参表达式求值。存在性无交错轨迹不是local Hoare或所有执行safety。fresh块仅保证避开已拥有存活单元的地址块，不为单元中出现的任意未拥有指针目标建立有效分配不变量。没有完整TCB/stack分配、链表无环、真实Hook实现、七调用实际Mf连接或完整OSInit。六门仍94/1/1/1/1/0，GOOD_OS与同程序K1–K4开放；uCOS3未开始。225源是增量构建，复用1120旧产物，不是cold build。未提交或推送。

## 接下来

把本条件接口用于 OSTaskCreateExt/OSInit 实际调用链时，必须继续显式传递缺失端口义务，或获得范围内真实端口实现再证明；不能临时加noop“闭合”。随后仍需初始化到运行期Inv、OSStart、源码级GOOD_OS及同程序K1–K4。第一阶段真正闭合后再做uCOS3。

### 下一段源码已经定位到的具体连接顺序

本轮重新提取的 `source/OSTaskCreateExt.body.c.snapshot.txt` 显示：

1. 检查 `prio<=12`，进入临界区并检查 `OSIntNesting==0`。
2. 检查所选 `OSTCBPrioTbl[prio]==NULL`，把槽先写成保留指针 `(OS_TCB *)1`，再退出临界区。
3. 调用尚缺实现的 `OSTaskStkInit(task,p_arg,ptos,opt)` 得到 `psp`。这是新调用者必须额外保留的端口义务，不能因已连接两个TCB Hook就忽略它。
4. 以 `psp` 为新栈顶调用本轮的 `OS_TCBInit` 条件接口；其旧表槽参数可以取保留指针，而不是强行要求NULL。
5. 按实际 `err` 分支：成功时只有 `OSRunning==1` 才调度；失败时须真实撤销保留槽，不能只证明成功分支就宣称该API完整。
6. 返回到 `OS_InitTaskIdle` / `OS_InitTaskStat`，再继续连接第57步七个初始化调用的实际Mf。这里仍未开始实现/证明上述调用者；该清单是下一步工作，不是覆盖成果。

这解释了为什么本轮虽然连到了返回，距离整核完成仍有真实的调用者、端口和运行期不变量义务，而不是再改一个“完成”标记即可。
