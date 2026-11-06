# 第31步：真实 OSTimeTick 的有限 while 与同次字段归还

## 对象与接口

固定 uC/OS-II V2.93.01，上游提交 `0c4a48e6fbc6e915714e816196619a5481accf0c`、配置和两类授权修复不变。旧171活动源不改，新增登记后172源＝69目标＋103框架／tactics。不改既有AST、C、port、framework、tactics、测试、门禁、覆盖证据或白名单。

稳定接口：[V293_tick_while_owned_execution](../certiucos/v293/proofs/V293TimeTickLoop.v)。
独立入口：[V293TimeTickLoopProbe.v](probes/V293TimeTickLoopProbe.v)。
[中文连续扫描表及五步讲解](../docs/开发中/时钟中断如何跳过零延时任务.md#已继续把三个分支接成有限任务链的整个-while)。
[前瞻协议、开发快照与实际日志](logs/stage31-time-tick-loop/)。

## 不是假设执行的有限链

任务列表只描述空间字段，不是语义执行的oracle。每个节点的Next字段指向下一项，尾项指向idle；普通节点优先级不等于12，idle字节确为12。入口拥有局部扫描指针、每个节点的八项字段、group与两行位图、idle优先级和任意分离R，另有地址／byte／delay界及真实环境绑定。不输入成功store、guard值、单轮执行或整段执行。

从实际局部指针与Prio加载计算guard。非空链实际走true，复用既有0／大于1／等于1的完整循环体证明，再经sskip回到while。每轮把已处理节点放入frame，以更新后的共享位图和同一M1为剩余链入口；归纳返回一个Mf，重新组合全部节点。空链从真实idle Prio12求值false并退出，不要求idle Dly或Next字段。

同一Mf连接实际loststep循环、最终局部指针为idle、更新后的全部所选任务字段（含Next／Prio）、两行位图及group、idle优先级和任意分离R。IE和原控制栈恢复。全链共享位图fold，不是每轮重置或把独立终态拼接。

## 独立混合入口

六个节点覆盖0、3和四个Dly=1状态：Stat为1、9、0、8。初始Pend均7，group／row0／row1均0；最终Dly为0／2／0／0／0／0，Stat为0／0／0／8／0／8，Pend为7／7／1／1／0／0，group／row0／row1为3／4／4。预期列表直接按字面写出，再在实际Mf读回，不只比较输出函数的计算值。额外99和消息指针保持；非零节点偏移、非空控制栈、任意初始IE。

初始idle的Dly／Next加载均为None，实际循环仍能退出；不把初始缺失推广为尚未证明的终态缺失。入口可满足仅为空间见证，不是初始化可达；也不声称每个数值合法但可能地址重叠的列表都能满足分离入口。

## 单因素反对性检查

协议在开发前登记：只把主定理最终扫描指针从idle改成原链头；只把普通节点有效性中的Prio≠12改成True。保持实际AST及全部Proof正文。第一项应在最终readback连接拒绝，第二项应在真实guard连接拒绝。早期拒绝不获得下游信用；排除依赖路径／namespace／不一致假设造成的伪拒绝。

审稿式逐项边界见 `adversarial-review.json`。数值界不等于prio与位图坐标的全局关系；字段所有权不含完整TCB、Prev、事件等待表或全局ready关系。

## 开发诊断与资源开销

原始失败及成功尝试均保留，不覆盖。probe-dev01缺少旧fixture产物，随后按原源重编两个旧fixture。probe-dev02达到前瞻16GiB RSS预算后定点SIGINT，退出-2，不伪报为Coq证明拒绝；快照、进程信息、预算和日志保存。

最初怀疑是相等性搜索，替换地址分离策略后继续观测。最小计时诊断表明入口的tactic及Qed能够完成，主要持续增长发生在下一定理：直接对整个合并函数内存的缺失字段load做vm_compute。改用已有OwnershipCellsOutside按字节地址清单证明缺失，再用通用首字节缺失引理推出loadbytes=None，不改入口／六任务／定理结论。额外opaque入口分离实验未保留为生产机制；诊断源码有快照，临时.v副本纳入清理。不能把最初相关现象当作根因已确认。

另一个独立开销出现在任务合法性证明：无差别repeat constructor会为byte范围生成大量Peano构造。保留原Forall与全部数值约束，只对列表骨架用Forall_cons，各节点闭合数值由discriminate／lia证明；隔离诊断由10秒超时变为0.062秒通过。probe-dev04至06的归约／rewrite错误也保留；最终改用明确的loadbytes层及f_equal连接decode，没有更改结论。

## 范围与下一步

这里只构造存在的一条无ISR插入的顺序循环执行，不是所有中断交错下的safety。完整函数的hook／时间递增／OSRunning／链头赋值、局部alloc／free／return、ISR包装、初始化可达性及完整共享Inv仍开放。C到AST沿用已有手工映射，不声称已验证C前端。

下一步先连接函数前缀与while，再连接函数及共享Inv。最终仍需源码级GOOD_OS与同程序K1–K4全部闭合，之后才按教师要求开展uCOS3。长期目标未完成。

## 正式结果与清理后复核

| 检查 | 实际结果 | 不可外推的范围 |
|---|---|---|
| 正式 gate01 | 7条实际命令均符合预期：0／0／0／0／1／1／0 | 不是全仓 source-only 构建 |
| 独立 coqchk | 生产 while 与独立 probe 两模块通过 | 复用855个既有生产依赖产物 |
| 根定理假设 | 生产4根、probe3根，仅既有 classic 与 functional_extensionality_dep | 无新增公理，不是无经典公理证明 |
| 错误最终指针 | exit1，在 FinalPointer 的最终读回连接拒绝 | 不能替代全部算法负控 |
| 中和非 idle 约束 | exit1，在真实 guard 连接的 Nonidle 处拒绝 | 早期拒绝不给下游信用 |
| 新增测试 | 9／9通过 | 新测试没有覆盖整核正确性 |
| 清理后全量 | 1034项，362失败、1错误 | 整体仍失败，不标绿 |
| 范围／固定 C 核对 | 两项 exit0 | 不提升功能证明覆盖 |
| 默认 make audit | exit2，保留 stale function evidence input identity | 未重写旧冻结证据 |
| 正式六门 | 94／1／1／1／1／0，未改变 | while 进展未冒充完整函数或 GOOD_OS |

清理后全部363项诊断，按kind／id及重数，与本轮新增测试前的1025项旧测试结果完全相同。相对stage30的361项诊断，仅多出stage30的冻结输入身份和精确项目append两项；此前诊断全部保留。没有修改旧测试、门禁、证据或白名单，没有将全部失败归因于同一种原因。

清理前已逐项记录类型、大小、SHA256、链接目标及目录成员，并在首次unlink之前全体重新核验。实际删除367项：342个软链接、25个实文件／1405645字节，以及38个空目录；基线文件删除0。删除对象仅是两项负控隔离树、三个probe的临时编译产物和两份已保留同字节快照的诊断.v副本。

保留全部真实源码、所有成功／失败／中断日志及快照、855个旧生产依赖和5个新生产可复用产物。原有.lia.cache由实际编译更新后保留，前后hash在最终报告记录，未把旧cache当作一次性垃圾删除或恢复。README与VERIFICATION_STATUS仅前置新检查点，教程仅追加本节，历史正文通过字节hash核对；旧171活动源及旧生产依赖也逐一核对。HEAD不变，未提交或推送。

机器可读最终核对与逐项证据见 [final-report.json](logs/stage31-time-tick-loop/final-report.json)、[final-evidence-manifest.json](logs/stage31-time-tick-loop/final-evidence-manifest.json)。这些结果支持的只是本节有界执行接口；完整函数、所有ISR交错、初始化、共享Inv、GOOD_OS、同程序K1–K4和uCOS3均未据此标记完成。
