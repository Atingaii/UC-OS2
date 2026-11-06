# 第155步：真实未初始化局部入口与返回后的联合资源

## 要解决的缺口

第154步的 post-hook 接口拥有一个合法 `Vptr`，不能直接应用到真实分配后的 `Vundef`。第34步虽已有局部分配与返回执行，但返回端只提供按 block 的字节保持，未把共享任务、ready、实际优先级表及抽象时钟的空间资源一起交还调用者。本步连接这两个缺口；旧证明与证据保持原样。

## 实现

生产文件：`certiucos/v293/proofs/V293TimeTickRawReadyReturn.v`。

- `V293_tick_raw_ready_payload`：复用第33步真实 raw-slot 执行；不把 `Vundef` 当成满足类型匹配的合法指针。由原来的 head 赋值生成合法指针后，复用原完整 while、任务记录重组、ready 关系及原 clock／taskchain 抽象步骤。
- `V293_tick_release_slot`：从真实 `Amapsto ** R` 的空间分割，经框架既有 `free_locality2'` 构造成功 `free`，精确得到同一个剩余内存中的 `R`。不是先假设 free 成功，也不从可读性反推所有权。
- 两局部释放辅助证明按真实 `getaddr` 顺序执行 `sret_step`、两次 `sfree_step` 及 `sfreeend_step`；同时支持变量标识决定的两种顺序，检查每个局部4字节全部消失。
- 稳定上层接口 `V293_tick_raw_ready_return`：从真实 post-hook 返回检查点，连续执行原尾段与返回释放，恢复 caller；同一实际返回内存拥有 ready／任务记录、时钟／running／head、共享抽象字段及具体 frame cells。
- 任意 `R` 仅在不变的 callee 环境内保持。跨环境只移动已有 context 引理验证的具体资源，不声称所有断言均与环境无关。

唯一新增资源打包 `V293_tick_return_payload` 只是既有断言的空间组合，不增加执行关系、抽象槽或新公理。

## 前瞻验证与对照

协议先于实现写入 `audit/logs/stage155-tick-raw-ready-return/protocol.json`。

探针：`audit/probes/V293TimeTickRawReadyReturnProbe.v`。非空实例含同一 block 中互不重叠的两个等待任务、一个 ready 任务和 idle，实际13项优先级指针表与 canary99。基底不含两个局部对象，真实两次 `allocb` 加保存寄存器初始化产生 `Vundef`／0入口。caller 非空且不同于 callee。

1. 正例检查真实分配入口、原时钟37→38、到期与递减、返回资源与 caller 恢复、两个局部各4字节全 `None`。
2. 单因素关系对照：同一正确返回内存、相同任务／ready／字节，只省略抽象时钟更新。除时钟外抽象槽相同，物理38拒绝旧抽象37。
3. 释放对照：同一正确返回内存不能再解释被释放的局部指针所有权；不是执行漏 free 的 C mutant，不通过删堆制造失败。

实际运行结果、失败编译快照与最终独立检查见本步 `checkpoint-report.json`／`verification.json`；结果未生成前不以本说明代替验收。

## 实测结果

- 稳定编译：生产`raw07`与探针`probe07`退出0；保留全部14次编译的源快照、日志和真实退出码，其中10次失败不删除、不伪装成通过。
- `make build`及清理后重建均退出0。15个新根的`Print Assumptions`只使用既有允许集合中的classic／functional extensionality，未扩张假设集合；独立`coqchk`检查323个活动模块＋44个探针模块通过（785.40秒）。
- 新增7项结构／证据回归全部通过；清理前后全套均为1916项、423失败／1错误，与第154步的失败及错误ID集合完全相同。Python测试不代替Coq语义证明。
- `make audit`仍退出2，原因仍是`stale function evidence input identity`；`git diff --check`仍退出2，保留旧`inferules.v:581–586`空白问题。本步没有重写旧证据或放宽门槛。
- 核对27787份旧文件；仅README／状态说明前缀、`_CoqProject`新增一行和生成的`.Makefile.coq.d`出现预期差异。全部旧C／Coq源码、framework／tactics、测试和审计证据字节保持。
- 删除前完整确认清单，然后清理10个一次性文件及1个空目录，共692187字节；两份既有缓存按原哈希恢复。源文件、失败快照、结果日志和可复用Coq产品保留。
- 最终检查报告、证据哈希清单及冻结后复核入口均在`audit/logs/stage155-tick-raw-ready-return/`。这仅是本步局部检查点通过，不是整仓库测试全部通过或最终GOOD_OS完成。

## 本轮修正的证明错误

返回读数处的 `rewrite` 曾报“找不到子项”。缩成通用内存的最小例子后，`Set Printing All` 显示：表面相同的 `get` 带有不同的隐式类型索引（`addr` 与定义上相等的 `positive * Z`），导致改写匹配失败。明确地址的 `addr` 类型后可正常改写；时钟／指针表则直接用 `eq_trans` 连接保持等式与原读数。结论和内核语义均未改变。失败快照和简要诊断留在本步日志目录，不删除失败来制造全绿。

## 明确边界

非空caller探针只检查局部环境确实恢复：其9999标识对应的block999未建立生产caller不变量；canary90是另外实际拥有的空间frame。因此不主张该caller是生产初始化可达且全部局部有效的调用者。

固定 `OS_TIME_TICK_HOOK_EN=1u`。分配前缀停在真实 CPU hook 调用，尾段从 hook 返回检查点开始。两条轨迹共享同一个局部入口，但**没有**把开放 hook 偷换成 skip、没有安装虚构 hook 体，也没有把两检查点拼成连续整函数调用。

本步仍是未挂起有限链、无交错端点，不是完整 tick Hoare／API／ISR或逐物理步精化。挂起／flags、event／pend关系、生产 Inv、初始化 side condition、完整 WFIFun、源码级 GOOD_OS及同程序K1–K4仍开放。原pend7只是合法输入边界，不是已证启动可达性。

特别是，`V293_ready_payload` 的 task record 只是已选字段，不是完整TCB：原tick链的 `next`（偏移20）以及 ready任务的delay／pend等额外字段未作为命名所有权从本步稳定接口交出，而被外层 `Atrue` 吸收。因此本步不能直接推出下一次tick所需原链资源；非局部字节保持也不能补造可写所有权。下一步须先修复这处资源接口缺口，再讨论可重复调用与Inv重封闭。

六门维持 `94/1/1/1/1/0`，旧423失败／1错误及审计身份失败不改写。第一阶段完成后才开展 uCOS3；总目标 active，不提交、不推送。
