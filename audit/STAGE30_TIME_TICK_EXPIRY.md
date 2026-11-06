# 第30步：OSTimeTick 到期路径的实际执行与同次资源归还

## 本步结果

固定 uC/OS-II V2.93.01、上游提交 `0c4a48e6fbc6e915714e816196619a5481accf0c` 和既有两类授权修复不变。新增稳定接口 `V293_tick_expiry_iteration_owned_execution`，连接原可执行循环体的 Dly=1 路径。不是完整函数、初始化或整核证明。

- 生产源：[V293TimeTickExpiry.v](../certiucos/v293/proofs/V293TimeTickExpiry.v)。旧170活动源逐字保持，新增登记后171源＝68目标＋103框架／tactics。
- 具体入口与实际执行：[V293TimeTickExpiryProbe.v](probes/V293TimeTickExpiryProbe.v)。
- 前瞻协议、失败／成功源快照、命令、负控及独立内核检查：[本轮证据目录](logs/stage30-time-tick-expiry/)。
- 用户教程：[已填表格与逐步讲解](../docs/开发中/时钟中断如何跳过零延时任务.md#已继续dly1到期后是否进入就绪位图)。

## 真实语句与证明边界

入口持有本地ptcb、Dly、Next、Stat、独立StatPend、Y、BitY、BitX、group和目标row的实际空间所有权，加任意不相交R；给出真实环境绑定、合法地址和byte／索引界。不把成功store、复合表达式值或执行结论作为前提。

由完整写权限构造Dly递减到0的M1；从M1重读Dly。按事件等待mask55处理Stat与StatPend；从写后的内存重读Stat检查suspend8。没有挂起时先写group，在新内存重读Y／BitX／row后写row；挂起时保持位图。随后从更新后的内存读Next，写局部ptcb并退出临界区。同一Mf连接实际loststep执行、六项读回、十项资源及R整体归还，恢复原IE和控制栈。

清除等待位保留suspend位及64／128高位。空间所有权不等于完整TCB、事件等待表、优先级与位图关系或共享Inv；Y／X范围合法不等于已经建立这些全局关系。这里只证明顺序执行的临界区内循环体，不证明ISR交错、外层guard／while／idle终止、时间递增、hook、函数局部alloc／free／return或初始化。

语句模型沿用已有手工C映射，不声称已验证C前端。最初把源码物化helper的输出放进仓库子目录，触发 `git apply --numstat` 的路径上下文问题，报 `patch changes files outside its authorized source: mutex`。失败原因保存在 `source-inspection.json`，并非C漂移；没有改helper、补丁或C。之后直接读取真实上游 `os_core.c`，其SHA与冻结repaired core恰好相同，因为授权两修复不改该文件；准确行号摘录和函数身份保留。临时物化副本经清单核验后清理。

## 入口非空与可观察分支

独立编码字节入口覆盖全部256个Stat字节及任意初始IE。当前节点偏移8、后继不同、控制栈非空；旧StatPend=7、group=1、目标row=128、Y=1／X=2。同一个实际Mf中检查：

| 入口Stat | 最终Stat | 最终StatPend | 最终group | 最终row |
|---|---|---|---|---|
| 0 | 0 | 0：OK | 3 | 132 |
| 1：等待SEM | 0 | 1：TIMEOUT | 3 | 132 |
| 8：挂起 | 8 | 0：OK | 1 | 128 |
| 9：等待SEM且挂起 | 8 | 1：TIMEOUT | 1 | 128 |

每行都有实际执行，不只是输出函数求值；另对2／4／16／32／64／128／255取得实际执行及Stat／Pend读回。未选中的另一行85、额外值99、事件指针和消息指针在Mf保持。入口空间可满足不是初始化可达；设置就绪位图不是立即运行，TIMEOUT也不是消息到达。

## 反对性检查

两项负控先登记，再各只修改最终一个load结论，入口、AST及完整主定理Proof后缀保持：错误声称Pend恒为0；错误声称不论挂起均设置row位。两者均在最终readback证明被Coq拒绝，排除了依赖缺失和namespace错误。`downstream_credit=false`，不把两项拒绝推广到全部下游机制。

开发中的类型导入、参数推断、notation冲突、算术归约与tactic问题及全部源快照保留；dev15生产编译成功、probe-dev02具体执行编译成功。没有通过新增公理或修改框架／tactics规避证明。审稿式逐项检查见 `adversarial-review.json`。

## 实际验证与保留的失败

正式gate01实际7命令达到预期：生产、两个旧fixture、新probe正向编译均0，两项负控均1，独立coqchk检查生产及probe两模块为0。生产三根与probe四根只含既有classic／functional_extensionality_dep，或全局闭合。179个门禁输入在结束时与最终检查时保持一致。复用既有依赖.vo，**不是当前身份的全仓source-only干净构建**。

新增9项测试通过。清理后全量1025测试仍360失败、1错误；361项诊断按kind／id重数与本轮旧1016测试完全一致。与上轮比较，旧359诊断全部保留，新增2项为stage29冻结项目输入身份／精确append断言；不把其余历史失败一概称为快照问题。不改旧测试、不重绑旧证据。

范围及冻结C只读检查通过，`git diff --check`通过；默认 `make audit` 仍exit2：`stale function evidence input identity`。未运行check-functions覆盖旧身份。正式六门记录保持94／1／1／1／1／0，不晋级。HEAD保持，未提交或推送。

## 清理与下一步

先逐项记录类别、大小、SHA／链接目标及目录成员，全体核验完成后才首次unlink。清理377项（340软链接、37实文件／1691399字节）及40目录，只包括两个负控隔离树、失败物化的临时源码副本、三个audit probe的15个编译产物。旧850生产／框架依赖逐字保持，新生产5个可复用产物、所有真正源码、成功失败日志和快照保留。既有 `.lia.cache` 被本次Coq编译更新，单独记录前后SHA并保留，没有删除或恢复；它不是冻结证据或生产源。

README／状态页仅前插检查点，教程仅追加，旧正文逐字保留；项目仅追加新模块登记。最终状态与哈希见 `final-report.json`。

下一步把零延时、未到期、到期三条循环体路径接到同一链表循环不变量，再连接完整函数与共享Inv。GOOD_OS、同程序K1–K4仍开放，uCOS3未启动；长期目标保持active。
