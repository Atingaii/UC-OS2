# 第330步：延时调用的真实嵌套返回后缀

## 本步补上什么

上一步的恢复后缀用的是简化 `kstop` 上下文，不能代表 `OSTimeDly` 调用 `OS_Sched` 后的两层返回。本步使用真实保存的 `DAcontinuation`，从完整就绪资源和两层局部变量所有权直接构造 `TaskSim`，不把后缀执行或仿真作为公开定理的前提。

公开接口：`certiucos/v293/proofs/V293TimeDlyNestedReturn.v` 中的 `V293_ready_nested_return_TaskSim`。它允许任意满足条件的外层局部变量列表与外部 `frame`，复用现有 `owned_record_cells`、完整 `ready_inv`、实际 `excrit`/`sret`/`sfree` 规则，不另造弱不变量。客户端限制为既有有限 skip 类上下文；要求明确的函数绑定、环境布局、零偏移所有权、空ISR、`GoodInvAsrt`。

实际后缀依次：

1. 从保存的调度器末端上下文退出临界区，按保存的IE拆分共享资源。
2. `OS_Sched` 返回，释放其CPU槽，恢复 `OSTimeDly` 的环境。
3. `OSTimeDly` 返回，按 `getaddr DCle` 的实际顺序释放 `y`、`ticks`、外层CPU槽。
4. 恢复客户端环境并进入原客户端尾部；保留原外部frame，给出 `RDYINV ** frame ** LINV`。IE=true 时共享core已交还共享INV，不能再说整个core仍被任务独占。

泛型生产定理不绑定实例中的11/12/13块；实例中的三个地址来自真实环境布局。内外局部变量有写权限，释放保持内存和抽象状态的精确分离，不是只把局部环境置空。

## 非空实例与严格边界

`audit/probes/V293TimeDlyNestedReturnProbe.v`：

- `DNcontext`：实际全局切换后的任务表保存的确实是该 `DAcontinuation` 和调度器局部环境。
- `DNresources`：从真实客户端调用前缀的同一个堆重新分组所有权；不是凭空假定存在资源。
- `DNnested_TaskSim`：在该堆上构造带实际嵌套上下文的资源条件仿真，支持两种保存IE和任意计数器值。
- `DNrelease`：单独给出实际低层局部执行闭包，恢复空客户端环境；最终四个局部对象的全部类型长度范围内字节均为 `None`。保留完整 `ready_full ** DNframe` 的资源结论用于这一局部执行，不与启用中断后TaskSim的任务/共享分割混淆。

`DNframe` 保留原前缀中的high=6、cache=4、counter=c+1、目标指针、guard、canary及只读查找表。**保留cache不是证明cache同步**。对读写值与边界已有前缀定理，本步不将它们升级为完整函数覆盖。

最关键的是：实例的起始堆来自真实前缀，但本步没有从切换后的全局状态构造“旧任务已被唤醒、重新当选并恢复到该上下文”的可达轨迹。当前抽象任务仍有延时；完整 `ready_full` 本身不代表当前任务已就绪。本步是实际上下文上的资源条件后缀，**不是旧任务恢复可达性**。不能把局部执行拼到另一任务的全局状态之后，也不能把两个单独成立的闭包直接当成同一整段执行。

因此本步**不是完整 API**、**不是全局 ProgSim**、**不是 GOOD_OS**，也没有完成任意API/ISR交错、统一WFInt、初始化或同程序K1–K4。阶段一完成后才开始老师要求的uCOS3，总目标保持active。

## 事前单因素消融

协议先于实现冻结：`audit/logs/stage330-time-delay-nested-return/protocol.json`，SHA-256：

`8b4b6fe4f51782b43140090f333dbd5d42db40c596bc766d4a62e212329c8555`。

只中和外层return/free片段，其他初始堆、保存IE、共享资源、frame与内层CPU释放保持不变。正例执行两层返回后所有外层局部字节不存在；负例停在同一内层释放后的 `Mi`，此时 `ticks` 仍可读取3，因而同一个“全部外层局部字节不存在”门为假。`DNouter_free_ablation` 在Coq中证明这两个判断，不依赖负例编译报错。

这是片段级资源/释放对照，**不是突变程序的全局恢复执行**，也不声称证明全块fresh（只证明已分配的类型长度字节范围）。

## 验证、历史失败与复现

原始日志、源码重放、稳定编译快照、逐根依赖和递归 `coqchk` 均在 `audit/logs/stage330-time-delay-nested-return/`。最终结果以其中 `verification.json` 为准；本文件不能代替原始证据。

```bash
make build JOBS=1 COQBIN=/data/home/lucentzhou/.opam/default/bin/
PYTHONDONTWRITEBYTECODE=1 python3 -B scripts/project-audit.py
PYTHONDONTWRITEBYTECODE=1 python3 -B -m unittest discover -s tests -p test_time_delay_nested_return.py -v
PYTHONDONTWRITEBYTECODE=1 python3 -B audit/logs/stage330-time-delay-nested-return/verify.py
```

14根递归检查包含8个生产引理/定理及6个实例引理/定理；仅允许既有经典逻辑与依赖函数外延性。不新增证明空洞，不改C、配置、既有测试、冻结证据或旧文件正文，不提交/推送。

全量回归、总体审计和空白检查分别记录，不用局部编译通过替代；若旧失败仍在，应保留其身份/顺序及原始输出，不将全量报告写成通过。下一步应从实际切换后状态连接合法tick唤醒、重新调度及恢复资源，再将本后缀接到同一全局轨迹；不能继续以独立后缀实例冒充这一义务。

## 本次实测结论

生产与探针各两轮稳定编译通过；全部14根递归 `coqchk` 通过，885项Coq输入在检查期间保持不变。构建、项目审计、两轮新增8项测试通过。

两轮全量均为2892项、440失败、1错误。第329步原439个失败与1个错误的身份和顺序保持，但新增1个失败：`test_ready_resume_partition.ReadyResumePartitionTests.test_history_and_bounded_completion`。它在旧测试第136行要求 `_CoqProject` 恰好等于第329步快照；本步追加生产证明注册后，该精确身份判断为假。只读内存字节对照确认唯一差异正是本步追加行，详见 `regression-delta.json`。这不是将该失败判成通过的理由：**无新增失败门禁未通过，局部证明检查通过不能替代这一门禁**。不修改旧测试、不删除有效注册、不过滤失败、不覆盖两轮原始日志。

总体 `make audit` 仍因既有函数证据输入身份过期退出2；`git diff --check` 仍报告原6处空白错误，与上一步输出逐字节相同。阶段一整核目标及uCOS3阶段均未完成，目标active，未提交/推送。

清理前逐一审查并移除了本步10项一次性信任驱动/对象和缓存备份，原4缓存字节恢复，306个既有pyc以及可复用证明对象、失败快照和全部验证日志保留。生成Makefile的mtime早于 `_CoqProject`，下次构建会重新生成。清理驱动标签与报告文件发生命名冲突，驱动记录已单独保存在 `cleanup-command.json`，报告原字节从保留的 `cleanup.log` 恢复，过程记于 `cleanup-report-recovery.json`；没有重复删除或丢弃运行结果。
