# 第334步：链表资源穿过实际调度与切换，并执行while一步

## 本步解决的问题

第333步的增强入口已有head/Next资源，但原全局轨迹止于调度调用前。本步不重新制造末端堆：沿同一 `LHinitial` 的真实客户端延时调用，执行原调度器的局部分配、helper调用/返回、计数器更新和任务切换，保留入口两槽及完整ready_full；随后在该实际切换堆上另证scanner分配、源码head赋值、真实while guard与一次未到期iteration，回到残余while。

固定目标仍为uC/OS-II V2.93.01及两类授权修复。没有修改C、配置、旧生产证明、旧测试或冻结证据；新增生产仅追加注册，中文总说明只加顶部记录。手工源码模型与既有临界区归一化不是经验证C前端。

## 资源和执行的连接

| 边界 | 证据 | 严格范围 |
| --- | --- | --- |
| 原客户端入口→延时阻塞 | 复用 `LHglobal_ready` | head/Next从入口即拥有，不是切换后补造 |
| 阻塞→调度调用完成 | `LGglobal_sched` | 同一全局程序、同一原始入口，helper槽在返回边界释放 |
| 调度→任务切换 | `LGglobal_switch` | 实际lpstep与current指针store，物理/抽象current均为新选中任务 |
| 切换堆→scanner准备 | `LGprepare` | 显式alloc与原head读取赋值；是另外的局部执行 |
| while→残余while | `V293_ready_countdown_while_step`、`LGiteration` | 实际guard读取、true分支、3→2、Next推进和excrit |
| 同输入消融 | `LGsame_input_ablation` | 正反使用同一个准备堆Mp；只将Next赋值替换成skip |

稳定接口不要求调用者提供成功load、store、eval或执行轨迹。guard从完整ready_full中的优先级字段和显式scanner槽读取导出；没有用预期结果作为循环oracle。当前任务和被扫描任务可不同：本例旧任务priority4等待，新选中任务priority6是current，tick后旧任务仍等待2。

**完整ready_full本身不拥有Next**或head；它对ready记录也不提供delay44所有权。因此这些链表槽仍为显式入口fixture，**不是OSInit/TaskCreate的初始化来源证明**。不能直接把下一ready节点的delay=0当作已有事实，更不能把本例两任务链表当成有idle终点的完整遍历。

## 事前单因素消融

协议 `audit/logs/stage334-switched-linked-tick-loop/protocol.json` 在实现前冻结。

| 项目 | 正例 | 消融 |
| --- | --- | --- |
| 原全局延时/调度/切换和head准备 | 同一输入、同一Mp | 完全相同 |
| while guard、true分支 | 实际读取执行 | 相同guard，实际执行 |
| 临界区、非零判断、倒计时、未到期分支 | 执行3→2并退出临界区 | 同样执行3→2并退出 |
| 抽象任务表和完整ready_full/frame | 实际闭合 | 同样闭合 |
| 唯一因素：Next赋值 | scanner改指另一任务 | 仅替换为skip，scanner留在旧任务 |
| 残余while处的预期pointer门 | 通过 | 晚拒绝 |

`LGmutant_late_gate` 构造实际突变循环片段，不是编译失败、入口缺资源或提前拒绝；倒计时、抽象更新、完整所有权、真实excrit和残余while均已成立，再由旧/新scanner读取矛盾拒绝正例终点。current在正反都保持新选中任务；缓存仍为4，不声称与新priority6同步。另证计数器c+1及canary99读取保持。

该消融只检验Next语句，不检验scheduler、switch、guard或全局ISR闭包，**不是K1–K4**。

## 复核方法

- 新生产 `certiucos/v293/proofs/V293SwitchedLinkedTickLoop.v`：2个证明根；实例 `audit/probes/V293SwitchedLinkedTickLoopProbe.v`：14个根。
- 两文件各两次稳定编译、完整增量构建；4个固定配置函数重新物化并重放源码身份。
- 16根Print Assumptions及递归coqchk，检查期间冻结全部Coq输入；只接受既有classic和functional_extensionality_dep。
- 新8项检查分别覆盖来源、非循环接口、实际while、原全局调度/切换、scanner来源、单因素消融、递归信任、历史/范围。Python文本检查不能替代Coq内核检查。
- 两轮新增测试和两轮全量测试分开记录；不改旧快照断言，不删除或豁免旧失败。新历史测试事前使用只追加的注册契约，不要求未来项目停止新增生产文件；本步verify仍精确核对唯一新增注册。
- 开发失败snapshot/log原样保留；最终数据以本步verification.json及原始日志为准。

## 本步实测结果

| 检查 | 结果 |
| --- | --- |
| 两文件各两次稳定编译、增量构建、4函数身份重放 | 通过 |
| 16根Print Assumptions与递归coqchk | 通过；递归约317秒；893份Coq输入期间保持 |
| 假设集合 | 仅既有classic、functional_extensionality_dep |
| 两轮新增检查 | 每轮8项通过 |
| 两轮全量 | 每轮2924项、444失败、1错误，身份与顺序完全一致 |
| 相对第333步 | 原443失败/1错误身份和顺序保持；新增1项失败，无新增错误 |
| 无新增失败门禁/整体local checkpoint | false；局部proof checkpoint为true |
| 总体make audit | 仍失败：旧function evidence input identity过期 |
| git diff --check | 仍失败：旧inferules六处空白，输出与第333步逐字节相同 |

新增失败为 `test_ready_tick_linked_entry.ReadyTickLinkedEntryTests.test_history_and_explicit_limitations`：该旧测试严格要求_CoqProject等于第333步冻结清单；本步合法追加新生产注册后不再相等。没有改写、删除或豁免该测试，也没有把预期的快照失败记为通过。全量门禁不通过与局部Coq证明通过分别记录。

核对46416份基线文件中全部非许可变更项未改变，保留上步manifest的114项非可变交付。先逐项记录并审查10个本步一次性Trust驱动/对象与缓存备份，再删除；4份既有缓存恢复原哈希，Makefile时间保持早于_CoqProject，下一次build会重新生成。306份既有pyc、可复用证明对象、开发失败snapshot/log和历史资料均保留，源码重放临时目录自动清除。未提交/推送。

## 不能外推的结论

本步**不是合法ISR入口**，**不是完整OSTimeTick调用**。原全局轨迹确实到达实际switch，但scanner分配、head赋值和while片段仍是从同一堆出发的另外局部执行；其控制流、局部环境和中断状态未连接为合法全局ISR轨迹，不能仅凭资源相同拼接。

只执行一次true guard并回到残余while，未完成后续节点、idle终止、时钟、hook或中断返回。没有到期唤醒、旧任务重调度、原嵌套延时返回或缓存同步结论。任意API/ISR闭包、统一WFInt、初始化、顶层ProgSim、GOOD_OS和同程序K1–K4仍开放；uCOS3按老师要求在阶段一完成后才开始，不需要硬件。总目标保持active。

下一步需补齐ready节点delay/链表资源的初始化与保持来源，再连接后续节点和idle终点；不能把完整ready_full没有拥有的字段用无来源fixture补到冻结末端堆。
