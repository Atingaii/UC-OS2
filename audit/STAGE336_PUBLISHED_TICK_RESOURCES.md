# 第336步：从原初始化/发布链取得head、Next和零延时资源

## 本步补什么

第335步只从18字段初始化取得delay44=0，Next仍是外来资源。本步复用原连续初始化前缀→两次真实CPU hook调用→优先级表写入→链表发布→返回/释放局部变量的定理，在其同一返回堆上提取head/Next/零延时的联合所有权。**两个CPU hook契约仍开放**；不删除调用、不补造空hook，也不把条件定理当成无条件可达性。

固定对象仍是V2.93.01及两类授权修复；C、配置、旧证明、旧测试和冻结证据均不修改。活动源码为手工源码模型及既有临界区归一化，不是经验证C前端。

## 可供后续调用的接口

| 接口 | 结论 | 边界 |
| --- | --- | --- |
| `V293_published_tick_extract` | 原返回资源重排为head、新节点delay0/Next、全部canonical任务记录、其余10字段、其余发布链槽与原frame | 只移出已有资源，不推出新的执行 |
| `V293_TCBInit_returns_published_zero_under_hooks` | 原始未初始化TCB入口连续到返回0，实际head变为新节点、Next变为原非空head；返回上述资源，保留原资源视图和9个局部对象释放结论 | 非空链表；两个真实hook执行/保持契约仍为前提；起点在分配/CPU_SR赋值之后 |
| `V293_published_head_then_zero_iteration` | 实际源码head赋值与零延时iteration在一个sseq、同一续体中连续执行；scanner先变新head再变Next，原IE/临界栈恢复 | 显式scanner存储；不是函数/中断全局入口 |

`V293_published_link_spares` 对原返回链槽只移出Next/head，其余Prev、group、row、counter和原head的Prev继续拥有。原初始化remainder也只移出delay44，其余10项保留。新、旧canonical记录与这些资源以一个分离断言共同返回，不重复占有，不丢弃原frame。抽象任务图O保持原样，不能把拥有记录误写成完成抽象任务创建提交。

生产文件：`certiucos/v293/proofs/V293PublishedTickResources.v`。

## 有限实例与反例

实例文件：`audit/probes/V293PublishedTickResourcesProbe.v`。

- `PTcreation_under_hooks` 复用原 `ChainSpatialEntry`：新TCB为301:128、原head为301:8、原有priority12记录、18个未初始化字段、priority11参数和canary77；实例化新的连续创建接口。**没有闭合两个hook契约**，所以这部分仍是条件实例，不宣称实际hook实现存在或契约非空。
- `PTactual_head_then_tick` 从完整构造的有限内存出发，对任意P、续体及两种保存IE，无执行/load/store前提，构造真正的连续head赋值与零延时iteration；联合资源与所有非scanner字节保持。这个实例证明下游片段非空，**不是前一个条件创建实例的同一末端堆**。
- `PTliteral`/`PTvalid` 对任意延时构造全部字节、写权限和记录；不以编译失败充当反例。

事前冻结协议 `audit/logs/stage336-published-tick-resources/protocol.json` 只检验一个因素：是否可以在hook边界只保留canonical记录，而省去运行时零延时资源。沿用已检查的候选族，并在两个候选中加入完全相同的发布head槽；唯一变量仍是delay44四字节。

| 门/资源 | delay=0 | delay=3 |
| --- | --- | --- |
| 相同发布head、Next、scanner、canary、priority/status/message及canonical记录 | 完整拥有 | 完整拥有 |
| 运行时零延时资源门 | `PTzero_gate_passes` | `PThook_zero_resource_necessary` 由实际load矛盾拒绝 |
| 所有非delay字节 | `PTsingle_factor_outside` 对任意地址证明一致 | 同左 |

这是资源契约充分性的消融，**不是执行突变hook**，不证明delay3候选可由初始化/hook轨迹到达。真正的创建轨迹保留全部hook保持契约，不能由提前资源拒绝推断后续语句正确。

## 不能据此宣称的结果

- **不是无条件完整OS_TCBInit**：两个CPU hook契约仍开放，未连接调用分配/CPU_SR前缀及上层创建调用。
- **不是合法ISR**：创建返回与扫描实例不是同一全局轨迹；scanner显式准备，没有完整中断进入/退出证明。
- **不是完整OSTimeTick**：没有while guard/整链遍历/idle终止、到期唤醒、旧任务恢复或缓存同步结论。
- 仅非空链表；空表发布不自动满足含Vptr的零节点接口。
- 没有最终全局ProgSim、统一WFInt、GOOD_OS、同程序K1–K4；uCOS3仍未开始，**总目标保持active**。

## 反方审查

| 质疑 | 处理 |
| --- | --- |
| 是否从rdy推出物理delay0？ | 不做此推导；来自原初始化写入并经显式hook保持；非零候选给出反例 |
| head/Next是否仍是凭空假定的新值？ | 连续创建接口复用原实际发布执行；输入为原head/旧槽，输出才是新head/原head对应的Next |
| 是否只是把假设执行换一个名字？ | 只有已有两个真实CPU hook契约保留执行义务，其余存取/执行从入口资源导出；清楚标为条件接口 |
| 是否偷偷拼接不同续体或不同堆？ | 创建执行与扫描执行分开报告；只有扫描内部head赋值→iteration是一个连续sseq |
| 是否遗漏旧记录/链槽/局部变量释放？ | 返回原资源视图、九局部释放事实及新联合视图；spares精确移出3个所需槽 |
| 有限扫描实例能单独检出漏读head吗？ | 不能：该fixture初始scanner恰为head；这里只验证真实语法轨迹，通用接口允许任意原scanner。未把此fixture当作head读取的单因素对照 |
| 是否用下游有限实例证明hook契约成立？ | 没有；有限实例仅证明扫描资源与片段非空，不证明条件创建可达 |

## 验证记录

证据目录：`audit/logs/stage336-published-tick-resources/`。编译、递归信任检查、源码重放、构建、全量回归分别记录；新增7项Python检查只约束证据，不替代Coq内核。实测结果见下表，旧失败不改写、不豁免。开发期失败快照和日志全部保留，不提交/推送。

| 验证 | 实测结果 |
| --- | --- |
| 生产证明/探针各两次稳定编译 | 四次退出0；每次起止源码哈希相同 |
| 11个证明根及递归依赖 | `coqchk`退出0；897份Coq/工程输入在检查期间不变；仅框架既有经典逻辑和函数外延性假设 |
| 锁定源码重放、增量构建、project audit | 均退出0 |
| 新增7项证据检查，两轮 | 均通过；文本检查不替代Coq语义证明 |
| 全量回归，两轮 | 均2939项、444失败、1错误；与第335步失败/错误ID及顺序完全一致，无新增失败，但全量仍不通过 |
| `make audit` | 退出2，原函数证据输入身份过期仍保留 |
| `git diff --check` | 退出2，原六处框架空白问题；输出与第335步逐字节一致 |

清理前逐项审查并记录10个本步一次性文件，随后删除临时信任驱动/对象及4份已恢复的缓存备份。四份既有缓存逐字节恢复，Makefile时间戳恢复为下次构建会重新生成；306份既有pyc、全部旧证据、开发失败快照/日志和可复用证明对象保留。没有提交或推送。

下一步必须闭合真实CPU hook/程序环境边界，并在同一全局创建→合法ISR路径中保留这些资源；不能继续把局部片段数量当整核完成度。
