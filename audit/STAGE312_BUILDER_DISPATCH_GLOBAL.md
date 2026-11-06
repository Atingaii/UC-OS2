# 第312步：实际中断入口连接全局调度前缀

## 1. 与上一阶段相比改变了什么

第311步只连接有限**局部**handler前缀和末端全局切点。本步不更换程序、内存或过渡规则，把该前缀提升成原 `lpstep` 的有限全局轨迹，并在非空实例中连接：

原 `pint` → EOI → Enter完整调用 → normalized Exit／`OSSchedNew` → 优先级缓存拷贝 → 原物理切换。

相同切点还由原 `hpstep` 执行高层调度。前缀不等于完整高低层模拟：本步没有证明每一个前缀低层步骤都有匹配的高层步骤，更没有证明所有交错安全。

## 2. 稳定接口

生产文件：`certiucos/v293/proofs/V293InterruptBuilderDispatchGlobal.v`。

接口：`V293_builder_dispatch_global_prefix`。

- 输入未过滤的真实 `BuildintPre` 和同堆捕获的控制字节 `(1,0,0)`。
- 从第311步接口构造轨迹，不把局部／全局轨迹作为调用前提。
- 直接调用原入口规则 `V293_interrupt_source_enter`；中断程序表必须安装同一个wrapper。
- 通过既有 `V293_interrupt_local_steps_global`，将实际前缀嵌入原 `kint interrupted ike caller ks`。
- 输出全局切点保持同一 `Mf`、保存的CPU局部环境、ISR和辅助栈；保留未执行的 `excrit`／返回／`exint` continuation。

显式前提仍包括：全清原ISR、入口可接受／优先级条件、原 continuation 的 `goodks`、同程序函数绑定、handler-entry builder资源，以及输入缓存／256项lookup的一致性。它们没有被伪装成初始化后自动成立的结论。

## 3. 非空实例怎样检查上下文

实例：`audit/probes/V293InterruptBuilderDispatchGlobalProbe.v`。

`BGprepare` 从原 canonical heap 的实际所有权子堆构造输入。复用子堆读取证明推导缓存6与lookup表，不直接借用完整fixture读取。调用本步生产接口，非空抽象任务表确定下一任务为 `OwnershipReady`，优先级4。

| 项目 | 实际实例 |
| --- | --- |
| 原当前任务 | `OwnershipWaiting`，阻塞，优先级6 |
| 目标任务 | 另一个已就绪任务 `OwnershipReady`，优先级4 |
| 原执行表达式 | 常量37，非空表达式 continuation `CSke` |
| 原语句 continuation | `CSks`，不是空尾部 |
| 原caller | 非空，变量108映射至块999；故意与当前优先级名称相同 |
| handler运行环境 | 入口为 `emp`，Exit内部为真实CPU局部环境；不误用原caller的shadow绑定 |
| 全局程序 | 同一 `RDprogram` 与实际安装的 `BGip` |
| 末端切出任务代码 | `SKIP`，保存 `BDK ## kint BGinterrupted CSke BGcaller CSks` |
| 目标任务代码 | 原 `CSready` 保持 |

`BGcompleted_match` 由真实全局前缀得到 `Ms`，将**同一 `BGcutT`、`BGcutS bs Ms`** 交给第310步原切换匹配，再将入口、前缀、切换拼接成一条全局轨迹。末端物理指针与抽象当前任务都为Ready，缓存为4，三个控制字节为1、0、0；所有切点低层一步后继相同，无该切点abort。

这只是切点的一步确定性／无abort，不是整条轨迹所有状态的确定性或整个内核safety。

## 4. 先执行、后观察的单因素对照

方案预先写入本步 `ablation-protocol.json`。两份测试均先获得入口、全局前缀、低层切换、高层调度、拼接轨迹及物理读取见证。

唯一改动：最终期望保存的caller由真实非空 `BGcaller` 改为 `emp`。程序、执行、内存和证明脚本不变。基线通过，变体在最后使用 `Saved` 的地方被拒绝；错误上下文仍保留已完成的 Entry／Prefix／Low／High／Full／Physical／Observed。

这是精确终态观察的对照，不是删除某条程序语句的消融，也不证明所有上下文错误都可检出。

## 5. 对抗式复核

| 可能的假进展 | 本步证据或边界 |
| --- | --- |
| 仍只是拿局部trace换个名字 | 生产接口输出原 `lpstep` 闭包，实例从原 `pint` 拼接到切换后全局状态 |
| 中断上下文凭空给出 | 初始任务／环境／辅助映射为原任务上下文；原入口实际保存它 |
| 程序表在中间切换 | wrapper、Enter、Exit、scheduler与物理切换使用同一RDprogram／BGglobal |
| 用不相关内存连接末端 | 同一Ms传入原切换规则，Mf用于所有末端观察 |
| builder或lookup通过执行oracle代替 | 从实际未过滤资源和typed子堆读取构造，生产接口无轨迹输入 |
| 保存空caller也能蒙混通过 | 非空shadow caller和完成后的单因素观察对照 |
| 声称已经完成中断返回 | 旧任务只保存尚未执行的continuation；新任务运行、旧任务恢复均未证明 |
| 声称全交错模拟／GOOD_OS | 明确不成立；后续仍需统一控制接口、TaskSim和初始化等 |

## 6. 验证与下一步

| 检查 | 实测结果 |
| --- | --- |
| 生产接口与非空实例 | 各两次稳定编译通过，两次源码身份相同 |
| 递归信任复核 | 5个根全部通过；`coqchk` 退出0，耗时423.886秒；仅原有经典逻辑与函数外延性假设 |
| 构建／项目注册审计 | `make build JOBS=1` 通过；386个活动V293文件、103个框架／策略文件 |
| 新增回归 | 7项全部通过 |
| 完整回归 | 2752项，437失败、1错误；与第311步全部失败／错误ID及顺序相同，没有新增失败 |
| 完成后单因素观察 | 原caller观察通过，改为空caller的变体在最后使用 `Saved` 时失败；前置执行见证保留 |
| 旧覆盖审计 | 仍因 `stale function evidence input identity` 退出2；没有改写旧证据制造通过 |
| 旧空白检查 | 仍有 `inferules.v` 第581–586行六处；日志与第311步原字节相同 |

全部失败尝试、成功日志和源码快照保留在 `audit/logs/stage312-builder-dispatch-global/`。本步冻结前逐项核对后清理一次性验证副本、派生产物、缓存备份和两个任务专用生成器；原根缓存、306个既有pyc、历史证据与可复用证明产物保留。清理结果和交付身份分别见本目录 `cleanup.json`、`verification.json` 与 `checkpoint-evidence-manifest.json`。

下一步优先连接切换后被选任务继续执行与旧任务恢复时的 `excrit`／调用返回／`exint`，建立后继模拟，而不是重复新增有限执行包装。随后仍需统一控制状态的框架健全性、缓存／lookup关系初始化及保持、完整初始化和各功能族纵向连接。

最终目标不变：同一固定程序的 uCOS-II V2.93.01 `GOOD_OS` 与同程序K1–K4完成后，才按照教师附件进入uCOS3。当前没有提交或推送Git。
