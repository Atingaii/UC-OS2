# 第142步：调度器真实调用、CPU_SR 分配与返回释放

## 目标与实际增量

仍按老师要求先做 uC/OS-II V2.93.01，之后才做 uCOS3。第141步从 cpu_sr 初始化后的函数中途开始；本步连接既有完整函数 AST 的真实入口与出口，不修改 C、配置、AST、framework 或 tactics，不增加六门整函数信用。

生产模块 `V293ReadyFullCall.v` 提供7个根：真实 `sfexec` 入口、一个 Tint32 局部变量的分配与原赋零语句、初始化后的空间所有权、原释放后的精确重建、四字节释放与其他 block 保留、原 sret／sfree／sfreeend 返回、既有 loststep 闭包的 continuation locality。没有增加执行规则或把成功分配／写入当 oracle。

联合探针 `V293ReadyFullCallProbe.v` 复用上一轮同一非空 ready＋waiting、实际 TCB／位图／优先级表／只读 lookup。编号113仍绑定既有完整 OS_Sched 函数，调用者环境为 `RTle`，不是 cpu_sr 的 callee 环境。

- `FCcaller` 从实际 fixture 所有权执行原 free，证明释放后整个98号 block 都 fresh；再由原 allocb／store 精确重建相同内存。不是预置局部变量冒充调用，也不是初始化可达性证明。
- `FCenter` 从 `scall` 开始，经真实 `sfexec`、单个局部分配、原初始化赋值，连续到原临界区控制。原始全局 OS 分类以 sfexec 为入口，前面的 scall 是局部调用语法步骤；本步不声称已经分类完整全局调用。
- `FCblocked_return` 对任意合法 guard 字节、任一 guard 非零的组合，从实际调用到返回，调用者环境、内存、IE 和 critical stack 全部恢复。结论明确连接同一 fixture 的 free 结果，避免任意空内存见证。
- `FCno_switch_return` 在 guard 都为零、current=Ready4／cache=4 时，执行原选择调用／返回／目标赋值／分支与临界区出口，最后释放 cpu_sr 四字节并恢复调用者环境。返回后 target=Ready4，counter=UINT32_MAX，cache=4。释放只改局部 block，其他 block 与释放前相同。
- `FCready_to_switch` 从同样真实调用入口接到 Waiting6／cache=6 分支的确切 switch，counter 回绕为零，旧任务仍保有 cpu_sr 和待执行 excrit／sret／真实调用 continuation。
- `FCswitch_after_call` 将上述局部前缀与原 lpstep 的实际 switch 用同一个 Mtail 接合，current 实际改为 Ready4；旧任务保留局部对象和保存栈，新任务辅助状态不变。这是局部前缀＋单次全局切换的混合接口，不是完整全局闭包，不声称旧任务已恢复、退出或返回。

## 单因素消融与反向审查

`FCfree_ablation` 从真实完整调用连续运行到唯一局部对象的动态释放点。正例执行原 sfree，四字节全部变为 None；负例只把此处单元素 free list 替换为空表，在相同内存、环境、aux、调用 continuation 上执行原 sfreeend。负例仍返回并恢复调用者环境，但 Tint32 局部对象仍能完整读取零值。两者在98号 block 之外逐字节相同。

这是仅跳过一次行政性局部释放的语义故障注入，不是声称 C 源码中有一条 free(cpu_sr) 可删除；不把负例更改后的动态代码当成原程序执行。两条后缀都真正运行到返回，未用共同提前拒绝证明下游成功。

分配地址98由有限实例构造，通用入口定理接受 fresh 地址。本步证明存在性、无交错轨迹，不覆盖所有分配选择、所有交错或初始化可达性。ISR 映射／interrupt stack 仍为空，guard 的非零字节未与真实活动 ISR 建立可达关系。

实际 switch 不写 OSPrioCur，旧 cache=6 与 current=Ready4 的同步缺口保留。生产全局语义 Inv、CurLINV、旧任务恢复、端口同步、API／ISR 保持、Hook／栈、WFIFun、GOOD_OS 和同程序 K1–K4 仍未完成。uCOS3 未开始，总目标 active；六门仍为 `94/1/1/1/1/0`。

## 验证与证据

证据目录：`audit/logs/stage142-ready-full-call/`。实际通过范围以 `checkpoint-report.json`、`verification.json` 及逐文件清单为准；计划或文本结构检查不能替代 Coq 语义验证。

本步18个根的 Print Assumptions 已通过；coqchk 独立重查309个活动模块及28个额外探针，退出0。实际假设集合仍仅 classical 与 functional extensionality，与第141步相同。全量两次运行应各为1828项，失败／错误逐ID核对结果以冻结报告为准。

保留所有失败编译快照和日志；稳定源码逐根 Print Assumptions，再用 coqchk 独立检查。假设集合不得超出既有集合。新增7项结构／身份回归；全量测试的失败 ID 集合与错误 ID 必须逐项等于第141步，旧423失败／1错误仍保留。make audit 的 stale function evidence input identity 与原 inferules.v 空白失败不隐藏；共同身份提前拒绝不计为下游通过。

旧冻结证据和既有源码逐文件比较；没有修改六门、固定 C 或配置。只清理本步一次性 Trust 产品和缓存备份，先核对全部目标，恢复旧 lia／nia 缓存；保留源文件、可复用证明产品及失败证据。未提交／推送。

下一步把真实 sfexec 入口至返回的局部轨迹接成原全局语义闭包，随后处理切换后旧任务恢复与 OSPrioCur 同步边界；不能凭本步有限成功增加整函数信用。
