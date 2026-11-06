# 第290步：OSIntExit 嵌套未退尽分支的完整客户端调用

## 接上了什么

唯一生产接口 `V293_exit_nested_client_call_TaskSim` 从高低两层相同的 `scall f nil` 出发。低层使用原边界归一化 AST，依次完成客户端入口、函数入口、任意 fresh saved 分配、写零、running 判断、真实 encrit、nesting 递减、外层 guard、excrit、释放局部变量和恢复调用者；高层通过显式 API 绑定执行 `END None`，不执行 sched。最终后置是原来的 `RDYINV G t ** LINV ...`，不是 Post=True。

公开接口只要求函数/API 绑定、资源、分支条件及合法 client 尾部，不把执行轨迹、求值/写入/释放结果或下游 TaskSim 作为前提。内部切点引理允许 continuation，用完整入口定理将它们消去。没有修改框架的 InOS 分类。

| 条件/动作 | 本步处理 |
| --- | --- |
| running=1、2<=n<256 | 原饱和递减写入 pred n |
| pred n>0 | 外层 nesting==0 为假，跳过整个 dispatch |
| lock/helper | 保留 lock=0 的所有权，但不要求其全局查询或 helper 函数绑定；这条分支不读 lock、不调用 helper |
| ready/current/target/counter/decoder | 复用同一 active resource；未修改的资源重新合入同一 storage invariant |
| 高层 API | 分支专用 END None；不是把上一轮的 sched 规格硬套到不调度分支 |

`V293_nested_reclose` 将 decoder 的两份读权限合并为完整 storage；target 单元保留真实类型证明。重闭合使用当前具体全局环境，没有假设所有分离子状态自动共享一个尚未证明的环境查询性质。

## 非空实例与单因素对照

`NCnonempty_client_call` 直接复用既有 `ACmemory n` 和 `ACbase`，覆盖全部 n=2..255，不更换任务记录、ready 表、decoder 或 guard 堆；saved 仍由实际函数入口分配。实例固定 `NCspec`，后置使用 `ACinv`。抽象任务仍为原来的 Waiting 任务，这条不调度分支无需证明它已成为最高优先级 Ready 任务。

协议先于实现固定。`NCdecrement_control` 在同一个非空输入堆上只对照 nesting 的递减写入和省略写入：

- 原字节为 n，实际 store 写入 pred n，更新后 load 确认该值；有界字节注入性证明两者不同。
- 除 (150,0) 这个地址以外，每个位置完全相同，包括同块的其他偏移。
- 原路径递减后的 guard 与省略递减的 guard 都为假。因此，不能用“最终未调度”判断递减没有发生。
- n=2 的 2→1 与 n=255 的 255→254 分别有边界推论。

这是局部存储/guard 对照，**不是完整调用执行消融**，也不证明所有后续机制的必要性；省略路径不冒充已经建立完整 TaskSim。

## 验证与范围

生产文件加入 `_CoqProject`，探针不加入生产清单。串行重复编译、逐根假设、递归 coqchk、构建、审计、全量回归与失败源码快照保存在 `audit/logs/stage290-exit-nested-call/`；最终实测以 `verification.json` 和只读 `checkpoint.py` 为准，文本结构测试不代替 Coq kernel。

C、配置、AST、框架及 ADR-0010 不变；之前的冻结文件和未通过门槛不改写。source-identity.json 沿用旧来源哈希，历史 function/scope 描述不用于认定本步分支覆盖；本步范围以协议、定理签名和本说明为准。

本步仅 running=1、2<=n<256、原 lock=0 资源族、IE=false、si=nil、ISR 全清、空 LINV。只是不调度分支的分支专用规格，不是统一 OSIntExit 规格。running=0、锁阻塞、等优先级分支与强 current guard 缺口仍需处理。不是 WFIFun/WFInt，不是 GOOD_OS，同程序 K1–K4 未闭合，uCOS3 未开始。旧失败保留，目标 active，未提交/推送。

### 本步实测与缓存干扰

| 检查 | 实测 |
| --- | --- |
| 生产与探针 | 各两次串行编译通过，源码哈希稳定 |
| 逐根假设、递归 coqchk | 14 个根通过；仅既有经典逻辑与函数外延性；递归检查约 552 秒 |
| 构建、项目审计 | 通过；364 个活动 V293 文件、103 个框架/策略文件，不等于函数覆盖数 |
| 新增 Python 检查 | 5 项通过；清理后复验亦通过 |
| 首次全量回归 | 2616 项，443 个失败、1 个错误；原始记录保存在 full-tests.json/log |
| 缓存恢复后全量回归 | 2616 项，434 个失败、1 个错误；旧失败/错误标识及顺序完全一致；见 full-tests-after-cleanup.json |
| 覆盖审计、空白检查 | 仍未通过；分别为既有函数证据身份过期、既有 framework 空白问题 |

首次全量比上轮多出的 9 个失败都明确指向 `.lia.cache` 的哈希变化，而不是新的功能反例。Coq 编译更新了该既有缓存；按预定清理要求恢复开工前原字节后复跑，旧测试和断言不做任何修改。首次失败、每项完整诊断、清理前后哈希均保留，不能删除首次结果冒充一次性全通过。

清理逐项核对并删除本步 6 个一次性 Trust 文件和 2 份已恢复缓存备份；保留编译失败记录、源码快照、可复用依赖、交付和核查材料。既有 306 个 Python 字节码文件不变，没有新增字节码。
