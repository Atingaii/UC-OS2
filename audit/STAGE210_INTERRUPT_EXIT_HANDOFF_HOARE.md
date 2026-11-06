# 第210步：不同任务退出尾段的所有权 Hoare

## 本步解决的问题

第209步只连接了不调度与同优先级的真实退出 builders。不同任务分支还需要执行计数器递增、更新当前优先级缓存和切换。不能把前面的分支证明当成这条路径已经成立，也不能把切换前的共享值作为原线程恢复后的快照保留。

本步稳定接口是 `V293_OSIntExit_changed_tail`，证明第200步已接受归一化 AST 中的实际正分支尾段：

```text
counter = counter + 1;
skip;
current = high;
switch(target);
```

`skip` 对应固定配置关闭的 profiling 语句，沿用已有 AST。没有改 C、配置、AST、框架、切换语义或旧证明。仍使用 ADR0010 的源码级调用点抽象，并非汇编端口精化。

## 入口、实现与返回资源

生产文件：`certiucos/v293/proofs/V293OSIntExitHandoffHoare.v`。

| 位置 | 实际证明内容 | 尚未证明的内容 |
| --- | --- | --- |
| `V293_handoff_byte_read` | 从全局环境、不遮蔽及实际拥有的字节推导表达式求值 | 不以外部求值结果作前提 |
| `V293_handoff_byte_copy` | 直接使用 `assign_rule` 更新完整写权限的 current 字节 | 不是指针或任务表的额外正确性定理 |
| `V293_exit_handoff_increment` | 复用已证实际计数器加一，保留字节和共享表 | 不声称计数永不溢出；采用 UINT32 模加 |
| `V293_exit_handoff_close` | 将 high/current/counter 全写单元和共享抽象表封入同一 storage Inv | 不建立生产 TCB、就绪位图与缓存的全局关系 |
| `V293_OSIntExit_owned_handoff` | 赋值后直接应用真实 `switch_rule` | 不假设一整个 handoff Hoare 当前提 |
| `V293_OSIntExit_changed_tail` | 顺序连接 increment、skip、copy、switch | 不包含不同优先级 guard，也不包含退出前缀或 builders |

入口显式拥有共享抽象任务/事件表、时间、当前任务、目标指针、三类实际可写单元及调用方提供的 `px`。最高就绪和当前任务成员条件用于导出 `SWPRE_NDEAD`；`px` 需满足 `GoodFrm` 和指定 `LINV` 义务。本步不从生产不变式自动取得这些资源，也不把 `GoodFrm` 本身当作资源“确属线程私有”的全局证明。

已知三个可变全局单元不放进 switch 的 frame。frame 仅包含环境绑定及接口参数 `px`；共享值通过 `V293_storage_cell` 的 `EX v` 存回 Inv。返回接口 `V293_exit_handoff_resumed` 不带入口 high/current/counter、任务表、事件表或时间的值参数。

**切换规则后置的含义是原线程将来恢复执行，不是刚切入目标线程的即时状态，也不是切换必然返回的终止性定理。** 其他线程可能已经修改共享数据，因此后置不能沿用入口快照。

## 独立非空见证与观察

探针：`audit/probes/V293OSIntExitHandoffHoareProbe.v`。

`FHbyte_owned`、`FHextra_witness` 和 `FHspatial` 从编码后的实际字节、独立抽象表和不相交内存构造资源。`FHentry_nonempty` 并非从待证 Hoare 的结论倒推存在性。`FHdifferent_max_nonempty` 明确实例化：

- 当前任务与目标任务不同，当前任务在任务表内；
- 当前任务优先级 4、处于等待态；目标任务优先级 12、处于就绪态且是最高就绪者；数值较小的等待任务不参与最高就绪选择；
- high 字节为 12，current 字节为 4；计数器为 `Int.max_unsigned`；
- 实际指针、完整写字节、共享表、清除的 ISR、IE=false 和空两栈共同存在；`px=Aemp`。

`FHactual_changed_tail` 在同一资源布局实例化生产主定理，对任意计数器值成立。`FHcounter_wrap` 单独检查最大值加一为零。`FHcopy_observable` 从实际资源导出 current 的可观察求值；在 copy 后资源 `tail nh nh c` 上实例化，观察值就是 nh，而不是恢复后永不改变的值。

这些是局部资源非空和 Hoare 适用性，不是初始化可达性或新的一份完整执行轨迹。

## 事前消融与证据边界

协议及身份在实现前写入 `audit/logs/stage210-interrupt-exit-handoff-hoare/protocol*.json`。

本步复用第200步已冻结的 `BXcopy_ablation`：输入相同、其他机制不变，仅删除缓存 copy；两侧都完成实际 switch，但删除侧的缓存与切入任务不一致。探针重新检查该定理类型，递归检查包含其模块。它检验 copy 的必要性，不是因为 guard 提前拒绝而宣称下游机制都有效。

**BX 与 FH 是不同见证。** BX 观察切入新任务的即时状态；FH 证明本步资源契约及原线程恢复语义。本步没有把 BX 的执行当作 FH 的执行，也没有声称新完成了双变体完整退出执行或完整恢复轨迹。

## 验证与剩余目标

- 每次编译均保留 `.v.snapshot.txt`、输入 SHA、日志和结果；失败不删除。稳定版本见 `stable-compiles.json`。
- 新增结构回归只约束证据和接口形状，不替代 Coq 证明，也不声称语义 TDD。
- 逐根假设、递归 `coqchk`、两次构建、全量测试和精确配置后源码重建以本目录 `verification.json` 为准；不把尚未执行的检查写成通过。
- 全量回归必须保留此前 423 个失败和 1 个错误的原 ID 与顺序。审计的旧源码证据身份错误和旧空白错误不通过删结果消除。
- 只清理本轮一次性信任驱动及其产物、已恢复原字节的缓存备份；源文件、失败证据和可复用 Coq 产物保留。

本接口目前要求 storage shared flags 所规定的清 ISR、IE=false 等条件。第206–209步参数化的 ISR 上下文与该 storage Inv 的统一尚未完成，不能直接拼接宣称整个函数成立。完整不同任务退出前缀、真实 builders、增强统一 Spec、生产 Inv/ISR/LocalInv/WFInt、初始化、GOOD_OS 与同程序 K1–K4 仍开放；uCOS3 尚未启动。

六阶段覆盖不变：`94 / 1 / 1 / 1 / 1 / 0`。这是向不同任务分支纵向连接迈进的一段局部证明，不是新增整函数覆盖、整核完成或阶段一结束。
