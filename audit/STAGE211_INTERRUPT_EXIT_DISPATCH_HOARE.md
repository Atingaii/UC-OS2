# 第211步：真实调度前缀接入不同优先级退出分支

## 解决什么问题

第210步只证明 counter 加一、配置后的 skip、缓存 copy 和 switch 尾段。第211步把已接受源码级 AST 中的真实 `OS_SchedNew` 调用、目标指针赋值和不同优先级 guard 接到这个尾段，不用几份互相独立的状态拼接出一个结论。

稳定接口：`certiucos/v293/proofs/V293OSIntExitDispatchHoare.v` 中的 `V293_OSIntExit_changed_dispatch`。结论只有一个 `InfRules`；前提不假设整个 dispatch、本体或后续求值正确。实际 callee 的函数契约仍是接口前提，不等于整程序函数环境已经闭合。

```text
OS_SchedNew();
target = priority_table[high];
if (high != current) {
    counter = counter + 1;
    skip;
    current = high;
    switch(target);
}
```

这仍是已打开资源边界上的局部 dispatch，不包含完整 `OSIntExit` 的 saved 初始化、running/nesting/lock 外层 guards、进入/退出临界区、return 或真实函数 builders。没有改 C、配置、AST、框架、旧证明或旧测试；沿用 ADR0010 的源码级切换抽象，不开展汇编端口或编译器精化。

## 同一状态上的资源连接

| 接口 | 本步实际连接 | 约束和边界 |
| --- | --- | --- |
| `V293_handoff_cast` / `V293_handoff_comparison` | 从实际全写字节和环境绑定导出真实 cast、比较值和类型 | 不接收外部表达式求值 oracle |
| `V293_exit_dispatch_open` | 从同一 callee 返回状态获得最高就绪目标、选中的 high 字节和目标指针 | 使用位图与任务表、优先级指针表关系，不由单独模型猜测目标 |
| 输入数组回收 | 完整就绪输入与优先级指针表由借出的两半权限重组后归还同一个 storage Inv | 不把这些共享数组留在 switch frame |
| `V293_exit_dispatch_guard` | 从返回状态的 high/current 字节计算实际不同 guard | 需要 selected priority 与 current 字节不同 |
| `V293_OSIntExit_changed_dispatch` | 实际调用及赋值 → guard → 第210步真实 increment/skip/copy/switch | false 分支由相同资源的实际 guard 值排除，不假设整个分支正确 |

共享 high/current/counter 全写单元、就绪输入、优先级指针表和显式其余 storage 均纳入同一 Inv。切换 frame 仅有环境绑定与接口参数 `px`；`px` 仍需满足 `GoodFrm` 和 LocalInv 义务，不把 `GoodFrm` 本身当成“生产状态中一定私有”的证明。

后置 `V293_exit_dispatch_resumed` 不带 lo/hi/current/counter、任务表、事件表或时间快照参数。它描述**原线程将来恢复**时的不变式资源，而不是刚切入目标任务的即时状态，也不证明切换必然返回。数组长度、地址和类型是布局参数，不是共享内容快照。

通用前置没有建立 current 缓存等于当前任务优先级的生产关系。因此 selected priority 不等于 current 字节，单独并不能推出目标任务与当前任务不同；不把数值 guard 偷换成完整全局缓存一致性。下面的具体见证另外证明两个任务确实不同。

## 独立非空实例

`audit/probes/V293OSIntExitDispatchHoareProbe.v` 的 `DXbyte_owned`、`DXextra_owned`、`DXphysical_owned` 和 `DXresources_owned` 从编码字节、独立任务表及不相交内存构造入口，不依赖待证主定理的结论倒推存在性。`DXentry_owned` 使用真实借出规则得到 dispatch 入口。

- 就绪输入 lo=0、hi=16，实际选择 priority 12。
- 当前任务 priority 4，处于时间等待态；目标任务 priority 12，就绪且为最高就绪任务。等待态的 priority 4 不参与最高就绪竞争。
- current 字节=4，入口旧 high 字节=0；真实 callee 随后将 high 更新为12，再用于 guard 和目标指针赋值。不能把入口旧 high=0 写成 callee 返回值。
- `DXentry_nonempty` 同时给出位图/任务表、指针表关系、当前任务成员、最高就绪、不同任务及真实入口所有权。
- `DXmax_entry_nonempty` 覆盖 UINT32 最大计数器；`DXactual_dispatch` 在同一布局、同一入口和同一 outer Inv 上实例化主定理，对任意计数器成立。加一沿用既有 UINT32 模加，不宣称不会溢出。

这些是局部资源非空与定理适用性，不是初始化可达性或完整函数执行轨迹。

## 对照不是完整执行消融

实现前冻结协议：`audit/logs/stage211-interrupt-exit-dispatch-hoare/protocol*.json`。

`DXcomparison_control` 在**同一个实际 DXstate** 上只改变比较表达式 high 参数的标识符：比较旧 high(0) 与 current(4) 得1；比较 current(4) 与它自身得0。该状态同时满足真实 dispatch 入口。这只检验字节读取和比较的可观察差异，不是两份完整 dispatch 执行，也不是从不同 guard 拒绝推出下游 switch 都正确。

缓存 copy 的必要性仍由已冻结的 `BXcopy_ablation` 提供：相同输入、仅删除 copy、两侧均完成 switch，缓存一致性观察不同。BX 是另一份 fixture，只检查其既有定理及递归依赖，不把它当作 DX 新入口的执行或原线程恢复轨迹。

## 核验、旧失败与下一步

本步目录的 `verification.json` 是实际核验汇总；编译输入、每次失败快照及日志全部保留。新增5项结构回归只检查证据/接口形状，不能替代 Coq 证明，也不声称语义 TDD。逐根假设、递归 `coqchk`、两次构建、完整测试及三份精确配置后源码重建均由脚本记录，不预先写成通过。

原有423个失败、1个错误必须保持原 ID 和顺序；旧 `make audit` 的证据身份失配及 `inferules.v` 第581–586行空白错误不删除、不放宽门槛。README/状态仅前插，工程清单仅追加，旧冻结材料及源码保持身份。

清理只限本轮一次性 Trust 驱动及产物、原缓存恢复后的备份；清理前逐项记录身份。保留失败证据、源文件、可复用 Coq 产物、用户材料和已有缓存。

**下一步是真正把外层退出前缀与这个不同优先级 dispatch 接通，并解决第206–209步任意 ISR 上下文与当前 clear ISR/IE=false storage 边界的统一，随后接入真实 builders 与统一函数环境。** 不能把“已经接上内部调度前缀”误写为“整个退出前缀已闭合”。

生产 Inv/ISR/LocalInv/WFInt、初始化、最终 GOOD_OS 与同程序 K1–K4 仍开放；uCOS3 未启动。六门不变：`94 / 1 / 1 / 1 / 1 / 0`。总目标 active，本步不是阶段一完成；未提交或推送。
