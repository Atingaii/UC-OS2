# 第279步：把弱 storage TaskSim 前推至缓存复制入口

## 1. 本步具体增加什么

278 已经覆盖实际旧任务的 `switch` 切出点。本步把该结论沿
`V293_interrupt_handoff high current target` 的缓存赋值向前移动，证明同一
`TaskSim` 从赋值前开始成立，不把已执行的全局 trace 直接冒充任务模拟。

生产文件：`certiucos/v293/proofs/V293HandoffTaskSim.v`。
唯一生产公开接口：`V293_handoff_TaskSim`；另有三个内部桥引理。
独立见证：`audit/probes/V293HandoffTaskSimProbe.v`，六个证明根。
正式登记只加入生产文件，probe 不加入 `_CoqProject`。

**不是完整调用入口 TaskSim；GOOD_OS 未闭合；uCOS3 未开始。**
目标仍为先完成固定 uC/OS-II 整核 GOOD_OS 与同程序 K1–K4，再进入第二阶段。

## 2. 源码与抽象边界

固定上游提交 `0c4a48e6fbc6e915714e816196619a5481accf0c`；
`os_core.c:693–736` 的 OSIntExit 在第723行调用 `OSIntCtxSw()`。
本步不修改 C、配置、AST、框架、授权修复或 ADR-0010。

这里的“七个 C 小步”严格指 **ADR-0010 已接受调用点解释中的 C 语义步骤**：
`OSPrioCur := OSPrioHighRdy; switch OSTCBHighRdy`。
不是声称原始 C 函数体直接包含这次赋值，也不是原始外部声明到该边界的
refinement。原始端口函数无实现时的停顿结论仍然保留。
具体文件哈希与定位见本步 `source-identity.json`；没有重新预处理。

## 3. 公开接口需要什么

- 调度器绑定与当前 OS 函数绑定；有限 SKIP caller；
- 当前 `IE=false`、`si=nil`，保存栈 `top::ci`；`top` 不固定；
- high/current 的局部查找为空及真实全局地址/类型绑定；
- `nh<256`；抽象任务表中旧任务存在，next 是最高 ready；
- saved(bs) 私有，以及 ready SWINVt、缓存单元、最高优先级单元、
  目标指针单元和其余 storage 的分离所有权。

公开前提不接收 TaskSim、执行 trace、store 或 free 的成功结果。
实际 `store` 由独占缓存所有权构造；内部桥接引理接收 continuation 和 store，
但公开接口自行证明这些义务，不能把内部前提误报成公开接口。

## 4. 七步如何接起来

| 次序 | 原 C 语义规则 | 内存变化 | 证明手段 |
| --- | --- | --- | --- |
| 1 | `sseq_step` | 无 | 进入赋值，挂起 switch |
| 2 | `sassign_step` | 无 | 两侧 Tint8 类型成立 |
| 3 | `evar_step` | 无 | 从拥有的 high 单元读取 nh |
| 4 | `sassignrv_step` | 无 | 转向 current 地址求值 |
| 5 | `eaddr_step` | 无 | 从环境得到缓存地址 |
| 6 | `sassignend_step` | 写缓存 | 独占所有权构造 store |
| 7 | `sskip_step` | 无 | 到达既有 switch TaskSim |

每步通过 `V293_invariant_cstep_TaskSim` 向前接原 TaskSim。
六个无写步骤对任意可分离外部 frame 保持总堆，以 `cstep_idmove_deter`
限制所有 C 后继。写步骤使用 `store_mono`、`join_store_join` 和已有写步唯一性，
不是只证明一个固定总堆上的可执行轨迹。CurLINV 在写前、写后分别由所有权推出。

写后把缓存/high 转入既有弱 storage，并在 **同一共享子堆** 上构造
SWINVt 与 SWPRE_NDEAD，调用278的 switch 桥。
因此 inherited callback 仍量化任意兼容归还的共享资源，saved(bs) 私有；
没有改为只接受原共享堆的恢复。

## 5. 同一个完整调用的非空见证

`HCactual_handoff` 复用既有完整活跃调用的 fresh 分配入口和实际前缀。
全局 trace 到达赋值前 handoff，随后 **在同一个 M 上** 分离出：

- Mt/Ot：本步 Owned 资源及其 TaskSim；
- Mf/Of：`IWframe`；即 saved98 与 RCframe 外部。

完整前缀的 trace 与 handoff 起点 TaskSim 是不同证据：
后者由 `HCpartition` 调用新生产接口获得，而非从一条 trace 推出。
`HCnonvacuous` 用两个 fresh-block 存在性和既有 `SPph` 提供非空实例。
该真实实例的保存栈顶为 false；公开生产结论量化任意 top，
不把此事实升级为完整调用的 true 入口可达性。

### storage 列表顺序的区别

本步 `HCcells br = cache94 :: high91 :: HCrest br`，其中 rest 为
`96,97,br,95` 四个 storage 单元。它是既有弱 storage Inv 家族的另一个布局实例。
与278 `STcells` 包含相同物理单元，但列表顺序不同。
**没有证明列表置换下 Inv 的等价，不宣称与278的 G 字面相同。**
既有278定理对任意 cells 量化，本步以该布局实例调用；
没有引入新不变式或解决强 current/cache guard 缺口。

## 6. 反例、必要性与未完成消融

`HCactual_switch_gap` 复用原调用后续 trace：复制后 cache=4，
旧任务仍 blocked，因此强 current guard 拒绝。不是换程序或只检查语法。
这项证据来自既有276，本步没有新增缓存复制的双执行消融。

`HCsaved_necessary`、`HCreject_missing_saved` 说明 saved 所有权蕴含真实 load，
load=None 会拒绝前提。这只是逻辑必要性检查，**不是完整单因素执行消融**，
也没有逐项移除绑定/最高 ready/类型等前提构造全部独立非空反模型。
`protocol_fully_completed=false`，不以相关的早期拒绝代替下游机制验证。

## 7. 验证记录与保留失败

本步日志：`audit/logs/stage279-handoff-tasksim/`。

- 两个源各独立稳定编译两次；源码哈希应前后一致。
- 十个证明根逐一 `Print Assumptions`，递归 coqchk 检查新模块和依赖。
- 新增五项 Python 结构/身份回归；结构测试不替代 Coq 语义核查。
- 全量旧 failure/error ID 与顺序必须保留；build、project audit、make audit
  和空白检查分别如实记录，最终实测以 `verification.json` 为准。
- 所有开发失败的源码快照、命令和日志保留；不重写原快照。

开发期出现过缺少直接 import、术语/列表 notation 冲突、固定环境的 entailment
泛化错误、目标存在式需要显式 witness、nh 实例化滞后和必要性引理的环境参数
未实例化等编译错误。修正证明而非放宽结论；逐次快照保留完整历史。

## 8. 明确还没有完成什么

- 完整 OSIntExit 调用入口 TaskSim/WFIFun、WFInt；
- 初始化可达性及任意中断交错；ISR 全清、si=nil、空 LINV 的限制仍在；
- 强 current/cache 不变式贯穿全部路径；
- 旧 blocked 任务的真实调度切回：不是全局切回可达性；
- 原始外部端口 refinement、完整共享循环；
- 整核 GOOD_OS、同程序 K1–K4、uCOS3。

下一步沿实际调用路径继续前推 TaskSim，优先处理比较、计数与调度 helper 的连接，
不以新增独立模型替代函数纵向连接。清理仅限本步一次性 Trust 检查产物，
恢复原缓存；正式源、失败日志、快照和可复用编译结果保留。未提交/推送。
