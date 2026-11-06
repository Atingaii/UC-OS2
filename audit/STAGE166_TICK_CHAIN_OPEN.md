# 第166步：从同一 canonical 共享资源打开完整 tick 任务链

## 解决的缺口

第165步已经证明原完整 `while` 同步抽象任务表并无损归还共享 core，但 caller 仍须提前
持有整链 raw 字段。本步从**同一份** canonical task／ready／clock 资源打开完整有限合法链，
接回第165步正式循环规则。不是只再证明一个 head 节点，也不是新建执行 oracle。

C、配置、AST、框架、tactics、旧证明／测试和冻结证据均不改；只增加当前目标中的接口和探针。

## 接口与字段来源

生产文件：`certiucos/v293/proofs/V293TimeTickChainOpen.v`。

- `V293_tick_chain_core_pre`：共享 fields、canonical ready payload（含完整 task records）、
  同一 clock，以及 scan、缺失字段补片、caller frame 联合拥有。没有整链 raw 前置。
- `V293_tick_canonical_node_open`：打开 canonical 记录中的实际 priority／pend 见证。
  由有限 priority 的唯一性匹配节点，使用精确布局置换，不从可读性推导可写所有权。
- `V293_tick_canonical_chain_open`：对有限 bindings 归纳，唯一 key 保证 head／tail 分离；
  依次打开 event／time／ready，最后处理 idle，完整保留余下 frame。
- `V293_tick_chain_core_open`：打开完整 canonical taskmap 和 ready payload，实际 pend 选择
  不改变同一抽象 taskmap、链顺序、head、状态或抽象 tick 程序。
- **`V293_tick_chain_core_hoare`**：接原完整 `swhile` 与第165步有序抽象链，归还同一更新后
  task／ready／table／clock core、scan、所有 residual 和 frame；post 不用 `Atrue` 丢资源。
- `V293_tick_chain_core_semantics`：仅经既有 `RuleSound` 正向导出。

| 字段 | 本步真实来源 |
|---|---|
| event wait 的 pend | canonical record 的实际隐藏见证；不是描述符 hint |
| time wait 的 pend | 显式补片，因为 canonical time record 不含此字节 |
| ready 的 delay0／pend | 显式补片，因为 canonical ready record 不含这两个字段 |
| 全链 Next | 显式补片；任务表本身不编码链顺序 |
| clock／taskmap／ready／table | 同一 canonical 联合资源，没有复制抽象槽 |

`V293_tick_pend_choices` 只记录打开过程中实际选取的 byte 值，不是额外执行前提。
合法链限制沿用第165步：未挂起 bindings、字段范围有效、NoDup key，完整任务域恰好为链加 idle。
不能推广到 suspended／flags 等尚未覆盖分支或任意生产状态。

## 独立入口与单因素对照

探针：`audit/probes/V293TimeTickChainOpenProbe.v`。
协议在生产实现前冻结：`audit/logs/stage166-tick-chain-open/protocol.json`。

`COentry` 复用第165步独立 encoded heap 的 `WCspatial`／`WCabstract`，直接将实际 bytes 打包为
canonical records；不调用旧 raw 入口 `WCentry`，也不调用新 opening／Hoare 定理构造入口。
TCB 同块、不相交；事件到期、时间倒计时、ready、idle 共存。13项实际优先级表、readonly current、
clock37、canary99、合法栈顶1都保留。`WCcurrent_member` 的 current=ready4 确实在任务表内。
两种初始 IE 共用同一物理堆。LocalInv 仍用旧空见证，不声称初始化可达。

- `COhint_same`／`COhint_entry`：只把事件节点描述符中的 pend 提示7改为99，canonical 入口、
  taskmap、链程序和补片全部不变。
- `COevent_selected`：从上述入口聚焦真实记录，再调用正式单节点 opening；
  其 raw 所有权推出实际 load，与独立字节堆的 pend7 比较，经有界 byte 单射性推出所选 pend=7。
  不仅证明一个数学 choose 函数恒等式，也不把99复制为实际值。
- `COtime_ready_supplements`：分别只改 time／ready 的 pend 补片7→99；同一 heap、canonical
  taskmap和抽象链程序不变。实际 load7 与错误补片要求的 load99 矛盾，两个错误入口均被拒绝。
- `COexecution_control` 明确**复用165**原操作执行、有序 `spec_stepstar`、精确 post、14项 reads，
  以及同一个实际 Mf 上只中和抽象任务更新的拒绝证据；同时提供本步新 canonical 入口。
  不是新 RuleSem 的运行实验，不是删除版源程序实验，也没有用 correlated early rejection
  推断下游机制。正式规则实例由 `COhoare`／`COsemantics` 单独验证。

## 验收状态

机器实测结果及失败日志保存在 `audit/logs/stage166-tick-chain-open/`。
以 `verification.json` 为验收依据；若最终核对未通过，本节不能额外授予信用。

- 稳定生产 `open16` 编译退出0；完整探针 `probe08` 编译退出0、耗时30.25秒。
  12个生产根＋14个探针根共26个新根，336活动＋56探针模块的独立检查通过；
  `coqchk` 耗时943.11秒。547份Coq输入在独立检查期间不变。
  允许假设仍仅 classic、functional_extensionality_dep、eq_rect_eq，没有扩大。
- 新增7项回归全部通过。三轮全套均为1993项、旧423失败／1错误；
  与修改前1986项及第165步比较完整失败／错误ID集合，未新增失败，不把旧失败算通过。
  见 `full-tests.json`、`post-cleanup-tests.json`、`final-tests.json`。
- 构建与清理后重建均退出0。旧 `make audit` 仍退出2：project audit通过，
  函数证据input identity仍陈旧；whitespace仍退出2，仅原 `inferules.v` 581–586六行。
  不重跑或改写旧冻结证据以制造全绿。
- 保留24次正式文件编译源码快照、命令及日志，其中18次非零。
  `probe03` 因单次 `flat sep auto` 超过180秒而主动SIGINT，属于性能中断，
  不当作语义反例。后改用精确cell permutation，同一堆／资源／合同不变；
  最终完整探针独立重编译通过，没有依赖一次性隔离模块。
- 先确认每个目标及两份缓存备份哈希，再清理8项一次性信任模块／缓存备份，共688632字节。
  两份既有算术缓存恢复本步原始哈希。保留源码、所有失败证据／快照和可复用Coq产品；
  见 `cleanup-inventory.json` 与 `cleanup.json`。
- 最终核对29280份旧文件，预期差异仅本步前插的README／状态说明、项目入口与生成依赖。
  第165步冻结manifest不变；最终验收及交付哈希由本步 `verification.json` 与
  `checkpoint-evidence-manifest.json` 固定。结构红态仅是缺少交付材料，不是行为消融证据。

## 未完成与下一步

本步减少了 caller 前置中的全链 raw 假设，但仍要求 canonical core 加上真正缺失的链补片。
两种初始 IE 的局部规则并不等于生产 IRQ 资源借出；生产 Inv／LocalInv、CPU hook、完整
`OSTimeTick`／API／ISR、初始化／WFIFun／GOOD_OS 与同程序 K1–K4 仍开放。
六门仍为94/1/1/1/1/0，本步不增加整函数信用；uCOS3 未开始，总目标 active。
下一步应把该 canonical 入口连接到真实生产不变量／后 hook 路径，而非继续复制 raw 前置。
不提交、不推送、不改写旧失败证据。
