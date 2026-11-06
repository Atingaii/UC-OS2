# 第165步：完整原 while 的抽象任务更新与共享 core 归还

## 本步解决的问题

第160步的完整原 `while` 已有正式 `InfRules`，但执行期间抽象任务表不变。
第151–153步另有操作语义执行和有序抽象链的端点证明；它们不能自动充当正式 Hoare 连接。
第164步则仅从 canonical core 打开一个等待节点，不能冒充整条混合链的证明。

本步保留原循环规则，把原有 `V293_tick_chain_code` 的逐节点抽象步接到完整原循环后，
将更新后的任务记录、ready bitmap、实际优先级表和不变的 clock 归还同一个共享 core。
前置仍要求 caller 联合持有**全链 raw 字段**；本步不是 canonical core 到全链入口的打开证明。
C、配置、AST、框架、tactics、所有旧证明／测试／冻结证据保持不变。

## 稳定接口及为什么没有引入 oracle

生产文件：`certiucos/v293/proofs/V293TimeTickWhileCore.v`。

- `V293_tick_chain_absinfer`：对有限合法 bindings 归纳；ready 节点跳过，waiting 节点使用既有
  `V293_tick_wait_absinfer`，以原 `absinfer_seq`／`absinfer_seq_end` 按顺序组合。
  NoDup 保证前面修改任务不会改变后续任务 lookup；没有新增一次性 batch primitive。
- `V293_tick_while_core_pre`：完整 raw loop 字段与 extras、idle extras、同一任务／事件／当前／时间槽、
  实际 priority table、readonly current、clock、caller frame 联合拥有。不是分别投影后拼接权限。
- `V293_tick_while_core_raw_close`：更新后的字段通过既有 lossless 重组得到 canonical records，
  同一新任务表与 ready relation 绑定；scanner、所有链 residual 和 frame 精确保留。
- **`V293_tick_while_core_hoare`**：原完整 `swhile` 的稳定正式接口，支持两种初始 IE，
  组合旧循环规则和上述抽象步。前提没有执行、表达式求值、另一个 InfRules／RuleSem 成功假设。
- `V293_tick_while_core_semantics`：仅由既有 `RuleSound` 正向得到。

主规则对任意符合绑定形状、字段范围、唯一 key、ready relation 和环境／栈／frame 义务的有限链成立。
这里的合法形状不包含 suspended 等未建模分支；不能推广到所有内核任务状态。
post 不用 `Atrue` 丢弃字节。证明中的 `CurLINV_extend` 使用纯投影取得局部不变量，
不依靠 `Atrue` 重建可写资源；精确返回资源由 lossless implication 独立完成。

## 非空入口与独立执行

探针：`audit/probes/V293TimeTickWhileCoreProbe.v`。
前瞻协议：`audit/logs/stage165-tick-while-core/protocol.json`。

四个 TCB 在同一 block 的不相交字节中，含 event delay1、time delay3、ready 与 idle。
实际13项优先级表包含它们的指针。当前任务为表中的 ready4，`WCcurrent_member` 机器核对；
不沿用第164步“当前任务不在任务表”的 fixture。clock37、canary99、合法栈顶1、readonly current
共同构造 `WCspatial`／`WCentry`；入口不调用旧 `RCentry` 或新主规则。
LocalInv 仍为旧空见证，故这不是初始化可达性证明。

`WCrules`／`WCsemantics` 将同一入口实例化到正式规则。
`WCliteral_execution` 另用既有 **操作语义** `V293_tick_while_owned_execution`，
在本次新联合内存和两种 IE 上执行原循环，并独立取得有序 `spec_stepstar`。
只复用生产规则的精确 closing implication；不执行新 RuleSem，也不把端点观察当作 Hoare 证明。

| 观测 | 原循环结果 |
|---|---|
| ready rows / group | 16、20 / 3；前后 bitmap 都非空 |
| event 节点 | delay0、pend1，event 指针保留 |
| time 节点 | delay2、pend7 |
| 三个 Next | Second、Ready、Idle，均保留 |
| scan 指针 | Idle |
| clock / canary | 37 / 99，不变 |

`WCexecution_control` 针对**同一个实际 Mf**、END 和控制状态，只把抽象任务表恢复为旧值。
`WCreject_neutralized` 从实际 high row20 推出 priority10 ready，与旧表中等待节点冲突而拒绝 core。
不清空 bitmap，不触发非空性早拒，不改 AST；这是输出抽象更新的单因素中和，
不是“删除版源程序运行”。诊断读值中的 `Atrue` 仅用于投影，不生产所有权。

## 验收入口

稳定编译、独立信任检查、完整失败 ID 比较、构建、清理及最终哈希核对保存在：
`audit/logs/stage165-tick-while-core/`。最终结果以该目录的 `verification.json` 为准。
编译失败的源码快照与日志保留；结构红态仅是缺少新交付材料，不是行为消融证据。

## 实测验收与清理

- 生产文件 `while14` 与完整探针 `probe06` 编译退出0；完整探针重编译约143.88秒，
  不是只检查隔离后缀。27个新证明根、335活动＋55探针模块独立检查通过；
  545份Coq输入在检查期间不变。允许假设仍只有 classic、functional_extensionality_dep、eq_rect_eq。
- 新增7项结构回归全部通过；全套实测1986项、423失败／1错误。
  与本步修改前1979项基线以及第164步比较完整失败／错误ID，不把旧失败算作通过。
  各轮结果保留于 `full-tests.json`、`post-cleanup-tests.json`、`final-tests.json`。
- 构建与清理后重建均退出0。旧 `make audit` 仍退出2：项目审计通过，但函数证据identity陈旧；
  whitespace仍退出2，仅原 `inferules.v` 581–586六行，不改写旧证据制造全绿。
- 20次正式文件编译快照中17次非零；另有13次隔离编译快照，其中11次非零。
  全部源码快照、命令和日志保留。隔离prefix实际编译成功后才复用；prefix未记录总耗时，
  仅保留逐命令计时，不据此宣称性能改进。最终完整探针不依赖隔离模块。
- 先逐项确认再清理：隔离模块源码／产品12项3055456字节；信任临时模块及缓存备份8项678702字节。
  合计20项3734158字节，两份既有算术缓存恢复本步原始哈希。
  保留交付源码、失败证据、快照和可复用Coq产品；清单分别见 `debug-cleanup-inventory.json`
  和 `cleanup-inventory.json`。
- 最终核对检查29124份旧文件，预期差异仅本轮前插的README／状态说明、项目入口和生成依赖。
  第164步冻结manifest哈希不变。以 `verification.json` 和本步manifest为最终结果，
  若核对未通过则不能把本节当作额外信用。

## 剩余缺口与下一步

1. 尚未证明任意 canonical core 能打开整条混合链的 raw 前置。旧单等待节点 focus 不是其替代。
2. 两种初始 IE 的局部规则并不等于已从生产 IRQ 不变量借出全链资源。
3. 尚未连接 CPU hook、完整 tick／API／ISR；生产 Inv／LocalInv、初始化／WFIFun 仍开放。
4. `GOOD_OS` 与同程序 K1–K4 未完成；六门仍94/1/1/1/1/0，无新增整函数信用。
5. 第一阶段未完成，uCOS3 未开始；总目标 active，不提交／推送。

下一步应从同一 canonical taskmap、ready 和 clock 见证无损打开全链，
把 caller 需要额外交出的字段严格限定为 canonical records 真正缺失的 Next／pend 等补片。
不能把本步完整 raw 循环的归还误报为已经完成生产不变量借还。
