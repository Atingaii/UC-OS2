# 第176步：同一 tick／hook 规格接收共享状态快照

## 本步解决什么

175已将clock/run放入同一Spec，但ct/es/si/ci仍是函数外固定参数。本步把这四项也接入框架已有lg通道：**不用更换Spec即可选择当前任务、事件映射、中断栈与临界区栈的有效快照**。不添加状态模型、不修改旧不变量。

生产文件：`certiucos/v293/proofs/V293TimeTickSharedSnapshot.v`。

```text
lg = [logic_val(Vint32 clock); logic_val(Vint32 running);
      logic_val(Vptr ct); logic_absecb es; logic_is si; logic_cs ci]
```

`V293_tick_shared_index`解码；`V293_tick_shared_guard`要求ct=调用线程、run<256、gettopis(si)<=INUM。有效索引仍使用原共享资源；非法索引入口为Afalse。两个caller local不归hook所有。

稳定上层接口是 **`V293_tick_shared_internal_contract`**：量化所有vl/lg，连接真实`BuildPreI`／`BuildRetI`，通过`V293_tick_shared_hook_call`的真实call_rule接原完整tick body和返回。hook前后使用同一lg；不是各自存在量化、不执行hook或另换函数体。

## 独立非空见证与单因素对照

探针：`audit/probes/V293TimeTickSharedSnapshotProbe.v`。固定同一个CCprogram与不带运行快照参数的SNspec。

| 证明 | 改变什么 | 实际证据与不变部分 |
| --- | --- | --- |
| SNbuilders／SNcontract／SNsemantics | lg和调用线程 | 真实builder、完整body的条件InfRules／RuleSem；一个固定Spec |
| SNall_snapshots_same_spec | 任意合法clock/run/ct/es/si/ci | 选择完整builder前后资源，Spec不变 |
| SNallocated | 任意es/si/ci，满足run与topis范围 | 完整入口独立非空；保留BHmemory实际分配内存和两个raw local |
| SNsame_endpoint_event_control | 只将es从ChainEvents改为emp | 同一非空SNstate、内存、代码、栈、clock/run；实际absecblsid槽拒绝 |
| SNsame_endpoint_is_control | 只将si从[1]改为[2] | 两者topis均合法；由实际Ais拒绝，不以范围门冒充下游检查 |
| SNsame_endpoint_cs_control | 只将ci从[false]改为[true] | 同一端点、si及其他资源；由实际Acs拒绝 |
| SNidentity_gate_control | ct从WhileReady改为WhileHead，调用者仍WhileReady | 只证明身份门拒绝；不归功于下游资源检查 |
| SNactual_fields | 不改状态 | 独立从实际共享槽读取curtid与事件映射，补充身份门不能证明的资源事实 |
| SNmissing_hook／SNno_EqDom | 不伪造hook实现 | 缺失hook无下一步，当前fixture不满足EqDom，不能推出WFFunEnv |

`SNallocated`先打开旧完整非空入口，保留物理内存／local／ready任务资源，只替换fixture抽象事件槽，再对GoodFrm资源运输中断辅助状态并重建真实switch invariant。**这是独立状态fixture构造，不是一次kernel事件更新或ISR执行trace。** 任意事件映射不代表已证明任务等待队列与事件映射的全局一致性；非空物理任务owner实例目前只有WhileReady，不能据此声称所有task布局均已构造。

## 对抗复核与信任边界

先写不可变protocol、baseline和源码身份，再逐次编译。每次尝试保留日志、退出码、源码快照；编译失败仅是诊断，不作语义反例。`adversarial-review.json`逐项记录12个质疑及对应证明或限制。

结构测试只检查接口连接形态；语义由Coq内核、Print Assumptions与递归coqchk独立检查。只有本步两个新入口及递归依赖重检，不冒称所有旧入口已重跑。未改C、配置、AST、框架、旧证明、旧测试或旧冻结证据；README/状态仅前插，项目清单仅追加。

## 尚未完成与下一步

bindings、idle、message、全局地址和R仍固定；IE=false、isr全清、合法有限未挂起链及旧LocalInv前提不变。未覆盖活跃ISR、动态任务拓扑、全局一致性、生产hook实现和返回、全程序函数环境或初始化。运行完整post的独立非空实例与完整tick trace仍未建立。

本步不再将“es/si/ci变化必须更换Spec”作为缺口，但不能说统一全局规格已安装。下一步需要对照固定CPU边界与全程序义务，接可变任务资源／生产ISR及hook契约；不得用空hook或放宽不变量制造闭合。

覆盖仍94/1/1/1/1/0，不授予新增无条件整函数信用。第一阶段GOOD_OS与同程序K1–K4未完成，uCOS3未开始；总目标active，不提交／推送。各检查最终结果见本步日志目录的verification.json及冻结manifest；旧全套失败和旧审计问题保留原状。

## 本步实际检查结果

- 生产284行8根、探针367行21根，稳定编译通过。29根Print Assumptions及两个入口连同递归依赖的coqchk通过（419.60秒）；567份Coq输入在检查期间不变。仍只使用既有classic、Eqdep与函数外延性三项，未扩大允许假设集合。
- 新增5项回归通过；全套2038→2043，仍423失败／1错误，完整失败／错误ID集合不变。写入最终说明后另跑一次全套，由final-documented-tests.json及verification.json核对，不宣称全套全绿。
- make build与project-audit退出0。make audit仍退出2（旧函数证据input identity过期）；git diff --check仍退出2（旧inferules.v 581–586六行）。不改写旧冻结证据或删除旧失败。
- 16次编译、13次非零诊断，源码快照与日志全部保留；非零诊断不是新增语义反例。临时Trust检查产物、备份与本步新测试字节码逐项清理，原lia/nia缓存恢复；生产／探针可复用Coq产物保留，清理明细见cleanup.json。
