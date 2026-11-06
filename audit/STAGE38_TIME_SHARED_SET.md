# 第38步：OSTimeSet 的共享写入与合法抽象更新

## 本轮要解决的缺口

第35步仅证明调用者持有时钟字节时的赋值；第36步 getter 已从 IRQ Inv 借还时钟；第37步对同一 Inv 证明 GoodI。本步不能把物理时钟改掉以后直接用普通断言蕴含改写抽象状态。真实 C、配置、端口、旧 AST、旧生产源、旧测试和旧证据均不改。

新增生产模块 `certiucos/v293/proofs/V293TimeSharedSet.v`；稳定上层接口是 `V293_OSTimeSet_shared_body`。继续使用既有 `V293_TimeSet_body`：保存单元清零 → encrit → `now=ticks` → excrit → void return，没有另造空程序替代。

## 最小连接

1. `V293_time_set_step` 是明确的 `osabstep` 规格：参数必须恰为一个32位整数，旧 `ostmid` 必须存在，结果为 None，并且只更新该槽。
2. `V293_time_set_transition` 使用框架 `spec_prim_step`：证明抽象域未变、TCB 域未变、当前任务未变，不是仅有 set 操作的状态引理。
3. `V293_time_set_absinfer` 从真实 primitive transition 推导 `absinfer_prim`；任意物理资源和其他抽象槽位是分离 frame。物理内存不随这个抽象步骤改变。
4. `V293_time_shared_set_copy` 从原共享核心取出旧见证，实际 `V293_time_copy` 执行写入；此时物理 n／抽象 old 暂时不同。通过 `abscsq_rule` 合法更新抽象状态，才用同一个 n 重建**原来的**共享核心。
5. 完整函数体连接保存单元初始化、真实进入／退出规则和 void return。入口只持有名称绑定、局部单元和 frame，不持有时钟字节，也没有成功 store、表达式值或运行结果 oracle。

这里复制步骤的最小 frame 条件是 `can_change_aop`，不是 `GoodFrm`：内部 frame 包括中断控制断言，后者不能满足 GoodFrm。外层进入／退出仍按原规则要求调用者 frame 满足 GoodFrm；没有放宽框架门禁。

## 独立入口与反例检查

独立 probe 不导入旧 probe。字面内存：时钟80、参数81（42）、保存单元82（Vundef）、当前指针90（指向91）。四个抽象槽位完整存在，旧时间7与新时间42不同；同时也证明任意旧时间的共享核心和局部资源可同时成立。两半 CurTid 来自同一实际可写指针分裂，而非假设两块可能不相容的内存。调用者确实没有80块时钟字节。

`SetterNoAbs` 实际证明空局部不变式 fixture 满足 NoAbs；`SetterBodyInstantiation` 对应上述具体参数和资源，不只留下一个未经实例化的 NoAbs 前提。字面 primitive 检查 ostmid 7→42，当前任务／任务表／事件表保持。

前瞻协议在生产实现之前冻结：

| 单因素对照 | 保持不变 | 实际应授的信用 |
|---|---|---|
| primitive 更新值 n 改为 old | 全部 Proof、C／AST、物理赋值 | 只检查 primitive 规格／transition 的连接；提前拒绝不证明下游都有效 |
| 唯一物理 copy 调用的规格参数改成 Int.one | C／AST、抽象规格、其他证明文本 | 只检查实际赋值调用与参数所有权的连接；不是运行了一个篡改后的 C 程序 |

## 仍未完成

- 当前共享函数体仅处理 IE=true 且所有 ISR 活动标志为 false 的任务入口。
- 使用 `NoAbs li`，字面实例是空 LocalInv fixture，不是完整任务资源生命周期。
- 局部存储已经分配；调用／参数分配／释放与最终 API 规格登记尚未连接。
- 退出临界区后允许中断和其他任务运行，**返回时不声称全局时钟永远仍是参数42**。归还的共享 Inv 保证物理／抽象时间继续一致，而非保持一个固定数值。
- 手工配置后 C／AST 映射不是验证过的前端，也不是原端口仿真。
- 初始化、所有 ISR safety、GOOD_OS、同程序 K1–K4 仍未完成；uCOS3 尚未开始。默认 audit 和旧测试失败必须如实保留，六阶段覆盖不晋级。
- 复用已有编译依赖，不是全仓 source-only 干净构建；没有提交／推送。

## 下一步

把已经建立的 getter／setter 共享 body 接口接入真实调用生命周期和 API 规格，再处理当前完整任务／ISR 不变式及初始化连接；不能以新增一个 body 定理替代这些义务。

实际命令、测试差分、假设检查与清理结果以本目录日志的 `final-report.json` 为准；下面的收尾节只在实际验证结束后追加。

## 实际收尾结果

正式 gate01 六命令退出码 `0／0／0／1／1／0`，独立 coqchk 两模块通过；生产4根／独立6根假设仅既有 classic／functional_extensionality_dep。primitive 负控在第29行未闭合义务处拒绝；copy 规格参数负控在第127行拒绝，只授各自连接信用。新增8测试清理前后全过。

全量1098测试实际376失败、1错误；之前375项诊断全部保留，只新增第37步冻结当前项目身份／精确append两项失败。旧测试、旧证据没有改写，清理前后诊断 multiset 相同。scope／固定C／diff检查0；默认audit仍exit2（stale function evidence input identity），六门94／1／1／1／1／0未晋级。

旧178活动源／890生产依赖逐一不变；新增后179＝76目标＋103框架／tactics。基线只有已声明4路径前插／追加，缺失0；HEAD不变，未提交／推送。第36／37步冻结manifest分别117／142项无漂移，旧lia／nia缓存未变。

逐项列出类型、大小、hash／链接目标和目录成员，全部重新核实后首次unlink：删除386项（356软链接、30实文件／953092字节）及45目录；仅两个负控树、一次新鲜C临时物化树、probe5产物。基线删除0，全部源／成功和失败证据／既有缓存／生产依赖保留，新增5个可复用生产产物保留。并非全仓source-only构建；总目标仍active。
