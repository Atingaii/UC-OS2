# 第251步：Exit 真实赋值前缀与切换前闭合障碍

## 这一步为什么必要

第249步的新候选在原资源上增加同堆普通合取条件：当前优先级字节与抽象当前任务关联，
或者抽象当前任务已经最高就绪。完整 GoodI 已通过，第250步接通了真实入口和 Enter。
但这些结果没有证明 Exit 的中间状态始终满足该候选。

本步保持固定 C/config/AST/framework、旧 Inv/LI/BDspec、证明、测试与冻结证据不变，
检查真实 changed handoff。没有删除 copy，也没有把 copy 与 switch 擅自合并为原子动作。

## 最小执行路径与结果

`V293_interrupt_handoff` 的实际 AST 是先赋值当前优先级，再执行原 switch primitive。
`framework/logic/inferules.v` 的 `switch_rule` 要求在 primitive **之前**关闭 `SWINVt I t`。
GoodI 支持切换后的状态，不替代这条执行前提。

固定同一 typed 起点，Waiting 优先级6，目标 Ready 优先级4：

| 时点 | 地址94的当前优先级 | abstract curtid | 当前关联 | 当前最高就绪 | 新候选 |
| --- | --- | --- | --- | --- | --- |
| copy 前／省略 copy 的比较点 | 6 | Waiting | 真 | 假 | 可关闭 |
| 真实 copy 后、switch 前 | 4 | Waiting | 假 | 假 | 任意分离 frame 下均不可关闭 |
| 原物理 switch 后 | 4 | Ready | 本步未单独检查 | 真 | 可关闭 |

最后一行的闭合证明只使用最高就绪分支，不额外声称当前关联分支已被单独检查。物理 switch 指框架 `lpstep`，不是机器码／硬件执行。

## 稳定接口与正负对照

生产模块：`certiucos/v293/proofs/V293CurrentHandoffPrefix.v`。

- `V293_current_handoff_prefix` 证明真实计数增量 → skip → 优先级复制。
  ambient `RI` 真正任意，分别调用原通用 increment/copy 规则，不搬运旧 Inv 下整段 Hoare。
  后置条件是打开的资源断言，不冒称已关闭新候选，也不包含 switch。
- `V293_current_handoff_core_enrich` 仅在已知完整堆 guard 和字节拥有者时用于构造候选；
  guard 限制回拥有者子堆，没有复制字节所有权。
- `V293_current_handoff_switch_reject` 从相同抽象任务表／当前任务、真实字节 load 和两个
  分支均假，推出任意分离 frame 下 `SWINVt` 均不成立。
- `V293_current_handoff_switch_highest_frame` 是切换后的断言闭合辅助，
  不是跨 Inv 的 Hoare 迁移定理。

独立模块：`audit/probes/V293CurrentHandoffPrefixProbe.v`，生产模块不导入它。

| 对照 | 证明根 | 结论 |
| --- | --- | --- |
| 新 Inv 的真实前缀 | GHprefix_in_new_candidate | 通用规则可直接实例化同一 GHinv |
| 真实赋值与 typed 非空 | GHactual_copy_obstruction | 真实 cstepstar，实际 store 6→4，其它地址及 abstract map 不变 |
| 固定状态换不变量 | GHactual_copy_obstruction | copy 前旧／新均成立；copy 后旧成立、新候选任意 frame 都不成立 |
| 排除资源拆分误诊 | GHrejected | 使用完整堆 load 与抽象 map，反驳不依赖某种拆分选择 |
| 排除候选禁止所有切换 | GHphysical_switch_still_works | 同一 copy 后状态可走原 lpstep，之后新候选成立 |
| 独立 GoodI 正对照 | GHcandidate_still_good | 同一 GHinv 的完整 GoodI 仍成立 |

起点取自既有真实局部执行前缀的 typed 状态；本步没有将该前缀拼成完整启动／中断执行。
省略 copy 的消融只保留同一个 M 作为比较点，不修改实际交付程序。
旧 `JHcopy_ablation` 还保留有／无 copy 的两条 switch 对照，本步没有改写其证据。
新定理没有声称完整执行了两次 C 函数，也没有复用不相同的末态当作单因素对照。

## 诊断结论及边界

预先冻结的三个假设依次是：字节／抽象当前任务暂时错位、资源拆分错误、候选禁止切换。
上述正负对照支持第一个，并排除后两个作为该具体闭合障碍的原因。
这不是一次 tactic 失败推导出的数学不可能，而是具体 typed 状态的 Coq 否定定理。

反驳仅针对当前候选在真实 copy 后的 switch_rule 闭合前提；
**没有证明所有 InfRules 推导不可能，也没有证明框架不健全。**
这不是初始化可达证明，不是内核漏洞，也不是完整 Exit 函数环境或中断返回。
Exit/Sched 环境尚未迁移；不是 `WFInt`，不是 `GOOD_OS`，同程序 K1–K4 未闭合，uCOS3 未开始。

下一步应处理 copy → switch 瞬态与函数边界的兼容性，先比较最小可行方案，
再在保留原 same 分支反例及本步 typed 反例的条件下验证。
不能简单去掉关联条件、增加未经证明的前提、删除 copy，或用旧 Inv 的函数结论冒充新 Inv 结果。
涉及真实源码或既定抽象边界改变时，应单独说明范围，不在本步暗改。

## 验证材料

预先协议、每次编译快照、失败日志、稳定编译标签、所有新证明根的 Print Assumptions、
递归 coqchk、完整构建／测试／审计结果均保存于 `audit/logs/stage251-current-guard-handoff/`。
结构测试只保护接口与身份，不替代语义检查。最终数值以 verification.json 为准；
旧失败及新增失败分别记录，不改旧测试、门槛或冻结证据。

未提交／推送；总目标保持 active。这是纵向集成障碍的定位，不是整核通过。

## 本轮实测

- 8项生产证明根、8项独立检查根，共16项，Print Assumptions 与递归 coqchk 均通过。
  仅使用既有 classic / functional_extensionality_dep，没有新增逻辑假设。
  信任检查期间726份 Coq 输入保持原字节，其中包括一次性 Trust 驱动。
- 正常构建、project audit、5项新增回归均通过。764项旧输入只有事先允许的 README、
  STATUS、工程注册三项变化；旧源码、证明、测试和冻结证据本体不变。
- 全套2419项测试为427失败、1错误，上一轮427失败、1错误全部保留，未新增或删除失败，
  旧失败相对顺序不变。全仓并未通过。
- make audit 仍因 stale function evidence input identity 失败；git diff --check 的既有六行
  空白问题不变。六门覆盖仍为94/1/1/1/1/0，不因新增证明文件增加覆盖信用。
- cleanup-inventory.json 逐项确认一次性 Trust 驱动／产物及缓存备份；cleanup.json 记录
  清理结果与既有缓存恢复。源码、全部编译失败日志、快照及可复用 Coq 产物保留。
