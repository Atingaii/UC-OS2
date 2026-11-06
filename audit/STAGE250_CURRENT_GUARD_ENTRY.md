# 第250步：新不变量接通实际中断入口与 OSIntEnter

## 前因后果

第246步证明旧入口缺少当前任务／优先级关联；第247步证明不能简单要求该关联
在所有切换状态一直成立。第249步的独立候选允许“当前字节关联，或当前任务最高就绪”，
已满足完整 GoodI，但当时尚未连接函数证明，也未证明 Waiting 实际入口非空。

本步只做下一条必要连接：在同一新 Inv 下，从真实 BuildintPre 直接走过
EOI → OSIntEnter。没有改固定 C/config/AST/framework，也没有替换旧 Inv/LI/BDspec。

## 稳定接口与证明路径

生产文件：`certiucos/v293/proofs/V293InterruptCurrentEntry.v`。

稳定接口 `V293_interrupt_current_entry` 量化向量、原 ISR、栈、任务及抽象操作，
要求实际 builder 等式、Enter 函数规格查找和合法向量编号；不额外要求 guard、
当前任务关联、强 snapshot、nest<255 或其它 ISR 位全清。

1. `V293_irq_current_builder_open` 从新 builder 打开不变量，分离 running/nesting/lock
   三个控制字节。当前优先级字节、TCB/ready 资源和 guard 留在 kept 资源中。
2. `V293_current_guard_separate` 用拥有者子堆的实际 byte load 与完整堆 load 一致性，
   将同堆 guard 限制回该拥有者子堆。这里使用普通合取 `//\\`，不是将 guard 与原资源
   再作分离合取；没有重复占用当前字节。
3. EOI 使用实际 `eoi_ieoff_rule`，保留原 ISR 的更新表达式；没有假设其它位全清。
4. OSIntEnter 调用复用原 `forall I` 证明，直接实例化当前新 Inv；kept 是合法 caller
   frame，不是额外前提。不是把旧 Inv 下的 Hoare 结论无证搬到新 Inv。
5. 后置条件保留 kept、地址绑定和 `V293_interrupt_nest_after` 的实际计数分支；
   不声称计数在 Enter 后不变，也没有承诺 Exit 返回。

`V293_irq_current_good` 是同一新候选与 bound LI 的完整 GoodI。
`V293_irq_current_enter_environment` 给真实单函数 Enter_unit 的 WFFunEnv / WFIFun。
这不是包含 Exit/Sched 的三函数环境。

`V293_irq_current_builder_enrich` 仅是非空见证的构造辅助：它确实需要额外 guard，
不能拿它冒充无前提的入口执行定理。无额外 guard 前提的是上面的稳定执行接口。
`V293_irq_current_builder_guard` 则从新入口自动抽取完整堆 guard，供负对照使用。

## typed 非空与单因素消融

独立文件 `audit/probes/V293InterruptCurrentEntryProbe.v` 不被生产模块导入。
沿用旧 typed 内存、全内存、abstract map 和分离 frame，不改旧反例。
新 CEinv 的 storage 包含 running/nesting/lock；不冒用第249步较短的 PPcells。

| 检查 | Coq 定理 | 确切结论 |
| --- | --- | --- |
| 实际新 builder | CEbuilder | CEpre 就是相同向量与抽象操作的 BuildintPre |
| Waiting 入口非空 | CEtyped_entry_nonempty | 同一 typed 状态同时满足旧 BCpre 与新 CEpre，Waiting 并非最高就绪 |
| 固定堆单字节对照 | CEtyped_single_byte | 只把地址94的当前优先级6写4，旧入口前后都接受，新入口只接受修改前 |
| frame/其它地址 | CEtyped_single_byte | 局部及全内存 store、join、同一 frame、其它地址不变均被检查 |
| 真入口执行 | CEactual_entry | 在相同 CEinv/LDli/CEspec 下走真实 EOI/Enter |
| 同一候选环境 | CEgood_and_enter_environment | 同一 CEinv 的 GoodI 和真实 Enter 函数环境成立 |

这不是初始化可达证明，也不是两次 C 执行，更不是发现可达内核漏洞。
负对照只隔离当前字节条件；不能以这项拒绝推断 Exit、调度或所有 API 都保持新 Inv。

## 验证与边界

预先协议：`audit/logs/stage250-current-guard-entry/protocol.json`。
最终编译见 stable-compiles.json；全部失败和快照保留。
trust.json 对所有新证明根执行 Print Assumptions 和递归 coqchk，
结构回归仅保护接口与身份，不替代语义检查。
source-identity.json 仅复核既有固定输入，未重跑预处理。

不是 `WFInt`，不是 `GOOD_OS`。Exit/Sched 的函数证明和完整返回尚未迁移，
所有 API 保持、初始化、同程序 K1–K4 仍待闭合，uCOS3 未开始。
全仓原有失败与工程追加注册导致的新身份失败必须分别记录，不能改旧测试或冻结证据。
未提交／推送。下一步优先在同一新 Inv 下连接 Exit/Sched，而不是再增加独立不变量。

## 本轮实测

- 13项生产证明根、7项独立检查根，共20项，Print Assumptions 和递归 coqchk 全部通过；
  仅使用既有 classic / functional_extensionality_dep，没有新增逻辑假设。
  信任检查期间全部724份 Coq 源输入不变，其中包括一次性 Trust 驱动。
- 正常构建、project audit、5项新增回归通过。760项旧源输入只有事先允许的
  README、STATUS、工程注册三项变化；旧证明、测试、冻结证据及旧 manifest 本体未改。
- 完整2414项测试为427失败、1错误；上一轮426失败和1错误全部保留，旧失败相对顺序不变。
  新增一项为第249步冻结工程尾部身份检查，实际停在 `project.endswith(PROD)`；
  没有修改旧测试或绕过该断言，不声称早退后的检查本轮执行通过。
- make audit 仍报 stale function evidence input identity；git diff --check 的旧六行空白问题不变。
  六门覆盖仍为94/1/1/1/1/0，不因本步新增证明文件就增加覆盖数字。
- 一次测试选择器未匹配任何测试的0项运行不计作通过；随后显式结构测试和完整5项新增回归均已执行。
- 按 cleanup-inventory.json 逐项确认一次性 Trust 驱动／产物及缓存备份，恢复既有缓存原字节，
  保留源码、失败日志及可复用 Coq 编译产物；完成结果见 cleanup.json。

这是新的实际入口／Enter 局部通过，不是全仓或整核通过；总目标保持 active。
