# 第193步：原 OSIntExit 的统一内部函数规格

## 本步消除的缺口

第192步已经接通原完整 body 和真实函数构造器，但外部 fpre/fpost 仍分别捕获一次调用的 running、快照和任务。`WFFunEnv` 要求在同一份函数规格下，对所有运行时参数、逻辑列表和调用任务证明实际构造器对应的 body；只分别证明若干标量实例不能直接满足这个量化。

本步生产文件 `certiucos/v293/proofs/V293OSIntExitInternal.v`（189行）的稳定接口为 `V293_OSIntExit_internal_contract`。它使用统一 `V293_exit_internal_fpre/fpost`，在真实 `P f` lookup、`BuildPreI` 和 `BuildRetI` 下，对 `vl/lg/tid/pre/post` 统一量化，并复用第192步已证明的完整原 body。声明中只有结论的一次 `InfRules`，没有把整个 body 或语句三元组作为前提。

这是**统一内部条件契约，不是完整函数环境，更不是 GOOD_OS**。静态布局、`Out`／`Sw` continuation、四项 callee lookup、函数良形与局部不变式条件仍显式存在。

## 最小连接方式

1. 逻辑参数首项编码 running，后续沿用第191步12项动态快照；roundtrip 在原有字节有界条件下成立。C 签名仍为 `void OSIntExit(void)`，没有增加运行时参数。
2. `V293_exit_internal_index` 只解释逻辑输入；解码失败时前后断言为 `Afalse`。解码成功时，前置断言包含动态合法性的 pure 部分以及真实物理资源。
3. `valid` 包括 running／快照字段界限、存在 ready 优先级、bitmap/task 关系和 priority table 关系。它从前置断言抽出，不要求调用方先给出“任意逻辑列表都合法”的全局假设，也不声称任意快照非空。
4. 实际 dnil 声明拒绝非空运行时实参；nil 参数产生原单局部 saved 的 cells 和完整 domain。**fpre 本身忽略 vl，拒绝发生在真实 BuildPreI，不是 fpre 中新增检查。**
5. 对解码成功的入口，用真实 `pure_split_rule` 取得动态约束，调用第192步稳定定理；解码失败用真实分离断言的 false 消去和 `pfalse_rule`。未改框架、语义原语或旧证明。
6. 与第192步按运行分支保护 lookup 的标量接口不同，统一主接口明确要求同一 Spec 的四项固定 lookup；这是为统一函数环境准备的条件接口，不声称减少了端口实现义务。

固定配置后的 `OSIntExit` 重新预处理并逐字节核对，原函数、原 body 和源码身份均保持不变。生产证明不导入 audit 探针；`_CoqProject` 只追加该生产文件，根说明只前插当前摘要。

## 独立物理证据与消融

探针 `audit/probes/V293OSIntExitInternalProbe.v`（225行）复用旧独立字节编码、分离 join 和完整物理堆，不从待测选择器反向生成入口。

| 证据 | 保持不变 | 实际结论 |
| --- | --- | --- |
| `UIbuilders`／`UIchecked` | 同一 UIfp/UIfq/SCspec | 对任意 lg/tid 的真实 builder 等式，以及统一 body 推导 |
| `UIenabled_different`／`UIenabled_same`／`UIdisabled_nested` | 同一规格及静态布局，counter 任意 | current=0、nest=1 的不同优先级；current=12、nest=1 的同优先级；nest=2 的禁调度完整 builder |
| `UInot_running` | 同一规格，run<256 且 run≠1 | 非运行路径仍连接原完整 body；没有更换函数规格 |
| `UIpre_nonempty_all_running` | 独立 RCbigstate 构造，idle 任务、固定其他字段 | 任意有界 run/current/nest、任意 counter／saved 旧值，包括 Vundef，入口非空；各分支不是仅靠空前置得到 |
| `UIrunning_control` | 同一物理堆、快照、任务、counter和名称，只改逻辑 run 1→2 | 两种输入都解码成功；实际 Tint8 load 使错误解释矛盾 |
| `UIcounter_control` | 同一物理堆、running、其他快照字段、任务和名称，只改逻辑 counter 0→1 | 两种输入都解码成功；实际 Tint32 load 使错误解释矛盾 |
| `UIcontrol_inputs_nonempty` | 各替代逻辑输入不变，只提供各自匹配的独立堆 | 两个替代输入也能拥有前置，不是隐藏的恒假规格 |
| `UIrunning_frame` | 构造参数除物理 running 外完全相同 | 16号块以外的所有字节不变；counter 块外保持复用第191步 RCcounter_frame |
| `UIreject_runtime_argument`／`UIreject_bad_logic` | 同一真实 builder／统一 fpre | 非空实参由 dnil 拒绝；nil 逻辑列表为 false 前置。这些仅是输入层控制 |
| `UIno_full_environment` | 同一 BLprogram/SCspec | 实际 WFFunEnv 仍不成立：callee 只有规格没有代码，实际域不相等 |

这里的 SCspec 仍是第192步的**非生产 identity switch 契约**。快照不等于执行 trace，调用规则不等于 callee 实现。物理入口固定 IE=false 和空 fixture LocalInv；current=0 仍复用优先级12的 idle TCB，不声称完整 current-task/TCB 优先级一致性。主定理对任意调用任务的条件量化，不等于已为任意任务建立非空生产状态。两个 load 消融也不能推断其他未测字段或生产 ISR 已正确。

## 验证记录与未通过项

前瞻协议和5项 Python 测试在生产实现前冻结；初始结果为1通过、4个缺材料错误。这不是已经构造出语义错误反例的 TDD。Coq 物理对照随实现建立；15次编译（11次失败、4次成功）的源码快照、日志和退出码全部保留。结构测试不代替语义证明。

稳定编译为 `body07`／`probe08`。生产4根、探针20根共24根逐根打印假设，并对两个入口递归 `coqchk`；检查期间603份 Coq 输入固定。实际使用经典排中律与依赖函数外延性，无 Eqdep；每根清单见 `trust.json`、`assumptions-by-root.json`，不增加公理白名单。

完整测试两轮各2129项，旧423失败、1错误及其有序 ID 原样保留；新增5项通过。第二轮在本说明和根摘要定稿后运行，**不是全库测试通过**。`make build`／项目审计通过；完整审计仍因旧函数证据输入身份过期退出2，空白检查仍报告旧 `inferules.v` 581–586行并退出2。

冻结前保护32757份原有文件，只允许根摘要、追加项目列表和生成依赖清单变化；缓存恢复原字节，仅逐项清理本轮临时信任驱动／备份和一次性生成器。实际命令、清理数量、尝试记录、清单及只读复查见 `audit/logs/stage193-interrupt-uniform-internal/`，以最终 `verification.json` 为准。

## 下一条纵向义务

统一函数规格只补上了 WFFunEnv 需要的调用量化形式，不能绕开其域和 callee body 义务。接下来应建立同一个程序／Spec 的可执行或明确归一化抽象边界闭包，连接已有 scheduler 证明和生产临界／任务切换契约，而不是再把 fixture lookup 称为完整函数环境。分析端口只有声明，不编造端口 C 函数体；如沿用 ADR-0005 的显式宏归一化，必须保留原始调用对象与抽象程序的区别及转换义务。

还需完成任意初始 IE 保存恢复、生产 ISR/LocalInv、初始化／全局环境、全交错模拟和同一程序 K1–K4 排除。当前六阶段覆盖仍为 `94/1/1/1/1/0`，最终源码级 `GOOD_OS` 尚未完成，uCOS3 未启动，总目标保持 active；本步没有提交或推送 Git。
