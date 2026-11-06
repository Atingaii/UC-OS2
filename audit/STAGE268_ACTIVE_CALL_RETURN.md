# 第268步：切出的 OSIntExit 调用在显式切回后真正返回

## 先用任务故事理解

上一步的旧任务 A 调用 OSIntExit、分配自己的局部保存区 bs，然后切换到任务 B。上一步只接通了 B 原有的返回；A 仍停在退出临界区之前。

本步换用一个明确的环境任务 B：B 读取优先级表第6项，将目标指针写为 A，再执行 switch。A 因而继续自己第一次切出时安装的续体，执行 excrit、sret，释放**这一次入口分配的同一个 bs**，恢复原 caller 的空局部环境与临界栈 cs。不是凭空假设 A 已有 pending，也不是用 B 的保存区代替 A 的保存区。

注意：**B 是显式环境 fixture，不是真实调度器**。抽象任务表里的 A（OwnershipWaiting）仍然 blocked；本步没有唤醒它，也没有证明内核会选择它。表项存在不意味着任务 ready。两次切换形成的有限执行，不能推出公平性或“最终必然切回”。

## 最小生产变化

新增 `certiucos/v293/proofs/V293OSIntExitSwitchReturn.v`，只暴露一个稳定接口 `V293_int_exit_switch_resume_return`，并登记 `_CoqProject`。

已有调度返回适配器接受 `kseq (sseq excrit sret) (kcall ...)`；真实 OSIntExit 当前归一化体安装的是 `kseq excrit (kseq sret (kcall ...))`。二者不是可随意替换的同一个构造。本接口使用原 `pswitch_step`，再复用 `V293_int_exit_pending_return`，不改原框架的任何步规则，不改 AST、Inv、LI 或旧证明。

生产前提是切回快照上的指针、任务代码、环境、临界栈、保存区和 current 的空间资源；存储和释放均从这些资源构造，不将成功 store/free 或待证执行当作前提。结论包含真实 switch、有限全局执行、free 成功、四字节删除和其他块的逐字节 frame。该接口**仍要求切回快照资源**，不证明任意环境干扰下资源自动保持，也没有新增 ProgSim 结论。

## 独立实例如何连接

审计实例 `audit/probes/V293ActiveCallReturnProbe.v` 使用同一物理堆链，保留 running/nesting/lock、实际调度和缓存复制，不另造解释器：

`sfexec 114 → 函数查找 → fresh bs 分配 → saved 初始化 → running/encrit → nesting 1→0、lock=0 → OS_SchedNew → 目标更新与比较 → counter 回绕 → cache 6→4 → switch A→B → B 读取 table[6]、只写 target → switch B→A → A 的 excrit → sret/free bs → 原 caller`。

主定理 `ARroundtrip` 只要求 br 和 bs 对相应入口内存新鲜，不要求中间执行或 ProgSim。`ARnonvacuous` 从原内存新鲜块定理构造满足条件的入口。B 在初态已经持有环境代码，**不是**同一固定 C 内核的初始化可达任务；本步初态不同于第267步 FWtasks，不能套用其同入口 ProgSim 结论。

| 证明根 | 可观察结论 |
| --- | --- |
| ARenter / ARto_switch | 原入口查找、分配及完整活跃路径，抵达第一次 switch 前 |
| ARfirst_switch | 真正切换到 B；为 A 安装原两个 kseq 的 pending，保留 bs |
| ARtable / ARcells | 从第一次切换后的同堆资源得到真实 table[6] load 与所需 cell 所有权 |
| ARprepare | B 的真实赋值执行；只更新目标指针，准备切回 |
| ARresume | 用生产适配器接通切回与返回，构造 store/free 并读取最终 current |
| ARroundtrip / ARnonvacuous | 从实际入口分配到同一旧任务返回的有限执行及非空入口 |
| ARstack_control | 同堆、同代码、同 current/target/saved，仅移除保存栈顶的真实双执行 |
| ARendpoint_metadata | 初态并非 pending；中间安装 pending；终态 A 恢复 caller，B 停在其 switch 后 |

终态 A 的 bs 偏移0–3全为 None，current 指针为 A，A 环境为 emp、IE=false、栈为 cs；B 环境仍为空，临界栈仍为 false::ncs。B **没有返回**，其 CPcall 保留。旧 fixture 块98不作为 B 的局部保存区释放，本步不声称所有任务都结束。

## 前瞻消融与审稿检查

实现前已冻结 `protocol.json` 和 SHA，不回写协议。协议原写 scall 入口；实际独立定理从 **sfexec** 开始，覆盖函数查找、分配及后续执行，但不声称新增 scall/client 调用入口证明。这一入口差异在此明确记录，不将其伪报为协议文字完全一致。

`ARstack_control` 先从同样的实际分配入口到达切回前同一个 Mb。正向临界栈为 false::true::ci；对照只删除最上层保存的 false，保留 true::ci，其余代码、环境、ISR、指针和物理堆均不变。两边都实际执行 switch、excrit、sret/free，最终堆 Mf 完全相同，但正向 IE=false、余栈 true::ci，对照 IE=true、余栈 ci，任务辅助状态不等。不是通过早期契约拒绝来替代下游证明；该对照只支持保存栈恢复机制，不支持调度器、唤醒或全局不变式的结论。

其他可信异议及处理：

- 循环前提：主路径无执行/ProgSim/store/free 前提；生产接口仅由切回资源构造。
- pending 来源：元数据根检查入口 sfexec 与中间实际安装，不预设旧任务 pending。
- 堆拼接：相邻执行共享同一个实际堆，不混用独立存在的中间堆。
- current/cache：最终 current 回到 A，但 cache 仍沿用4；不声称缓存恢复到6或完整 Inv 保持。
- 初始化：typed high=88，而配置 lowest=12，且 A 为 blocked；不是完整 Inv 或初始化可达证据。
- 源码边界：沿用 ADR-0005/0010 显式源码级切换抽象；不证明外部 port、ABI、机器码或硬件。

## 核验、来源和状态

源码仍固定 V2.93.01 提交 `0c4a48e6fbc6e915714e816196619a5481accf0c` 加两类已授权修复；原 OSIntExit 位于 `os_core.c:693–736`。本步重查来源文件哈希与行锚点，未重新预处理，未更新函数覆盖证据。

稳定重复编译、逐根 Print Assumptions、递归 coqchk 使用 Coq 8.18；检查期间不改 Coq 输入。新增 Python 回归用于身份、接口及边界核对，不替代内核检查。全量测试记录具体新增/消失的失败和错误 ID；不修改旧测试或历史 manifest 来制造通过。实测统一见 `audit/logs/stage268-active-call-return/verification.json`。

README / VERIFICATION_STATUS 只前插，旧尾部逐字节保留；旧输入除 `_CoqProject` 的单行登记外不改。旧检查点会因生产登记/文档身份变化拒绝当前工作区，原日志及冻结 manifest 保留，不把“预期身份失败”写成通过。失败编译快照也保留。清理仅针对逐项记录路径、字节数、SHA 的本步一次性信任驱动和缓存备份，既有缓存恢复原内容；保留源码、证据及可复用编译产物。

**不是 GOOD_OS，不是 WFInt，不是所有路径 OSIntExit，不是完整中断返回，不是任意 client。K1–K4 未闭合，uCOS3 未开始，未提交／推送。** 本步只补“实际切出的调用在给定切回环境下可正确释放并返回”，不是整核验证完成。

下一步应转向真实内核路径与共享不变式的连接：核对切换规则要求的共享断言和临界区资源开闭，处理 current/cache 瞬态，再证明真实就绪状态变化和调度选择能提供切回资源。必须保留 copy 与 switch 的独立步骤，不能靠删除一致性要求、合并原子步或修改原失败证据制造通过，也不应再用同类环境 fixture 冒充这些义务。总目标仍是先完成 uCOS2 的源码级 GOOD_OS 与同程序 K1–K4，再依老师要求进入 uCOS3。

## 本步实测

- 稳定编译：production-04 / stable-production、probe-12 / stable-probe，分别与交付源码 SHA 一致。
- 根核验：1个生产根、11个独立根，递归 coqchk 通过；758项 Coq 输入在核验期间未改；假设仅既有 classic / functional_extensionality_dep。
- 构建及项目审计通过；新增6项回归通过；全量2506项，431失败、1错误。相对267新增失败2项、新增错误0项；消失失败0项、错误0项；具体ID见 test-delta.json，不改旧测试。
- 两个新增失败分别来自267/266的旧身份断言，日志首先明确指向增量构建重生成的 .Makefile.coq.d；工程登记也有已核对的单行变化，是本步生产登记及其派生依赖造成的冻结身份失配，不是新增证明编译失败。旧429失败/1错误的ID及顺序完整保留。见 failure-analysis.json。
- make audit 仍退出2（旧函数证据输入身份过期）；git diff --check 仍退出2（旧 inferules.v:581–586 空白）。
- 1156项旧输入只有中文入口前插及生产单行登记变化；旧文档尾部精确保留。第267步旧 manifest 的变化逐项保留于 previous-manifest-delta.json；本步不重写它。
- 保留18份编译快照，其中10份非零退出；清理8项本步一次性材料，共710494字节，既有缓存恢复原SHA。源码、失败日志、冻结证据和可复用编译产物保留。
