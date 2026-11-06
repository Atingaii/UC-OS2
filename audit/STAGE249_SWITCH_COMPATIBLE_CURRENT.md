# 第249步：与任务切换兼容的当前优先级候选不变量

## 问题与本步决定

第246步发现：原实际中断 builder 并不保证当前优先级字节与当前任务关联。
第247步进一步排除一种简单修补：如果把这项关联要求在所有切换状态一直成立，
原框架的切换只写当前任务指针、不改该字节，就会破坏加强后的条件。
这不是说所有新不变量都不可能，也不是可达内核漏洞。

本步新增**独立候选** `V293_ready_current_inv`，不替换旧活动 Inv，
不跨 Inv 搬运任何函数 Hoare 结论。核心条件为：

> 原 ready/TCB/storage 资源，与以下条件在同一堆成立：
> 当前字节与当前任务关联，**或者**当前任务已经最高就绪。

第二分支不要求当前字节已随物理指针更新。因此框架切换后，即使字节仍为6、
新任务实际优先级为4，也可通过最高就绪分支关闭候选。
两分支仍受相同原核心资源约束，不是任意内存状态都能满足的析取。

没有改 C/config/AST/framework、原 Inv/LI/BDspec 或精确抽象调度；
没有用 `spec_choice` 的任选规格把问题藏起来。
只复用当前 V2.93.01 工程已有引理，不引入其他操作系统版本的证明。

## 真正证明的接口

生产文件：`certiucos/v293/proofs/V293ReadyCurrentInvariant.v`。

- 稳定接口 `V293_ready_current_good`：完整
  `GoodI V293_ready_current_inv V293_scheduler V293_shared_li`。
  四项都闭合，尤其保留原指针写切换闭包，包含旧任务存在与已删除两种情况，
  后者仍量化任意局部资源释放及其 memory/abstract join。
- `V293_current_core_same_sched`：从新核心及任意分离 frame 抽取当前任务／表，
  用实际字节 load 和 bounded byte 唯一性识别关联中的值。
  当位图选择结果等于该字节时，两分支都推出原 `sched_self V293_scheduler`。
  关联来自新核心，不再是额外外加的当前任务关联纯前提。
- `V293_current_switch_highest`：原核心资源加当前最高就绪事实，可恢复新候选；
  不能在不知道最高就绪或关联时任意升级原 Inv。

`same` 接口仍显式需要 ready_rel、表字段读取、实际当前字节及比较相等事实。
本步没有证明所有 BuildintPre 自动提供这些事实，也没有给出同一新 Inv 下
EOI/Enter/Exit/exint 的完整函数环境。`GoodI` 不等于全部函数保持新不变量。

新增的析取由普通合取与原 payload 共享同一个堆，不重复拥有当前字节。
GoodInvAsrt、precise 和 inv_isr_prop 都实际构造后，才形成框架要求的 Inv。
精确性来自原资源核心的精确性；不是通过把整个核心变成纯命题获得。

## 预先固定的消融及独立 typed 检查

协议在实现前固定于 `audit/logs/stage249-switch-compatible-current/protocol.json`。
独立文件 `audit/probes/V293ReadyCurrentInvariantProbe.v` 不被生产模块导入。
它复用第246/247步固定的 typed ready/TCB/storage 状态，不另造空表模型。

| 单因素变化 | 保持不变 | Coq 检查 | 有界结论 |
| --- | --- | --- | --- |
| 删关联分支，只留最高就绪 | 原 Waiting/current-byte=6、原实际 BCpre | SCleft_required_typed | 该非空 typed 状态满足原 guard，但 Waiting 不是最高就绪；关联分支在 guard 层不可删 |
| 删最高就绪分支，只留关联 | 原指针 store、相同任务表、字节仍6 | SCright_required_typed | 切换后新 SWINVt 非空，但原完整当前关联为假；最高就绪分支不是冗余 |
| 删整个 guard | 只把 `(94,0)` 从6写4，frame、其余地址和抽象状态不变 | SCall_required_typed | 前后均为原 BCpre；坏状态比较相等而当前并非最高就绪，被新 guard 拒绝 |

第一行只声称 guard 层见证：**未证明该 Waiting 入口本身满足新 SWINVt**。
第二行从原 SWINVt 出发，证明真实指针写后的状态满足新 SWINVt；
它不是从新入口出发的整个函数执行或初始化可达性证明。
第三行保留片段及完整内存的 join、实际两次 store、逐地址不变和 load。
它是一个字节的状态对照，不是两次 C 执行；不是来源于可达错误的漏洞宣告。
消融结果不能替代后续函数闭包证明。

`SCsame_from_new_core` 只实例化生产接口检查参数与精确结论，
不当作独立的非空 same 执行见证或第二套语义证明。

## 对抗审查与未完成项

1. 空不变量也能满足部分条件？切换后 typed 新 SWINVt 的非空见证排除全空，
   但不冒称所有入口都非空或可达。
2. 是否暗中要求切换更新优先级字节？没有：见证实际保持6，且关联为假。
3. 是否只有 live 子句成立？完整 GoodI 证明包含 deleted/release 分支。
4. 是否把旧 Hoare 当成新 Inv 下的结论？没有。原 Inv 只用于断言遗忘与资源保持；
   **尚未迁移函数 Hoare 到新候选 Inv**，未宣称可直接替换旧三函数环境。
5. 是否把抽象规格改弱了？仍用原 scheduler/sched_self，不添加任意非调度选项。
6. 是否已解决整核？不是 `WFInt`，不是初始化可达，不是 `GOOD_OS`；
   K1–K4 未闭合，uCOS3 未开始，覆盖六门仍应以实际审计为准。

下一步应先在新候选下证明真实函数对 guard 的保持与返回资源关闭，再连接
实际中断 builders；还必须处理 quiet 与 changed/same 的统一抽象规格。
若某条真实路径不能保持，必须保留反例并重新评估候选，不修改旧证据制造通过。
GOOD_OS 和同程序 K1–K4 全部完成之后，才进入老师要求的 uCOS3 阶段。

## 复现与证据

正常工程已注册新生产模块。完整构建命令：

```sh
make build COQBIN=/data/home/lucentzhou/.opam/default/bin/ JOBS=2
```

本步目录 `audit/logs/stage249-switch-compatible-current/` 保留所有编译失败
和源码快照，最终编译由 `stable-compiles.json` 指定。
`trust.json` 对全部新根执行 Print Assumptions 和递归 coqchk；
`source-identity.json` 只复核固定 C 源码输入，不冒称重新运行预处理。
`verification.json`、`test-delta.json` 和原始日志记录实际结果。
结构测试只保护接口与证据身份，不替代 Coq 语义检查。

全仓原来已有失败：第248步完整2404项测试为425失败、1错误，
其中两项为第246/247步冻结 `_CoqProject` 身份的失败；更早基线是旧423失败、1错误。
本步继续注册新模块，旧第248步测试也可能因固定工程尾部断言失败。
不删旧测试、不改冻结 hash、不绕过早退门槛；新增失败与旧失败分别列出。
make audit 的 stale function evidence input identity 与旧六行空白问题也需如实保留。

本步只形成局部检查点，未提交／推送，不声称全仓通过。

## 本轮实测

- 18项生产根、9项独立检查根，共27项，Print Assumptions 与递归 coqchk 均通过。
  仅使用既有 classic / functional_extensionality_dep，未增加逻辑假设。
  递归检查期间全部722份 Coq 源输入 hash 保持，其中包含本步一次性 Trust 驱动。
- 正常构建、project audit 和5项新增测试通过。旧756项源输入中只有协议允许的
  README、STATUS 和工程注册发生变化；旧 Coq 定理、测试及冻结证据未改。
- 完整2409项测试为426失败、1错误；上一轮425失败和1错误全部保留，
  旧失败相对顺序不变，未通过删除失败或改门槛制造通过。
- 新增一项为 `test_interrupt_quiet_builder` 的工程身份检查：实际停在
  `project.endswith(PROD)`，因为新生产模块已追加注册；没有绕过断言重跑，
  不声称其早退后的断言本轮执行通过。原始详情见 new-failure-details.log。
- make audit 仍在 stale function evidence input identity 失败，
  git diff --check 的旧六行空白失败原样保留。六门仍为94/1/1/1/1/0。
- 清理前逐项确认本轮一次性 Trust 驱动／产物及缓存备份；恢复既有缓存原字节，
  保留新源文件、所有失败快照和可复用 Coq 编译产物。具体清单见 cleanup.json。

这是候选不变量的局部通过，不是全仓或整核通过；函数迁移与最终目标仍待继续。
