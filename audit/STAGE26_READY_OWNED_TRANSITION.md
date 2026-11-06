# Stage26：就绪成功路径与共享抽象任务表的所有权连接

## 身份与范围

唯一目标仍为固定 uC/OS-II V2.93.01，加上既定两类授权修复。未改变 C、配置、分析端口、框架、正式函数证据或覆盖。

`V293CriticalReturn.v` 原 4586 行 / 302,952 字节逐字节保留，追加 263 行至 4849 行 / 316,712 字节；SHA256 `419f807645f73200f9a9959e6ce09a65eb10cfe5a7ce7efd51662469e79db71d`。仍为 166 个活动 Coq 源，新增 probe 不进入活动工程。HEAD 保持既有提交；本轮未提交、未推送。

入口基线、前瞻协议、完整追加快照、探索失败和实际工具日志位于 `audit/logs/stage26-ready-owned-transition/`；不覆盖此前历史证据。

## 新的实际结果

- `V293_ready_prio_step` 是有界 ready 情形的局部抽象原语；要求旧任务表真实成员、新优先级空闲，只更新该任务优先级和抽象任务表槽，返回零。不是完整 API 规格。
- `V293_ready_prio_owned_step` 从实际持有的 `V293_shared_fields ... ** R` 取任务表，证明任务域 / 当前任务保持，实际构造框架 `spec_prim_step`；任意 `Of` 从 `join O Of OO` 保留到 `join O' Of OO'`。不以抽象执行成功作前提。
- `V293_ready_prio_branch_relations` 从入口 bitmap / task / priority-table 关系及 ready 成员导出真实 ready 测试为真，再推导两种出口关系对应同一个 `set tasks next ...`。不接受出口关系或分支真值 oracle。
- `V293_critical_ready_owned_success` 将 NULL 事件完整成功具体见证、实际所有权原语及两种关系接到一个最终 `Mf`。TCB 五字段、ready=80/0、表槽 8→NULL / 6→同一任务、NULL 事件指针、全部局部释放、返回零及 caller 恢复与所有权断言同时成立。最高就绪任务仍是另一个优先级 4 任务。
- `V293_ready_prio_stale_bitmap_rejected` 与 `V293_ready_prio_moving_not_highest` 是实际证明的否定命题：出口保留旧抽象表不满足位图关系；把刚修改成优先级 6 的任务当最高就绪任务也不成立。不是仅凭编译拒绝推出不可证。

固定 `V293ReadyOwnedProbe.v` 独立保存字面局部原语、出口关系及旧固定程序 AST 的约束；它不由门禁运行时生成。`expected_owned_nonvacuity` 用既有抽象 fixture 构造所有权入口并消掉空外部帧前提。probe 不是第二份独立证明。

## 对抗性复核与边界

| 可信质疑 | 实际处理 |
| --- | --- |
| 任务表只是随便挑的数学见证？ | 原语从持有的 `abstcblsid` 获取，出口所有权明确包含同一更新后的表；外部抽象帧保留。 |
| 新优先级可能被另一个任务占用？ | 原语显式要求全部状态 / 消息下新优先级空闲；具体连接从入口任务表关系和 NULL 新槽推导该条件。 |
| 位图分支被预先假定为真？ | 从入口 ready 成员和 bitmap 关系推导实际测试，不增加真值或出口 oracle。 |
| 改优先级后就应切换到被修改任务？ | 正反两方面机器检查：优先级 4 是最高，优先级 6 的移动任务不是最高。仍未实际执行无锁切换。 |
| 已恢复整个共享不变量？ | 否。出口只给 `shared_fields ** Atrue`；`Atrue` 不约束其余具体堆。没有 `V293_ready_inv`、TCB / 事件全体关系或初始化可达性结论。 |
| 已证明完整 API 精化？ | 否。只是一次固定 NULL 成功具体轨迹与局部抽象原语的配对；无前向模拟、线性化点、并发交错或完整 API 规格环境绑定。空原语参数列表不替代真实 API 参数 / SELF / 错误处理。 |
| 已有完整物理表与抽象任务双射？ | 否。复用的 `V293_priority_table` 只要求每个抽象任务对应正确槽，不额外声称所有指针槽都对应已分配且全字段合法的 TCB。 |
| 早期负控拒绝证明下游都有效？ | 否。每个负控只记首次拒绝，全部 `downstream_credit=false`；两个语义反例另行证明，不能混淆信用。 |
| 当前 C 已完成正常切换？ | 否。具体见证仍运行 1 / ISR 1 / 锁 0，真实调用只走受阻分支；准确缓存、源码切换对应仍开放。 |

## 机器检查

<!-- ready-owned-actual-results-start -->
| 检查 | 实际结果 |
| --- | --- |
| 新所有权门禁 `gate01/result.json` | 15 项通过，177 项输入保持，临时树已清理 |
| 当前 4849 行身份的旧入口门禁 `replayed-entry/gate02/result.json` | 13 项实际重放通过，175 项输入保持 |
| 当前身份的旧完整返回门禁 `replayed-entry/complete-return-replay/gate02/result.json` | 17 项实际重放通过，173 项输入保持 |
| 新局部测试 / 包含既有测试的相关集合 | 14 / 91 项通过，不把两组相加计算 |
| 完整测试 | 841 项，263 失败、1 错误；相较前轮 827 项，264 个 FAIL/ERROR 标签按重数完全相同，无新增或删除 |
| 范围审计 / 冻结只读核对 / 增量 `make build` / `git diff --check` | 通过；增量构建无需重编，不能替代 source-only 全量干净构建 |
| 默认 `make audit` | 退出 2，拒绝 `stale function evidence input identity`；原正式证据不覆写，六门仍 94/1/1/1/1/0 |

上述三组门禁都有实际 coqc、coqchk、冻结前缀正控及负控，不是仅更新期望 SHA。工作树编译检查按顺序运行，重叠部分仅使用各自独立的临时 namespace，见 `replay-workspace-order.json`。不授当前身份全部旧函数门禁重放或 source-only 干净构建信用。

新固定 probe 的四根和五根完整 / 单根正控实际 `Print Assumptions` 的并集仅 `Classical_Prop.classic` 与 `FunctionalExtensionality.functional_extensionality_dep`；分支正控仅前者。两个旧门禁的 probe 与各正控仍仅上述两项。

新三个单因素负控保留目标完整 Proof：NoAbstractWrite 在第 100 行 Proof 后，第 114 行出口 identity 首次拒绝；ReadyNotUpdated / TableNotUpdated 在第 215 行 Proof 后，第 254 行分别拒绝 FinalBitmap / FinalTable。均只授固定 Proof 的后置敏感性，`downstream_credit=false`；不授 C 修改或命题不可证信用。两个语义否定命题另有内核检查，不能与编译拒绝混算。

旧入口三负控实际在 88/88/89 行 Proof 后的 266/268/278 行拒绝 Exec / Removed / EventReady；旧完整返回六负控实际在 138/141/146/151/151/348 行首次拒绝。后者前五项保持完整 Proof，第六项只中和第二次 store 的权限传递，不冒称删除 C store 或 Proof 完全不变。均不授下游信用。详见本轮三个 `*negative-first-rejection-review.json`。

两个旧测试文件只重绑到这些真实重放结果，48 / 31 个 assertion AST 保持；历史输入快照逐字复制，旧日志不覆写。见 `test-evidence-binding-protocol.json`。旧入口报告的 `ready and event rows=0/1` 是行索引，不是数值：ready 16/1→80/0，非空事件 0/1→64/0；单独澄清，不改原始报告。

完整失败标签比较见 `full-test-comparison.json`；每条验证命令及退出码见 `verification-commands.json`。所有结果仅适用于上文边界，未晋级正式覆盖。
<!-- ready-owned-actual-results-end -->

## 失败历史与清理

隔离开发第 01 次早于生产前缀编译完成，导入路径未就绪；第 02–12、14–16、18–19、21 次涉及显式导入、map existential rewriting、断言重排、战术语法或见证实例化错误，原始日志和源码快照保留。第 01 次 shell 最后 `cat` 日志导致 shell 退出零，Coq 实际报错，**不授通过信用**。第 13 / 17 / 20 次仅其当时版本通过，不冒称最终强化版本；第 22 次通过包含新优先级空闲要求的最终开发版本。生产与规范门禁另行检查。

逐项核对路径、类别、大小与 SHA 后，删除本轮 26 个一次性文件，共 6,453,467 字节：工作树新 Coq 缓存 20 个 / 6,243,834 字节，隔离开发树 6 个 / 209,633 字节。完整开发源已保留文本快照。三个门禁自动清理的临时树另列清单并确认已消失，不重复计入 26 个。基线 903 个既有缓存路径全部保留，不声称缓存字节完全不变。源码、固定 probe、测试、文档、正式及历史证据、成功 / 失败日志、开发快照、依赖与用户数据保留。见 `cleanup-result.json`、`workspace-cleanup-manifest.json`、`development-cleanup-result.json` 和 `gate-temporary-cleanup-review.json`。

## 下一步

把一般成功入口的具体资源与实际所有权组合，不再局限固定 NULL 见证；补非 ready / 事件关系、真正共享不变量与正常无锁调度，再连接完整函数环境、入口分配、ISR/API 保持和初始化。`GOOD_OS`、同程序 K1–K4 未完成，uC/OS-III 未启动。中文入门见[物理位图与共享表](../docs/开发中/把物理就绪位图连接到共享任务表.md)。
