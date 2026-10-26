

你当前位于一个已经完成干净重构的 Coq 验证项目：

`CertiUCOS-II-V29301-Coq818`

这是一个新的验证项目。此前的 V2.52 证明已经由我另外保存，本项目不再验证 V2.52，也不要恢复、复制、机械迁移或重新引入任何 V2.52-specific 的代码、模型、证明、audit root 或历史 proof tree。

你的任务是继续完成 **uC/OS-II V2.93.01 的源码级功能正确性和 safety 性质形式化验证**。

请首先完整阅读并严格遵守：

* `AGENTS.md`

* `PROJECT_SCOPE.md`

* `ROADMAP.md`

* `VERIFICATION_STATUS.md`

* `KNOWN_BUGS.md`

* `TRUSTED_BASE.md`

* `README.md`

* `csrc/UPSTREAM.lock.json`

* `csrc/config/v29301-profile.json`

* `csrc/repairs/REPAIR_TARGET.json`

其中 `AGENTS.md` 和 `PROJECT_SCOPE.md` 是约束性文件。如果其他文档与它们冲突，以这两个文件及我本提示词为准。
一、唯一验证目标

--------

唯一 active kernel target 是官方：

uC/OS-II V2.93.01

固定 upstream commit：

`0c4a48e6fbc6e915714e816196619a5481accf0c`

验证的是一个**固定配置下的 V2.93.01 实例**，不是所有可能的 uC/OS-II 配置组合。

不得扩大配置范围。

尤其不要因为 V2.93.01 支持更多功能，就自动把以下功能加入验证目标：

* Multi-Pend

* timer manager

* event/task/flag/memory names

* task profiling

* task registers

* debug tables

* tick-step support

* application hooks

* TLS 或其他当前固定配置没有启用的功能

只有 `csrc/config/v29301-profile.json` 固定配置实际包含的功能才属于 active verification target。
二、验证目标性质

--------

本项目验证：

1. 操作系统功能正确性；

2. safety 性质；

3. 最终源码级 `GOOD_OS` 精化/模拟性质；

4. `KNOWN_BUGS.md` 中 K1–K4 四类已知反例在最终目标中的机器可检查排除。

本项目不验证与当前目标无关的其他性质家族。

不要引入 cybersecurity/security verification 目标。

不要进入：

* compiler correctness；

* assembler/linker correctness；

* ABI correctness；

* final binary correctness；

* concrete hardware correctness；

* 真实 x86 执行级证明。

我接受现有框架的 task-switch / interrupt abstraction 作为 trusted boundary。

这些更底层工作不得阻塞源码级 `GOOD_OS`。
三、四类已知反例的处理方式

-------------

### K1 — timeout / suspend / resume

V2.93.01 已经原生使用独立的 `OSTCBStatPend`。

这不是本项目 patch。

你需要直接从固定的 V2.93.01 upstream C 源码建立模型并证明：

* timeout 正确清除 event-wait 状态；

* timeout 结果通过 pend-result 状态保存；

* timeout 后再 Suspend/Resume 不会使任务丢失 ready 资格；

* API continuation 最终能够观察 timeout 结果。

禁止重新引入 V2.52 的 backport/repair 结构。

### K2 — mutex deletion / ready table / priority table

V2.93.01 已经修复历史单 mutex 场景中的原始 NULL 调度路径。

这也不是本项目 patch。

必须从 V2.93.01 upstream 源码证明相应 coherence：

`ready priority -> corresponding valid TCB`

以及相关 TCB/priority-table/ready-table 一致性。

### K3 — nested mutex stale priority restoration

这是 V2.93.01 中仍需修复的问题。

当前授权的 repair 原则是：

* 不把某个已经失效的中间 inherited priority 当作延迟恢复目标；

* task 的 effective priority 必须根据：

  * task base priority；

  * 该 task 当前仍然持有的 mutex 对 priority 的贡献
    重新计算；

* 不能因为恢复旧 priority 覆盖另一个 live task 的 `OSTCBPrioTbl` 项；

* active task priority 必须保持唯一。

这项 repair 可以修改固定 upstream V2.93.01，但必须：

* 是最小修改；

* 明确记录 patch；

* 有 stock V2.93.01 反例；

* 有 repaired C regression；

* 有对应 Coq model/spec/proof；

* 最终进入同一个 `V293_low_level_os_code`。

### K4 — scheduler-locked self-delete

这是 V2.93.01 中仍需修复的问题。

目标行为是：

如果**当前真正正在执行的任务**在进入 `OSTaskDel` 前已经持有 scheduler lock，则必须在任何破坏性删除操作之前拒绝该删除。

不得：

* 清 ready state；

* 从 task list 摘除；

* 释放 mutex/resource；

* 把当前 TCB 放回 free list；

* 使该 TCB 可被另一任务复用。

优先使用 V2.93.01 已有的合适错误码，不要无必要增加新 API/error code。

修复后必须证明至少：

当前 CPU execution context 所依赖的 TCB，在执行上下文真正离开以前始终 allocated，不能进入 reusable/free 状态。
四、首先执行 Gate 0 / Gate 1 验收

-------------------------

不要一开始就大量写 Coq lemma。

先执行并记录：
    git status --short --branch
    git log --oneline --decorate -n 10
    git tag --list
    make audit
    make fetch-source
    make source-audit
    make config-audit
    make build

如果命令名称或依赖关系需要根据 Makefile 调整，可以调整执行顺序，但不能跳过相同的验收内容。

确认：

1. upstream checkout 的 commit 精确等于固定 commit；

2. `csrc/UPSTREAM.lock.json` 中所有固定文件 hash 全部匹配；

3. effective `os_cfg.h` 来自固定 profile；

4. 不存在用其他 uC/OS-II release 文件替代 V2.93.01 文件的情况；

5. 当前 clean foundation 在 Coq 8.18 环境可构建；

6. `certiucos/v293` 中没有 `Admitted/admit`；

7. 没有新增未经审查的 `Axiom`、`Parameter`、`Conjecture`；

8. 不存在 V2.52-specific active proof dependency。

如果 clean foundation 本身存在实际错误，先修复 foundation，再继续。
五、Gate 1：重新生成真实源码范围

-------------------

在开始大规模 Coq 建模之前，必须从**固定配置实际预处理后的 V2.93.01 源码**重新建立 source inventory。

不要沿用 V2.52 的“96/99 个函数”数字。

必须机器生成并记录当前 V2.93.01 固定配置下：

* public/API C bodies；

* portable internal C bodies；

* CPU hooks；

* assembly/task-switch boundary entries；

* 被条件编译实际移除的函数；

* 每个 active body 的源码文件；

* locator；

* signature；

* relevant preprocessor guards；

* SHA-256 或等价固定身份。

建立一个 machine-readable coverage manifest。

每个配置后函数恰好对应一行。

覆盖状态至少必须包括：

`located`
→ `modeled`
→ `specified`
→ `local_hoare`
→ `component_linked`
→ `full_target_linked`

在 inventory 没有冻结以前，不得声称完整函数数量。
六、Gate 1：先冻结 repaired C target

------------------------------

在大规模证明开始前，优先完成 K3 和 K4 的 C-level target freeze。

要求：

1. 保留一份不可修改的 stock V2.93.01 source identity；

2. 两个 repair 分开记录；

3. repair 必须是最小 diff；

4. 不顺便重构 upstream C；

5. 不顺便修复没有经过机器反例确认的问题；

6. 不改变未授权 API 行为；

7. 每个 repair 建立 stock/repaired 对照 fixture。

K1、K2 应作为 upstream regression tests。

K3、K4 应同时具有：

* stock V2.93.01 counterexample；

* repaired V2.93.01 successful regression。

最后生成 immutable repaired-source manifest/hash。

一旦 Gate 1 repaired target 冻结，在没有发现新的、可复现的 functional/safety counterexample 且没有得到我的明确许可之前，不再修改 C 目标。

如果发现新的疑似 bug：

先做最小实际 C reproducer 和源码分析。

只有能够给出明确 functional/safety 错误时，才停下来让我决定是否扩大 repair scope。

不要因为 Coq invariant 难证就修改 C。
七、Gate 2：建立 V2.93 专用状态和全局 invariant

-----------------------------------

只在 `certiucos/v293/` 中建立 active OS-specific development。

不要复制整个旧 proof tree。

优先建立最小但足够支持最终 `GOOD_OS` 的 V2.93-specific：

* TCB concrete representation；

* task abstract state；

* ready table；

* priority table；

* event objects；

* semaphore；

* mailbox；

* queue；

* mutex；

* flags；

* memory partitions；

* timeout / pend-result；

* scheduler/core state；

* initialization state。

全局 invariant 至少必须能推出：

1. ready-table / priority-table / TCB coherence；

2. live task priority uniqueness；

3. timeout / wait / pend-result consistency；

4. mutex base/effective priority consistency；

5. mutex owner identity consistency；

6. 当前 executing context 对应的 TCB 一定 allocated；

7. 当前 executing TCB 不在 free/reusable pool；

8. K1–K4 对应错误状态不可达。

不要为了覆盖未来可能需要的功能而过度设计状态。
八、尽早建立顶层 proof spine

--------------------

不要等所有函数做完以后才开始 program integration。

尽早建立并逐步冻结：
    V293_low_level_os_code
    V293_os_spec
    V293_ucos_init

以及最终目标 theorem 的 skeleton，例如：
    Theorem V293_ucos_correct :
      GOOD_OS
        V293_low_level_os_code
        V293_os_spec
        V293_ucos_init.

在前期允许这个 theorem 仍依赖明确列出的未完成 function obligations，但不得使用 proof holes。

目的不是提前假装完成，而是让每个函数证明从一开始就知道最终进入哪一个 top-level dependency closure。
九、Gate 3：以后以“纵向完成一个函数”为主

------------------------

禁止再次采用：

“为某一局部状态不断生成大量 proof 文件，但函数 Hoare 和 top-level linkage 长期不增长”

这种推进模式。

对每个函数，原则上按：
    exact configured C body
    → CoqImp AST/model
    → specification
    → local Hoare/source simulation
    → stable facade theorem
    → component linkage
    → V293 program linkage

完成一条纵向切片。

一个函数内部可以有必要的辅助 lemma，但向上只暴露稳定 facade theorem。

顶层模块不要直接依赖大量内部小 lemma。

每完成一个函数，立即更新 machine-readable coverage manifest。

以后项目完成度只按 configured function coverage 和 top-level linkage 衡量。

“新增了多少 lemma / proof root / .v 文件”只能作为审计信息，不能作为完成比例。
十、严格控制文件增长

----------

本项目已经从旧工程的大量 proof-island 模式重新清零。

因此：

* 不要一个小 lemma 创建一个 `.v`；

* 能合理放在同一逻辑模块中的证明放在一起；

* 每个 source function 尽量有一个稳定 facade module；

* common invariant lemma 集中管理；

* 不要为了“方便”复制已有 theorem；

* 不要产生同一性质多个几乎等价版本；

* 定期检查未被 active dependency closure 消费的 proof modules。

如果某批新增证明的 coverage delta 长期是：

`0 located / 0 modeled / 0 specified / 0 local Hoare / 0 linked`

则必须说明它解除的是哪个明确 blocker；否则停止横向扩张，回到纵向函数集成。
十一、注释中的 API 前置条件

----------------

可以使用 V2.93.01 官方源码注释中**明确写出的 API 使用约束**，但必须：

* 精确记录来源；

* 区分编译时条件、runtime check 和 documented precondition；

* 不得为了排除已经能够合法复现的 counterexample 而事后发明新的前置条件；

* 如果某个性质只对满足 documented client discipline 的客户端成立，定理中要明确表达这一点。

十二、Git 工作方式
-----------

你被授权在本地仓库中：

* `git add`

* `git commit`

* 创建本地 tag

不需要每个 commit 都征求我同意。

但：

* 不要 `git push`；

* 不要 force push；

* 不要 destructive reset；

* 不要 `git clean -fd`；

* 不要通过删除未解决证明来让 build 通过；

* 不要 amend 已经作为 milestone 封存的历史。

建议在每个 Gate 或重要纵向 slice 完成后形成 buildable checkpoint。

commit message 必须说明：

* 对应 source target；

* coverage delta；

* 是否改变 repair；

* 对 K1–K4 有何影响。

十三、什么时候需要停下来让我决断
----------------

除以下情况外，不要因为普通证明困难、编译错误、需要补 lemma、需要整理 invariant 等原因中途停下来问我。

只有在出现下列情况时需要我作决定：

1. 发现一个新的、经过实际 C reproducer 支持的 functional/safety bug，需要修改当前 frozen target；

2. 必须改变已有 API 对外可观察行为，而当前 scope 没有授权；

3. 必须扩大固定配置或加入原本关闭的功能；

4. 必须改变 trusted boundary；

5. 发现 V2.93.01 官方源码/许可证/来源身份无法可靠固定；

6. 最终规范存在两个明显不同且无法从源码和官方注释决定的合理语义，需要我选择。

除此之外，请自行推进。

不要频繁给我“是否继续”的问题。

如果没有决策点，就继续完成下一项最能提高真实 coverage 或 top-level linkage 的工作。
十四、每个阶段的验收纪律

------------

重要 checkpoint 至少检查：
    targeted Coq compilation
    full Coq build
    static proof-hole scan
    forbidden proof escape scan
    Print Assumptions for important roots
    coqchk for the relevant closure
    source/hash audit
    coverage audit
    git diff --check
    git status

最终 Gate 5 必须：

* Coq 8.18.0 clean full build；

* complete configured function inventory；

* every active function full-target-linked；

* `V293_low_level_os_code` 完整；

* `V293_os_spec` 完整；

* `V293_ucos_init` 完整；

* `V293_ucos_correct : GOOD_OS ...` kernel checked；

* K1–K4 regression theorems与同一个 repaired program 连接；

* final `Print Assumptions`；

* final `coqchk`；

* 0 active proof holes；

* 0 unreviewed new axioms；

* clean Git worktree；

* immutable final tag。

十五、现在开始
-------

现在不要只给我计划。

请直接开始执行。

第一步：

1. 阅读上述项目文档；

2. 审计当前 Git 和 clean retarget baseline；

3. 执行 `make audit`；

4. 获取并 hash 验证固定 V2.93.01 upstream；

5. 生成并验证固定配置；

6. 在当前环境完成 baseline Coq build；

7. 重新生成 configured source inventory；

8. 建立 Gate 1 machine-readable coverage；

9. 实际复现/核对 K1–K4；

10. 完成并冻结 K3/K4 两项最小 C repair；

11. 建立 repaired-source manifest；

12. 然后进入 V2.93 common state/invariant 和纵向函数证明。

如果执行过程中没有出现上面规定的真正决策点，不要停在“下一步应该做什么”的报告上，直接继续推进下一项工作。

每次阶段性报告请优先报告：

* 当前 frozen target commit / repaired source hash；

* configured function 总数；

* coverage 六阶段数字；

* full-target-linked 数量；

* 当前 top-level theorem 状态；

* K1–K4 状态；

* assumptions/coqchk/build 状态；

* Git checkpoint；

* 真正的 blocker。

不要用 lemma 数量或 `.v` 文件数量代替完成度。

这份提示词和新项目的 `AGENTS.md / ROADMAP.md` 是配套的。**最重要的是一定用新会话，不要 `codex resume` 以前的 V2.52 会话**；否则旧会话的上下文很可能重新把它带回 V2.52 的证明路线。

另外，第一次 Codex 回报时，我建议你重点看它是否真的完成了 **Gate 1 的“configured function inventory + repaired source freeze”**。在这两个数字/哈希都没有固定前，如果它又开始连续新增几百个 Coq lemma，就应该立即纠正方向。
