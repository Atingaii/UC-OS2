# CertiUCOS-II V2.93.01：下一轮框架证明提示词

你正在 `CertiUCOS-II-V29301-Coq818` **现有仓库根目录**工作。直接执行本轮任务，不要停在计划或建议；每完成一个可核验的证明连接，就继续推进下一项。允许先给出简短进度，再继续工作。

## 目标与当前事实

本轮重点是把已有的**有界内存框架证明**接到实际的程序级模拟，同时保持 V2.93.01 七修复源码的唯一验证目标。不要把一个抽象保持性引理、一条 C 回归，或条件定理 `V293_completion_sound` 称为完成了整核证明。

仓库当前记录的事实应在开始时重新核实：

- 唯一源码基线是官方 uC/OS-II V2.93.01，commit `0c4a48e6fbc6e915714e816196619a5481accf0c`，加 `PROJECT_SCOPE.md` 授权的**七项**修复。活动源码锁为 `csrc/repairs/K5_FROZEN_SOURCE.json`，其中 `source_set_sha256` 为 `04da6841c84df40228d90f09d19dacfdc60debbfb624106f7c3399a2baf6ae5f`。旧五、六修复锁及反例是历史证据，不是当前目标。
- `audit/coverage.json` 记录 95 个配置后的 C 函数体（65 public、30 internal），六阶段统计为 **95 / 2 / 2 / 2 / 2 / 0**。完成组件连接的两个函数是 `OSVersion` 和 `OS_Dummy`。`V293_ucos_correct` **尚未定义，也尚未证明**。
- `framework/proof/memory_bound.v` 已包含 `bounded_GOOD_OS_from_matching`、具体关系 `bounded_program_match`，以及中断、事件、普通任务步进、abort 和**同任务**切换的连接。`audit/foundation-validation.json` 当前枚举 121 项有界事实；最新接续点是 `bounded_switch_ready_partition` 后的**不同任务切换**。这些事实没有关闭所有 `lpstep` 分支。
- 历史框架的 `memory.MemoryNotFull` 与现有允许任意地址映射的内存类型冲突；`audit/MEMORY_MODEL_TRUST.md` 给出了可检查的全占用内存见证。旧 `toptheorem.Soundness`、现有条件接口仍可能依赖它。已有有界事实没有消除整条旧依赖链。经典逻辑、标准函数外延性及其他项目公理也必须分别审计，不能一概称为 `Closed under the global context`。
- K5 回收临界区前移已**获授权、实施并冻结**；`audit/K5_RECLAIM_ATOMIC_REPAIR.md` 是当前记录。不要再次要求这项修复的授权。抽象池模型及 O0/O2 实际 C 回归不等于 `OS_TCBInit`/`OSTaskDel` 的 CoqImp Hoare 证明。

## 首先核验现场

按以下顺序阅读：`AGENTS.md`、`PROJECT_SCOPE.md`、`VERIFICATION_STATUS.md`、`audit/MEMORY_MODEL_TRUST.md` **末尾的最新进度**、`audit/K5_RECLAIM_ATOMIC_REPAIR.md`、`audit/RUNTIME_PROOF_ROLE_AUDIT.md`、`certiucos/v293/proofs/V293Program.v`、`framework/proof/memory_bound.v` 与 `framework/proof/lemmasfortoptheo.v` 中相关证明。查看 `Makefile`、`scripts/check-foundation.py`、`audit/coverage.json` 和七修复锁；需要旧证明思路时，只把 `audit/CertiUCOS-II-V252-Coq818/` 当只读参考，不得复制其 OS 专用模型、证明或旧函数计数到活动树。

`start-prompt.md`、`ROADMAP.md`、`README.md`、`VERIFICATION_STATUS.md` 的部分“六修复”描述已经过期。以**当前 `AGENTS.md`、`PROJECT_SCOPE.md` 和实际七补丁锁**为准；若更新说明文档，保留六修复反例的历史身份，明确七修复为活动目标。

先记录：

```sh
pwd
git status --short --branch
git log --oneline --decorate -n 8
git diff --stat
git diff --check
coqc --version
make audit
make inventory-audit
```

本仓库上传快照含大量**未提交改动**和未跟踪的参考目录、日志、`start-prompt.md` 等。先列明哪些是用户已有工作；在这些改动上增量继续，不要 `git reset`、`git clean`、覆盖日志、重建 Git 仓库或 `git add -A`。不要为了得到“干净”状态删除参考资料。只有发现源码本地缺失时才按现有脚本获取并校验固定 commit；绝不能混用 V2.52 或另一 V2.93 版本的函数体。

## 本轮证明顺序

### 1. 完成具体 `bounded_program_match` 的切换分支

先看 `framework/proof/lemmasfortoptheo.v` 中原程序级切换证明（尤其不同任务存活、离开任务已删除两支；从约 4740 行附近用定理名重新定位），以及 `memory_bound.v` 现有的：

```text
bounded_program_match_switch_high
bounded_program_match_switch_memory
bounded_program_match_switch_other_resume
bounded_switch_self_dormant_tasks
bounded_program_match_switch_self
bounded_switch_ready_partition
```

在**相同的具体关系 `bounded_program_match`**上，先连接不同目标任务仍存活的 `pswitch_step`，再处理离开任务已删除的分支。证明必须保留原 `lpstep` 的全部前提、实际 `OSTCBCur` 写入、资源分区、`INV`/`RDYINV`/`CurLINV`、当前任务与休眠任务的模拟、以及对任意原框架允许的 client/resumption frame 的量化。内存界从真实整内存和 `join` 推导，不能给任意 frame 偷加有界假设。使用已经证明的 `bounded_switch_ready_partition`；不要把旧 `new_part_o`、`part_store_part` 或无条件 `fresh_exist` 重新引入新证明的依赖闭包。

若旧定理只在额外隐含前提下成立，精确给出最小可检查的反例或未满足的原始前提。不得通过让关系为假、增加不可能的初始化条件、丢弃已删除分支，或改变切换语义来关闭证明。

### 2. 完成其余真实低层步进分支

对 `pstkinit_step`、`pstkinitskip_step`、`pstkfree_step`，逐支证明同一 `bounded_program_match` 对真实 `lpstep` 的保持。核对已经完成的 `pint_step`、`pt_step`、同任务切换以及 `lpstepev`/abort 分支，形成一个**覆盖原归纳类型全部构造器**的程序级匹配定理。不要用新的全称“假设每一步都可匹配”替代尚未证明的构造器；报告中逐个列明证据定理。

### 3. 接通有界模拟，并准确界定剩余前提

复用现有 `bounded_ProgSim_coinduction` 与 `bounded_GOOD_OS_from_matching`，把本轮实际证明的具体关系分支连接起来。证明真实的初始化有界性和资源来源，或在确实尚无 V2.93 初始化模型时，留下**明确、可满足、来源清楚**的初始化证明义务；不要构造空初态或 `False` 前提使定理平凡成立。接口若仍依赖未证明的 API、ISR、内部函数规格或初始化，必须将它们逐项显示为开放义务，不得命名成无条件 `V293_ucos_correct`。

单独追踪 `MemoryNotFull`：对新增定理与将来用于最终 `GOOD_OS` 的实际依赖链运行 `Print Assumptions`。本轮要力争使新有界模拟路径不依赖 `MemoryNotFull` 或项目特有的映射外延性公理；若旧 `Soundness` 的其他调用者仍使用该公理，逐点记录路径，不能仅凭新引理“无此公理”便声称整核摆脱该公理。不能假设每个任意 `mem` 都有新鲜块；不能暗中修改 `mem`、`GOOD_OS`、操作语义或最终目标的陈述。如发现必须改变信任边界或语义才能完成，给出精确阻塞和可检查证据，继续完成不依赖该决策的证明。

### 4. 框架连接完成后再推进一个 V2.93 专用纵向切片

若本轮的完整框架步进连接已实际通过检查，按 `audit/V293_DIRECT_CALLGRAPH.json` 的调用依赖、`audit/coverage.json` 的准确源码定位和现有 `OSVersion`/`OS_Dummy` facade 模式，优先推进 `OS_TCBInit` 及其退休链、free-list、IRQ 屏蔽相关的**真实七修复 C 函数体**建模、规格和局部 Hoare 证明。补全全部活动 TCB 与 free-list 互斥，以及 K5 回收段和允许中断点的小步精化；不得把 `V293_pool_safe` 的抽象原子回收直接冒充该 C 证明。如果函数依赖尚缺必要的不变量或直接调用的规格，先建立最小可复用的前置切片并在 coverage 中如实标注，持续推进，不凭借辅助引理提升 `OS_TCBInit` 的状态。

`OSInit`、`OSStart`、`OSIntEnter`、`OSIntExit` 和 `OSTimeTick` 不是普通任务级 `BuildPreA'` 的同一种入口；依照 `audit/RUNTIME_PROOF_ROLE_AUDIT.md` 分别处理引导、ISR 和双上下文。65 个 `public_api` 是 C 可见性分类，不是 `WFAPI` 前置条件已满足的证明。不要为了适配现有条件接口而缩小合法调用域。

## 不变的边界

- 只验证固定配置下 V2.93.01 七修复程序的源码级功能正确性及安全性。保留 `csrc/UPSTREAM.lock.json`、`csrc/config/v29301-profile.json`、七修复补丁/冻结哈希与其反例档案。未经新的可复现反例和用户范围决定，不得再改 C 目标。
- 不引入 OS 专用 V2.52 证明；不扩展 Multi-Pend、timer manager 等禁用配置；不转入编译器、ABI 或硬件正确性。
- 不使用 `Admitted`、`admit`、`Axiom`、`Parameter`、`Conjecture`、`Abort`、`skip_axiom`、不可信 `native_compute` 插桩、绕过证明的 `False_rect`/矛盾假设。不弱化规格、前后条件、关系、不变量、函数域或 K1–K5 目标。普通 `Print Assumptions` 中的标准经典逻辑和函数外延性也必须据实列出，不能假称 Closed。
- `audit/coverage.json` 只有对应**当前冻结 C 源**的精确函数体模型、规格、局部 Hoare、组件连接各步实际机器证明后才可提升；框架引理、抽象 K5 模型和 C 测试都不改变函数覆盖。不能把条件 `V293_completion_sound` 当成已实例化的最终 `GOOD_OS`。
- 选择最小因果修改。不要批量迁移旧模型或为消除警告大范围改写 `framework/`。重要进展以可构建的 Git 小检查点保存，提交时显式列出本轮相关文件，不把历史参考归档或未归属文件顺带纳入提交。若与用户已有改动冲突，先保留现场、作局部兼容处理。

## 每项成果如何验收

先编译改动文件及其直接依赖，再执行仓库提供的聚合检查。大型依赖重编译可能超过 120/240 秒；超时只算**资源或时间限制**，须确认无遗留进程后延长预算继续，不能称为已通过或伪装成证明反例。至少运行并保存实际退出码：

```sh
make build COQBIN=/usr/bin/ COQC='bash coqc-wrapper.sh /usr/bin/coqc' JOBS=1
make foundation-check COQBIN=/usr/bin/ COQC='bash coqc-wrapper.sh /usr/bin/coqc' JOBS=1
make audit
make inventory-audit
git diff --check
```

根据实际 Coq 安装路径调整 `COQBIN`/`COQC`。新增的框架和 V2.93 根定理须分别做 `Print Assumptions`，逐个检查 Coq 输出无 `Error:`；使用 `coqchk` 重检查**包含新根的依赖闭包**。让 `scripts/check-foundation.py` 跟踪新增定理，保留其对 `MemoryNotFull` 和意外项目公理的拒绝逻辑，不放宽允许列表使测试变绿。如确实改动 C 夹具或源码，还需复验相应 O0/O2 回归，包括 `make k5-regressions`；历史 `make k5-reclaim-counterexample` 成功只表示复现六修复缺陷，不是七修复验收。

持续更新 `audit/FRAMEWORK_WORKLOG.md`，写明每个新定理的陈述、调用的旧引理、与真实操作语义的连接、完整命令和退出码。结束时交付 `FRAMEWORK_PHASE_REPORT.md`，明确：

1. 状态 `PASS` 或 `BLOCKED/IN_PROGRESS`；哪些 `lpstep` 构造器与 `lpstepev`、abort 真正连接；
2. 有界初态和程序级 `GOOD_OS` 桥的**准确开放前提**；旧 `Soundness` 与新增路径各自的公理闭包，特别是 `MemoryNotFull`；
3. 本轮提升了哪些函数覆盖行，及逐行源码 token 哈希、facade 定理和组件链接证据；未提升的仍保持原状态；
4. 七修复锁与 K1–K5 检查结果、Git 改动/检查点、下一条可直接执行的证明入口。

仅当**全部**真实低层步进分支、事件与 abort 的具体关系保持及有界模拟连接实际编译、`Print Assumptions` 审计、`coqchk`、源码/配置/覆盖审计通过，且开放的 OS 专用义务被准确暴露，才把**本轮框架里程碑**标为 `PASS`。这与 `V293_ucos_correct` 的整核完成状态是两件事；后者只有真正定义、实例化全部 95 个配置函数及边界、完成初始化并通过独立审计才能标为完成。

现在先简短说明核验所得的工作树和目标锁状态，接着从不同任务切换分支开始实际证明；不要在给出计划后停止等待确认。
