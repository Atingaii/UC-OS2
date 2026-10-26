已经按你的要求完成了这次**彻底重构**。新的项目不是在原来的大工程上继续删删改改，而是重新建立了一个干净的 V2.93.01 验证仓库。

核心变化是：

* 唯一验证目标固定为官方 **uC/OS-II V2.93.01**，commit `0c4a48e6fbc6e915714e816196619a5481accf0c`。官方源码本身标明 V2.93.01 和 Apache-2.0。

* **所有旧的 OS-specific 证明都没有进入新项目**，包括原来的 `certiucos/v252`、历史 `certiucos/code/spec/proofs` 以及依赖旧 OS 模型的 `tactics/ucostac`。

* 只保留 101 个真正与版本无关的 `framework/` 和通用 tactic Coq 文件。

* 全新的 OS 验证树只有 `certiucos/v293/`，目前放了 6 个基础模型/回归性质文件。

* Coq 文件规模从约 **5,482 个 / 70 万行**压缩到 **107 个 / 11.4 万行**。

* 新项目中扫描结果为 **0 个旧目标标识引用**。

* 也没有引入与本项目无关的 security 性质表述。

* coverage **重新从 0 开始**：不会把任何历史局部 lemma 冒充 V2.93 的完成度。

* V2.93 原生的 `OSTCBStatPend` 和 mutex TCB-pointer owner 判断不再作为“补丁”，而是直接验证官方实现。

* 自定义修复严格限制为两处：**nested mutex priority restoration** 和 **scheduler-locked self-delete**。self-delete 修复使用已有 `OS_ERR_SCHED_LOCKED = 50`，不增加新错误码。V2.93 本身已有该错误码。

* 新仓库是**全新的 Git 历史**，没有继承旧工程 commits。当前 commit 是 `deed527`，tag 为 `v29301-clean-retarget`，工作树 clean。

源码也采用了更干净的方式：`csrc/UPSTREAM.lock.json` 固定 V2.93.01 commit 和全部 15 个 `Source/*.c/*.h` 的 SHA-256；`make fetch-source` 只允许从这个 commit 获取源码，然后逐文件验 hash，再从官方 `os_cfg.h` 模板生成固定配置。这样绝不会在迁移中偷偷拿旧版本 C 文件补缺。

当前沙箱没有安装 `coqc`，同时不能直接进行外网 `git clone`，所以我**没有声称完成 Coq 8.18 全量构建，也没有伪造一个 V2.93 源码 checkout**。新项目明确把下一道 gate 定义为：
    make audit
    make fetch-source
    make build

其中目前已经实际通过：
    PROJECT AUDIT: PASS
    COVERAGE AUDIT: PASS
    legacy target refs: 0
    security refs:      0
    Git worktree:       clean
    git diff --check:   PASS
    git fsck:           PASS

这是重构后的项目：

下载干净的 V2.93.01 Coq 验证项目

下载 SHA-256 校验文件

压缩包 SHA-256：
    28a5aba87c1ec06e669aa9ae5f66d8442fbdf516e21d9ce0193d7f381104562e

我认为这次重构解决了之前最大的工程风险：**以后 Codex 不应该再横向扩张几千个历史兼容证明，而是从一份固定的 V2.93.01 source inventory 开始，按照 `located → modeled → specified → local Hoare → component linked → full-target linked` 一行一行向最终 `GOOD_OS` 收敛。**



• 已完成基线修复和 Gate 1 的 stock 源码清单，保存本地提交 164dbbd。完整证明尚未完成；发现了需要你决定修复范围
  的新反例。

  当前状态：

- upstream：0c4a48e6fbc6e915714e816196619a5481accf0c，源码和配置哈希验证通过。

- stock 配置包含 92 个 portable 函数体、16 个边界入口。

- 六阶段覆盖：92 / 0 / 0 / 0 / 0 / 0；full-target-linked 为 0。

- Coq 8.18.0 完整构建、Print Assumptions、相关闭包 coqchk 通过，无新增证明洞或公理。

- K1、K2 指定路径的 C 回归通过；K3、K4 stock 反例已复现。

- repaired source 尚未冻结，GOOD_OS 尚未建立。原有工作区改动已保留。
  新反例是：单 mutex 的等待者超时退出后，OSMutexDel(OS_DEL_NO_PEND) 成功返回，却留下 ready[5]=1、
  OSTCBPrioTbl[5]=NULL。-O0、-O2 均复现，且调用满足源码注释约束。详见反例与复现步骤 (audit/
  GATE1_BLOCKER.md)。
  依据 AGENTS.md 第 7 条和 start-prompt.md 第十三节，这项额外修复需要你的明确决定：是否授权对该删除路径增加最
  小修复，并纳入 C 回归和 Coq 证明？
