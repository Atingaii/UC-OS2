# Agent 工作约束：唯一目标 V2.93.01

继续开发前，阅读 `PROJECT_SCOPE.md` 和 `VERIFICATION_STATUS.md`；核对本次交接或恢复任务时，再阅读 `audit/BASELINE_REPORT.md`。根目录两份历史提示词不是可直接执行的当前指令。

1. 唯一活动目标是 uC/OS-II V2.93.01，提交 `0c4a48e6fbc6e915714e816196619a5481accf0c`，加上 `PROJECT_SCOPE.md` 明确授权的两类修复。
2. 仅复用真正版本无关的 `framework/` 与 `tactics/` 成果；不得导入、重建、改名或机械迁移旧内核专用证明树。
3. 保持固定配置。Multi-Pend、timer manager、命名、profiling、任务寄存器、debug tables、tick-step 和应用 hooks 保持范围外，除非用户明确改变范围。
4. 目标为功能正确性与 safety；不加入无关性质家族。
5. 建模 C 函数前，先定位准确的配置后函数体并记录源码哈希／定位，不使用其他发行版的函数体替代。
6. 独立等待结果字段和基于 TCB 指针的互斥锁所有者判断属于上游原生行为，直接从上游源码证明，不视为项目补丁。
7. 当前仅允许嵌套互斥锁优先级恢复与调度锁定自删除两类修复。新增修复先提供可复现反例，再取得用户明确的范围决定。
8. `certiucos/v293/` 中不得出现 `Admitted`、`admit`，也不得新增 `Axiom`、`Parameter` 或 `Conjecture`。
9. 每个配置后函数依次记录 `located`、`modeled`、`specified`、`local_hoare`、`component_linked`、`full_target_linked` 的机器可读证据。
10. 优先完成函数纵向连接，不以新增证明文件代替进展。每个函数暴露一个供上层使用的稳定接口定理。
11. 源码级 `GOOD_OS` 定理闭合前，不开展编译器、ABI、二进制或硬件正确性工作。
12. Git 检查点应小、可复现且可构建；若当前基础仍有构建或审计失败，明确保留失败状态，不通过破坏性清理隐藏未解决证明或源码错配。

`references/` 和历史提示词只作可移除参考；活动验证工程不得依赖它们。新增代码、规格和证据必须落在当前目标中，不能把历史材料的进度直接记入覆盖。
