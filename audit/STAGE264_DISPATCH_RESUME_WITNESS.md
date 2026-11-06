# 第264步：完整内层 dispatch 到已有目标 pending 返回的独立实例

## 1. 问题与最小改动

第263步的生产接口已经能组合完整调度调用与目标返回，但其独立实例只从物理 switch 开始。条件接口存在，不等于各条件能在同一个实际堆上同时成立。本步专门补这个证据缺口，不新增生产封装，不修改旧证明或函数证据。

固定对象仍为 uC/OS-II V2.93.01、上游提交 `0c4a48e6fbc6e915714e816196619a5481accf0c` 及既定配置。实际源码定位见本步 source-identity.json；OSIntExit 内层 dispatch 对应 `os_core.c` 的 OS_SchedNew 调用、目标指针更新、优先级比较及中断切换调用点。沿用 ADR-0005 临界原语和 ADR-0010 优先级缓存复制加 switch 的源码级边界。

新增证明只在 `audit/probes/V293DispatchResumeWitnessProbe.v`。直接实例化旧 `V293_exit_call_resume_progsim`，没有新增生产模块，`_CoqProject` 与依赖文件不变。这里的“独立”指具体状态中自行建立组合接口的条件，并非重建另一套语义、拒绝复用既有引理，或证明任意调用者正确。

## 2. 六个根与同堆连接

| 根 | 直接检验的事实 |
| --- | --- |
| `DPscheduled_canonical` | 从 OS_SchedNew 调用前开始，实际调用、分配、函数体、释放和目标指针写完成；证明调度后堆等于约定 canonical 堆上的实际 store 结果 |
| `DPdispatch_storage` | 在同一组 M/M1/Mc/Msw/Mret 上完成比较、真实计数回绕、缓存复制、当前指针写和目标 saved 块释放；同时执行完整内层 dispatch 到 switch |
| `DPcontext` | 实际程序中存在 enclosing OS 函数绑定；没有人为消除原 InOS 条件 |
| `DPprefix_global` | 把上述真实 cstepstar 提升到原 lpstep 的有限闭包，精确保持任务映射、环境和辅助栈 |
| `DPactual_dispatch_and_resume` | 从同一个初始 CEM 同时建立完整全局有限执行和原 ProgSim；无 ProgSim 前提 |
| `DPtarget_store_and_omission` | 固定调度后 CFfinal，只省略目标指针 store；读取仍为旧任务而不是所选任务 |

核心定理起点的当前任务执行 `XPbody`，不是已经到 switch 的 `RPcode`。它先通过 `DPprefix_global` 执行整个内层 dispatch，再用既有 `RPfinite_switch_and_return` 执行 switch、已有目标 pending 的 excrit/sret/free/caller。原 ProgSim 则单独调用生产接口，并以 `HPschedule` 及 `SPterminal` 建立高层匹配和最终 caller 端点模拟。有限轨迹和模拟分别证明，不能用一条成功轨迹代替全部后继、输出与异常义务。

## 3. 具体物理状态与资源

- 初始堆为非空 typed `CEM`。调度结果选择优先级4的 OwnershipReady；high 从88更新为4，旧优先级缓存为6，比较实际得到真。
- 计数块95为 `Int.mone`，实际32位增量 store 后为 `Int.zero`；不是只在整数算术中声明回绕。
- 目标指针块93和当前指针块1分开更新。所有后续阶段使用同一组 existential 堆，不靠分别存在的、不相容的端点拼接。
- 当前任务环境为空，目标任务独占 saved 块98。这里故意保留空当前环境，避免把当前调用局部和目标保存局部别名为同一块；并未证明完整 OSIntExit 入口可达此 fixture。
- `free Tint32 98` 真实执行，四字节全部移除，其他块与 Msw 相同。该 frame 只描述 free，不表示调度以来所有其他块未变。
- 最终任务为 OwnershipReady；切出任务仍挂起，任务映射保留其 HPpending，局部环境仍为空、辅助栈不变。目标返回不等于切出者也已返回。

## 4. 事前冻结的单因素对照

协议在实现前冻结于 `audit/logs/stage264-dispatch-resume-witness/protocol.json`，配套 SHA 保持不变。

正常定理验证实际完整内层 dispatch 和后续目标返回。省略对照固定源码与同一调度后 CFfinal，仅中和目标指针 store：high 已是4，但目标读取仍是 OwnershipWaiting，因此不等于 OwnershipReady。这是堆契约对照，不是一个完整 mutant 程序执行，不把早期读取拒绝当作 counter、copy、switch 或 free 已分别工作的证据。下游机制由正常定理的实际执行和同堆资源事实独立检验。计数回绕是正例边界，不伪称它有本步未实施的双运行消融。

## 5. 对抗性复查与明确限制

1. **组合是否循环？** 核心定理无 ProgSim 前提，最终 caller 用实际终止端点 SPterminal 建立；一般生产接口仍公开最终 caller 端点模拟条件，不推广为任意客户端。
2. **pending 从哪来？** pending 在任务映射中已存在。本步消费它，没有安装它，未证明任务挂起历史或重新调度公平性。
3. **是否完整函数调用？** 这是完整内层 dispatch，不是完整 OSIntExit 调用。尚未接入外层 saved 分配、初始化、running、encrit 与 nesting，当前空环境正是这个边界的可观察限制。
4. **typed 是否等于全局不变量？** high=88 大于配置最低优先级12，因此不是完整全局 Inv，也不是初始化可达证据。
5. **是否完整中断返回？** IE=false，目标保存栈顶=false；cs/ncs 尾部任意，不代表可推广到 IE=true、任意外部端口或任意中断交错。不是硬件端口 refinement。
6. **最终验收？** 不是 `GOOD_OS`；不是 `WFInt`；K1–K4 未闭合，uCOS3 未开始。未提交／推送。不刷新旧失败证据来制造全仓通过。

下一步先把外层实际函数调用、局部分配及临界区/nesting 接入本步完整内层 dispatch；必须另行处理当前局部与目标保存局部的分离和真实挂起续体来源，再连接共享不变量与顶层原模拟。

## 6. 复现与证据约定

本步日志目录保留每次编译快照（包括失败）、稳定重复编译、逐根 Print Assumptions、递归 coqchk、完整回归差分和旧输入身份。Coq 串行检查，检查期间不修改证明输入。Python 测试检查接口、来源及证据一致性，证明有效性由 Coq/coqchk 检查，不以字符串断言替代证明。

最终实测见第7节和 verification.json；复现约定不单独作为通过记录。只读检查入口：`python3 -B audit/logs/stage264-dispatch-resume-witness/checkpoint.py`。

## 7. 实测结果

| 检查 | 结果 |
| --- | --- |
| 稳定编译 | 既有生产 prod01/prod02、新实例 probe13/probe14；各对源码哈希相同 |
| 信任检查 | 3个既有生产根、6个新实例根；递归 coqchk 通过，约532秒；752项输入未改 |
| 假设 | 仅既有 classic 与 functional_extensionality_dep |
| 构建／项目边界 | 通过；仍为339个活动 V293 Coq 文件，没有新增生产模块 |
| 新增回归 | 5项全部通过 |
| 全量测试 | 2485项；428个失败、1个错误；相对263步失败／错误 ID 及顺序完全一致 |
| make audit | 退出2：旧函数证据输入身份过期，未刷新旧门 |
| git diff --check | 退出2：既有 inferules.v:581–586 六行空白，未改框架 |
| 旧输入 | 2004项只有README和状态文档前缀变化，旧尾部原样保留 |

旧检查点在 trust 期间因运行进程 guard 拒绝的记录单独保留，不能算作身份拒绝证据；trust 结束后再次核对其前向元数据拒绝。旧 manifest 未改。`_CoqProject`、依赖文件、生产证明、C/config/AST、旧测试与日志均未改。历史覆盖94/1/1/1/1/0未重新验收。

清理前逐路径、字节、SHA确认，删除8项一次性信任产物和已恢复的缓存备份，共709161字节；保留源码、全部失败编译快照、日志及可复用 Coq 产物。这是局部检查点，不是全仓通过。
