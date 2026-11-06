# 第171步：真实 tick CPU hook 的调用契约连接

## 先理解这一小步

`OSTimeTick` 先分配局部变量、初始化 `cpu_sr=0`，随后调用 `OSTimeTickHook()`，再执行时钟更新及任务链扫描。

- 第170步已有真实调用／分配 trace，但只到 hook 调用点。
- 本步用框架真正的 `call_rule` 证明：**若 hook 满足这里明确写出的资源保持契约**，则该 `scall hook []` 能与已有原后缀规则顺序组合。
- “写出并连接契约”不等于“证明外部实现”。固定分析端口没有 hook 函数体；本步另证其执行无法从缺失函数体处返回。

## 固定对象与未改变项

实际源码为 `csrc/upstream/v2.93.01/checkout/Source/os_core.c:937–1008`，hook 调用位于950行；本步核对整文件和函数行片段哈希，见 `logs/stage171-tick-hook-contract/source-check.json`。历史清单中的 `csrc/repaired/...` 是旧身份标签，不声称该标签对应当前磁盘文件。

不修改 C、配置、AST、框架、tactics、旧证明和测试、冻结日志；不添加新 Inv、空 hook 实现、执行成功 oracle 或逻辑假设。沿用同一 `V293_time_ready_inv`、IE=false／ISRclear、有限合法未挂起任务链、旧空 LocalInv 边界。

## 稳定接口及资源去向

生产文件：`certiucos/v293/proofs/V293TimeTickHookContract.v`。

稳定上层接口 `V293_tick_hook_then_suffix` 直接证明真实：

```text
sseq (scall hook []) 原 tick 后缀
```

它显式要求 `Spec hook = Some (..., (Tvoid, []))`，不是把调用改为 skip。调用契约要求空实参、空逻辑参数、正确 owner；void 返回为 `None`，并保持同一 resource。

callee 只获得已经证明 `GoodFunAsrt` 的资源：抽象代码、中断控制、共享视图、scan 原始槽、缺失链字段、globals、saved=0 及通用 R。调用方局部绑定独立留在 caller frame，不塞入新 funasrt；调用前后通过分离合取重排恢复后缀入口。局部不变量由同一 `CurTid ** R` 建立。正式组合由 `RuleSound` 得到对应 `RuleSem`，仍不能跳过外部函数环境的正确性义务。

## 预先登记的对照与证据

协议在实现前固定于 `logs/stage171-tick-hook-contract/protocol.json`。

1. **相同实际内存端点**：`HCsame_endpoint` 复用第170步实际分配产生的同一个 Ms，不重新造堆。该端点同时满足资源拆分、scan171=`Vundef`、saved172=0、canary90=99、原 caller 槽70=idle。
2. **参数／返回值分别单因素改变**：`HCsame_guard_controls` 在同一完整状态及相同 caller frame 上，正确空参数／None 返回分别可满足契约；仅把参数改为 `[0]` 或仅把返回改为 `Some 0` 即拒绝。它们只测试各自 guard，不充当 hook 实现保持资源的证据。
3. **saved 与局部环境**：保持同一 Ms，仅改 saved 资源见证0→1时完整错误入口拒绝；沿用170的实际 load 反证。`HCcaller_not_fun` 独立证明 caller 局部绑定不符合 `GoodFunAsrt`，不依靠前面的 guard 早拒说明这一点。
4. **缺失实现**：`HCmissing_no_step` 及 `HCmissing_no_return` 针对实际 `CCprogram` 的 `sfexec 2002 [] []` 证明没有下一步／返回 trace。另造 `HCspec` 只用于展示逻辑调用义务，不声称它和该程序构成已验证的 `WFFunEnv`。

探针：`audit/probes/V293TimeTickHookContractProbe.v`。

## 验收读取方式

- 编译源码快照和全部失败日志均留在本步日志目录；最终编译身份由 `stable-compiles.json` 指定。
- `trust.json` 记录19个根的 `Print Assumptions`，及**两个新入口模块连同递归依赖**的 `coqchk`。这不是重新检查此前400个独立入口；旧证据按冻结哈希保留。允许假设集合不扩大。
- 本步先运行原2013项测试作为基线，再加5项结构回归。最终数量、完整旧 failure/error ID 集合比较、构建、审计和清理以 `verification.json` 实测为准，不把旧失败刷绿。
- `make audit` 仍有旧 coverage identity 失败；`git diff --check` 仍是旧框架581–586行六处 whitespace。本步不覆盖旧审计报告。

## 审查结论与下一步

**本步只接通带显式外部契约的逻辑调用和后缀，未证明 hook 实现返回。** 保持资源是新契约的要求，尚不是固定端口的事实。probe 的正入口证明与 guard 负控不证明资源保持的真实实现。

完整 tick 尚需函数返回／释放局部变量及函数环境连接；生产中断安装、初始化、各 API 的统一共享状态、`WFIFun`、源码级 `GOOD_OS` 及同程序 K1–K4 均未闭合。六门仍94/1/1/1/1/0，没有增加整函数信用。下一步沿真实函数的返回和局部资源释放继续连接，同时保持 CPU hook 边界开放；不能为补齐证明凭空加入 hook body。

第一阶段未完成；uCOS3 未开始；总目标保持 active，不提交或推送。
