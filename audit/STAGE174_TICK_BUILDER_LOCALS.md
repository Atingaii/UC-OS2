# 第174步：任意 raw local 初值接入真实函数 builder

## 解决了什么

第173步已有原 tick 完整 body 的条件 Hoare 证明，但 scan 入口固定为 `Vundef`。框架真正的 `buildp` 对两个 local 的 raw 值均作存在量化，不能用一个具体非空入口代替其全部前置条件。本步补上这个差距：saved、scan 初值都参数化，再把完整 body 接到真正的 `BuildPreI`／`BuildRetI`。

**准确结论是一个函数的、依赖明确 CPU hook 契约的 builder 义务及其实例化 `RuleSem`，不是全程序 `WFFunEnv`、实际完整 tick 执行或最终 `GOOD_OS`。这里的 fpre／fpost／hook Spec 是对外部 clock／run 等参数固定的契约族；尚未安装为覆盖全部调用的统一全局规格。**

固定版本仍是 uC/OS-II V2.93.01、提交 `0c4a48e6fbc6e915714e816196619a5481accf0c`。重新核对 `csrc/upstream/v2.93.01/checkout/Source/os_core.c:937–1008`、第950行 hook 与 analysis-port 说明的实际哈希，见 [source-check.json](logs/stage174-tick-builder-locals/source-check.json)。未修改 C、配置、AST、framework、tactics、旧证明、旧测试或冻结证据；没有新 Inv、skip hook 或执行成功 oracle。

## 最小证明链

生产文件：[V293TimeTickBuilderLocals.v](../certiucos/v293/proofs/V293TimeTickBuilderLocals.v)。

1. `V293_tick_builder_resource` 只含共享资源和已证明 `GoodFunAsrt` 的剩余资源，不含两个 local 的地址、值或绑定。hook 的 fpre/fpost 使用该资源；local 留在 caller frame，不能用局部绑定污染 callee 契约。
2. `V293_tick_builder_body_hoare` 接受任意 raw saved／scan 初值。真正执行 `cpu_sr=0`，不读取其旧值；原 `scall hook []`、完整后缀和 `sret` 均保留。raw 未初始化字节并未被当作有类型整数或指针。
3. `unpack` 从实际 builder 的两组 `EX val, LV ...` 和 `A_dom_lenv` 提取两个地址、两个值与 caller 绑定；`pack` 对运行／停机分支分别归还两组 raw local 资源、剩余资源及域断言，None 约束保持。
4. 稳定上层接口 `V293_tick_builder_internal_contract` 以真正 `P f = Some tick_function`、`BuildPreI`、`BuildRetI` 为前提，展开并核对 builder，推导完整 body 的 `InfRules`。空形参使合法实参列表只能为空；两个 local 名必须不同。不是另造一个名字相似的 builder。
5. 环境、合法有限未挂起链、IE=false／ISRclear、栈顶、LocalInv、frame/change 和 hook Spec 仍是明确前提。探针证明具体全局绑定与精确 local 域满足环境前提；通用接口没有凭空消除这些边界。

## 独立实例和单因素控制

探针：[V293TimeTickBuilderLocalsProbe.v](probes/V293TimeTickBuilderLocalsProbe.v)。前瞻协议：[protocol.json](logs/stage174-tick-builder-locals/protocol.json)。

| 检查 | 实际结果与边界 |
| --- | --- |
| 实际分配入口非空 | `BLallocated` 复用实际两次分配后的内存，完整新入口及 `BuildPreI` 断言成立，saved／scan 都为 `Vundef` |
| 同一分配端点负控 | `BLsame_allocated_controls` 固定环境、堆、抽象状态和全部其他资源，只把完整入口中 scan 见证由 `Vundef` 改为 idle 指针即拒绝 |
| 任意 scan 不是空泛参数 | `BLarbitrary_scan_nonvacuous` 对同一分配内存独立执行一次 scan 槽 store，证明同一新 Ms 满足指针 scan 的完整新入口及实际 builder pre；旧固定 `Vundef` 入口在同一 Ms 被真实 load 拒绝 |
| hook 不拥有 caller local | `GoodFunAsrt` 的共享资源与 caller frame 分开；正式 `call_rule` 的 frame 保留任意 scan 和已赋值 saved，不依赖 local 提前初始化 |
| 真正 builder 计算 | `BLbuilders` 直接计算固定函数的两个 builder；`BLcontract` 实例化稳定接口，`BLsemantics` 经 `RuleSound` 得到条件语义 |
| 完整 void post 非空与负控 | `BLstopped_return_nonvacuous` 对 `run<256`、`run<>1` 构造完整 builder None post；同一状态只把 None 改为 Some0 即拒绝。任意 Some 另有通用拒绝定理 |
| 缺失 hook 不冒充实现 | `BLmissing_hook_still_blocked` 保留固定程序缺失 hook body 时无下一步的结论 |

scan 指针 store 是独立 fixture 操作，不是新增的 C 初始化；不能声称原调用前缀会把 scan 初始化为 idle。store 的 frame 保留全部其他断言，但本步没有新增逐字节 canary 读出定理。None 返回非空实例只指定 ghost `END`，没有执行 clock++／hook；运行分支的完整 builder post 独立非空实例尚未建立。这些检查不能拼成完整 tick 实际 trace。

## 验收索引

- 稳定编译为生产 `body13`、探针 `probe14`，见 [stable-compiles.json](logs/stage174-tick-builder-locals/stable-compiles.json)。27次编译、20次非零诊断和全部快照保留；开发编译错误不是语义负控。
- 新结构测试发现生产注释中使用了词法门禁用的动词；没有削弱门，停止第一次信任检查后只改注释，重新编译并完整重跑。首次递归检查的中断记录、零测试筛选及失败的结构测试均保留，不能当作语义通过或反例。
- 9个生产根、19个探针根，以及两个新入口及递归依赖的检查见 [trust.json](logs/stage174-tick-builder-locals/trust.json)。检查期间563份 Coq 输入不变；不是此前所有入口重新检查。允许假设集合未扩大，实际仍使用既有经典逻辑、函数外延性与 Eqdep。
- 新增5项结构回归；全套由2028项增至2033项，旧423失败／1错误保留，并比较完整失败／错误 ID，而非只比较数量。两轮最终全套分别在文档整理前后运行；精确结果见 [verification.json](logs/stage174-tick-builder-locals/verification.json)。
- 构建、project audit、清理后构建结果与旧失败均保留。`make audit` 的旧 coverage input identity 失败、`git diff --check` 的旧 inferules 第581–586行六处 whitespace 不改写。
- [反向审查](logs/stage174-tick-builder-locals/adversarial-review.json)、[逐项清理清单](logs/stage174-tick-builder-locals/cleanup-inventory.json)、[最终验收](logs/stage174-tick-builder-locals/verification.json) 与冻结 manifest 共同记录边界。清理只删除新的一次性 Trust 产品、备份与测试字节码，恢复既有两缓存，保留源文件、失败日志和可复用 Coq 产品。

## 下一步与最终目标

这一轮消除了“body 与真实 builder 未连接”的局部障碍；不能再把它当作尚未完成的同一事项重复计数。下一步应沿这个稳定函数级接口处理生产共享资源／ISR 的接入，以及原 CPU hook 的实现保持与返回义务，再接全程序函数环境，而不是再造一个具体入口。

CPU hook 真实实现、生产 Inv／LocalInv／ISR、初始化／WFIFun／最终源码级 `GOOD_OS` 与同程序 K1–K4 仍开放。六阶段覆盖维持 `94/1/1/1/1/0`，没有授予新的无条件整函数或整核覆盖信用。第一阶段未完成，uCOS3 未开始，总目标保持 active；不提交／推送。完成 uC/OS-II 后才按老师附件进入 uCOS3，不能把局部模型或条件函数证明当作整个内核端到端验证。
