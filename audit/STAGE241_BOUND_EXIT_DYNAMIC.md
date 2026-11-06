# 第241步：同一地址绑定 LocalInv 下的 Exit 三路径与共同函数环境

## 为什么做这一步

第240步证明了完整 changed-case Exit，却不能据此宣称 quiet/same 路径也成立。本步将三个既有运行路径接入同一个候选地址绑定 `LocalInv`，保留原 ready/TCB/storage Inv、原 normalized 函数体和固定 C/config。不是重新编写三个运行时函数，也不是把旧 shared-LI Hoare 定理直接改名。

| 路径／接口 | 实际证明入口 | 对初学者的解释 |
| --- | --- | --- |
| changed | `V293_bound_dynamic_changed_contract` | 解码动态逻辑参数，再接第240步真实整函数契约；返回保存绑定观察 |
| quiet | `V293_OSIntExit_quiet_exact_builder_contract` | 使用原先对 LI 参数化的真实函数体证明，只实例化为 bound LI |
| same | `V293_OSIntExit_same_exact_builder_contract` | 仍执行真实调度计算，但当前任务不变；保留同一 bound p_local |
| 统一边界 | `V293_OSIntExit_bound_dynamic_contract` | 任意逻辑参数与合法 builder 结果的统一整函数契约；畸形路径对应 false 前置 |
| 实际调用 | `V293_OSIntExit_bound_dynamic_call` | 同一实际 scall 接口，保留调用者 frame 和返回局部不变量 |
| 三函数环境 | `V293_bound_dynamic_WFFunEnv` / `V293_bound_dynamic_WFIFun` | 原 Enter/Exit/Sched 三函数使用同一 LI、Inv 和 joint Sched 查找 |

changed/same 分别通过已有 critical/ISR 到 all-joint 的规格嵌入连接真实 Sched；嵌入始终保持同一 LI，没有更换局部不变量的 Hoare transport。quiet 不需要调度调用。逻辑参数里的标签选择适用契约，不是在原程序中新增分支。

## 独立检查与单因素对照

`audit/probes/V293OSIntExitBoundDynamicProbe.v` 使用两套已有 typed 内存见证：changed/quiet 共享 RDprogram，same 使用原 SEprogram。它们是两套地址实例，不声称三种路径在同一个具体内存上同时成立。通用生产定理对参数统一量化，每个实例内部的三函数共享同一 LI/Inv。

- changed 的字面返回对照第240步独立 BIret；quiet 独立写出资源，same 独立写出外部资源及最高就绪任务的存在量化。
- 三路径实际 builder 与 scall 前置均有 typed 非空见证，不依赖 false 前置制造表面通过。
- quiet/same 从旧前置已有的全局名称观察建立 bound p_local，不额外假设 globals，不复制可写控制字节。地址观察零堆足迹但不等于逻辑上的 Aemp。
- `BDquiet_return_forget` / `SDreturn_forget` 仅弱化返回局部绑定，其他资源和程序保持不变。这是规格单因素消融，不是两次完整执行，也不证明旧规格不成立。
- 原 shared-LI 对照继续检查相同 runtime Exit/Sched；旧第238步错误 running 绑定负对照未修改，不能替代本步三条函数体证明。
- 非空实参由 BuildPreI 拒绝；畸形逻辑标签或缺失载荷前／后置均为 false。BuildRetI 本身不检查实参个数，不能误称其单独拒绝非法调用。

## 结果边界与下一步

本步完成候选 bound-LI 动态 Exit 的 changed/quiet/same 接入，不声称旧完整三函数规格仅改了 LI：候选 Enter 沿用第240步 bound Aemp 契约，与旧 local-storage Enter 边界不同。旧源码、旧规格和旧证据不改写。

这些是 typed 满足性见证，不是初始化可达；不是所有 BuildintPre、不是最终 iret 闭合，不是 `WFInt`，不是 `GOOD_OS`。同程序 K1–K4 未闭合，uCOS3 未开始，未提交／推送。下一步应接入中断返回／WFInt，并核对 Enter、Exit 与中断入口边界能否在同一个生产规格中组合，不能跳过尚未闭合的顶层义务。

逐根假设、递归 coqchk、构建、结构回归与全回归以本步 `audit/logs/stage241-bound-exit-dynamic/verification.json` 为最终实测。旧423失败、1错误和 audit/whitespace 历史失败保留；六门覆盖不得因局部定理增加而自动升级。编译探索的失败日志和对应源码快照保留，不称为语义 TDD。
