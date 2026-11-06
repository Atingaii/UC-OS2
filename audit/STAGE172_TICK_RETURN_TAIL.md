# 第172步：原 tick 后缀结果连接真实返回与两个 local 释放

## 这一步解决什么

前一步已经把真实 `scall hook []` 的逻辑调用规则接到原 tick 后缀，但它的输出仍在 callee 环境，保留 `ptcb` 与 `cpu_sr` 两个 local。本步只解决这个明确边界：**给定原后缀结果，执行真正的 `sret/free`，恢复 caller 环境，归还除两个 local 外的全部资源。**

固定对象仍是 uC/OS-II V2.93.01，上游提交 `0c4a48e6fbc6e915714e816196619a5481accf0c`。实际源定位是 `csrc/upstream/v2.93.01/checkout/Source/os_core.c:937–1008`，其函数区间及文件哈希见 [source-check.json](logs/stage172-tick-return-tail/source-check.json)。历史 inventory 的 repaired 路径不是实际存在的源码位置。

没有改 C、配置、AST、framework、tactics、旧 proof、旧 tests 或旧冻结证据；没有添加 hook body、执行成功 oracle 或新的不变量。

## 最小证明链

生产文件：[V293TimeTickReturnTail.v](../certiucos/v293/proofs/V293TimeTickReturnTail.v)。

1. `V293_tick_free_owned` 从完整可写 `Amapsto` 与分离残余构造 `free` 的实际结果，结果内存就是残余内存；不是把 `free` 成功当作前提。
2. `V293_tick_owned_void_return` 处理 `getaddr` 的两种可能顺序，执行真实 `sret_step`、逐槽 `sfree_step` 与 `sfreeend_step`，恢复 caller 环境。两槽各自的 **全部 4 字节** 都在同一终点为 `None`，不只是 byte0。
3. `V293_tick_return_factor` 从既有 `scan_switch_result` 拆出 scan、saved 与精确剩余资源。运行分支保留实际链残余及 pend choices；停机分支保留 missing fields。两者均保留同一个 `SWINV(time_ready_inv ...)`、控制状态、globals 与 caller frame。
4. 稳定接口 `V293_tick_return_tail` 将原后缀结果接到上述实际返回步骤。它从后缀末尾 `sskip`、`kseq sret (kcall ...)` 出发，不要求执行 oracle。
5. callee 局部绑定不能直接搬到 caller 环境：`V293_tick_result_forget_bindings` 只在绑定蕴含 `Aemp` 时去掉它们；剩余 frame 仍必须满足 `GoodFunAsrt`。没有随意丢弃内存资源。

## 独立实例与单因素负控

探针：[V293TimeTickReturnTailProbe.v](probes/V293TimeTickReturnTailProbe.v)。

| 检查 | 实际证据与范围 |
| --- | --- |
| 接前一步接口 | `TRfrom_hook_contract_post` 接受 `HCrules` 的原 `CCpost`，剥离空字节 callee 绑定，再调用新稳定接口；仍是带明确前提的后缀连接 |
| 同一实际分配内存上的返回 | `TRsame_allocated_return` 用第170步真实分配得到的 `Ms`，另立 `sret` 尾部 fixture，产生同一 `Mf`；`CCbare` 在 caller 环境仍成立 |
| 两 local 完整释放 | 同一个 `Mf` 上，scan171 与 saved172 的所有 `k<4` 字节均为 `None` |
| caller 数据保持 | 同一个 `Mf` 上实际 load 得到 canary90=99、原槽70=`WhileIdle` |
| scan 单因素负控 | 保持同一 `Mf`、环境、抽象状态不变，只额外要求已释放 scan 的所有权，即矛盾 |
| saved 单因素负控 | 保持同一端点不变，只额外要求已释放 saved 的所有权，即矛盾；不靠 scan 负控的早拒冒充 saved 检查 |
| 完整停机 post 可满足 | `TRstopped_result_fixture` 在真实分配 `Ms` 的相同字节上构造完整 `TRpost`，`TRstopped_fixture_return` 用该 post 实际执行稳定尾部；覆盖所有 `run<256` 且 `run<>1` |
| 缺失 hook 仍阻塞 | `TRmissing_hook_still_blocked` 重用已证的固定程序无 hook body 时 `sfexec` 无下一步；没有伪造 hook 返回 |

**必须区分两段 trace。** `CCexecution` 只执行到真实 hook 调用点；探针上的返回是从指定尾部位置开始的独立 fixture，并非把两段直接拼接成整个 tick。完整停机 post 的构造只改变 ghost 程序位置到 `END`，没有执行 clock++，抽象 clock 也不变。它验证 post 非空和尾部接口可执行，不验证缺失的中间执行。运行分支有一般后缀结果到返回的证明，但本步没有构造运行分支完整后缀结果的独立可满足实例；实际分配 run=1 上的测试仍只是 raw tail fixture。

协议在证明前冻结于 [protocol.json](logs/stage172-tick-return-tail/protocol.json)，逐条反向审查见 [adversarial-review.json](logs/stage172-tick-return-tail/adversarial-review.json)。文本测试只作结构回归，不替代 Coq 语义检查。

## 可复核验收入口

- [stable-compiles.json](logs/stage172-tick-return-tail/stable-compiles.json)：生产 `tail09`、完整探针 `probe07` 的成功日志及源快照。
- [trust.json](logs/stage172-tick-return-tail/trust.json)：20 个新根的假设检查，两个新入口及递归依赖的独立 `coqchk`；不是此前全部入口重新检查。允许假设集合与第171步相同。
- 实测新增5项回归全通过；全套由2018项增至2023项，仍为旧423失败／1错误，完整ID集合相同。`make audit`仍因旧coverage input identity退出2，旧inferules第581–586行whitespace仍退出2；project audit退出0。
- [baseline-tests.json](logs/stage172-tick-return-tail/baseline-tests.json)、[final-tests.json](logs/stage172-tick-return-tail/final-tests.json)：本轮前后完整测试及逐项旧失败 ID 对照，不删除不利结果。
- [verification.json](logs/stage172-tick-return-tail/verification.json)：构建、5 项新增结构测试、全套测试、旧文件哈希、清理后构建与旧审计失败的最终核对。
- 编译共16次，10次非零均保留源快照与日志；这些是开发诊断，不是语义负控结果。
- 逐项确认后已清理9项一次性材料697870字节，包括信任入口、临时缓存备份及新增测试字节码；已恢复两份既有缓存，保留生产／探针可复用产品与全部诊断证据。

## 不增加整核信用

边界仍为 IE=false／ISRclear、合法有限未挂起链、旧空 LocalInv。**CPU hook 实现保持／返回、完整 tick 的函数级证明、生产 ISR 安装、初始化／WFIFun／GOOD_OS 及同程序 K1–K4 仍开放。** 本步没有新增整函数覆盖信用；六门维持 `94/1/1/1/1/0`，阶段一未完成，uCOS3 未开始，总目标 active，不提交或推送。

下一步应把这个实际返回尾部接到函数级逻辑接口，并继续核对 CPU hook 的真实实现义务；不得把外部 Spec 或独立尾部 fixture 当作整函数已经执行的证据。
