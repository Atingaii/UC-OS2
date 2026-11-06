# 第175步：同一份 tick／hook 规格接收不同 clock 与 run

## 解决的具体问题

第174步已经证明真实 `BuildPreI`／`BuildRetI` 与两个任意 raw local 初值的连接，但其契约把 clock、run 固定在函数外。换一个调用快照就需要另一份 hook 规格。这还不能当作一个固定函数环境中的反复调用。

本步只消除这个缺口：**在其他外部参数固定、原有前提成立时，同一份 Spec 覆盖任意 clock 与合法 run**。不重复计算174已完成的 builder 工作，也不声称已得到整个程序的统一规格。

## 实现与稳定接口

生产文件：`certiucos/v293/proofs/V293TimeTickUniformSpec.v`。

复用框架已有 `list logicvar`，不添加状态模型或新 oracle：

```text
lg = [logic_val (Vint32 clock); logic_val (Vint32 running)]
run = Z.to_nat (Int.unsigned running)
```

- `V293_tick_uniform_hook_pre/post`：共享资源按同一个 lg 选择，保持 clock 与 run，不让 pre/post 各自选不相干的存在见证；实参为空、返回为 None。两个 caller local 不交给 hook。
- `V293_tick_uniform_hook_call`：真实 `call_rule`，令 `logicl=lg`，不是跳过 hook 的行政规则。
- `V293_tick_uniform_body_hoare`：真实 saved=0、真实 hook 调用、原 clock++／run 判断／完整 while、真实 `sret` 的精确 body 组合；继续复用已有赋值、后缀与返回接口。
- **`V293_tick_uniform_internal_contract`**：稳定上层接口。展开真实 `BuildPreI`／`BuildRetI`，对所有 vl、lg 给出条件函数义务；有效索引证明真实 body，无效 lg／run>=256 入口为 Afalse。非空 C 实参仍由真实 builder 的形参匹配拒绝，不改框架。

`bindings`、idle、message、ct、es、全局地址、R、ir、si、ci 仍为固定外部参数。原有 NoAbs、环境、LocalInv、frame、可变 aop、合法有限未挂起链、地址范围、IE=false／ISRclear 等前提全部保留。没有把这些前提搬成新的执行 oracle。

## 对抗检查与单因素对照

探针：`audit/probes/V293TimeTickUniformSpecProbe.v`。固定同一个 `CCprogram` 和不带 clock/run 参数的 `Uspec`，其 tick、hook 两个表项由 `Ufixed_entries` 直接计算。

| 检查 | 变化项 | 保持不变及独立证据 |
| --- | --- | --- |
| `Uall_clock_run_same_spec` | lg 里的 clock/run | 一个 Uspec 下覆盖所有 clock、run<256；不更换 Spec |
| `Uallocated` | 无 | 独立真实分配后的完整入口非空，两个 raw local 保留 |
| `Usame_endpoint_clock_control` | 只改 clock 索引37→38 | 同一 BHmemory、抽象状态、run、代码与所有资源；从实际 ostmid 槽排除错配 |
| `Usame_endpoint_run_control` | 只改 run 索引0→255 | 同一 BHmemory clock 0 与所有状态；实际 Tint8 load 与错误资源冲突 |
| `Usame_stopped_code` | 比较上述两个 run 的 ghost code | 直接证明 PCcode 0=PCcode 255，因此 run 对照不是换分支造成的早拒绝 |
| `Umalformed_or_out_of_range` | 错误 lg、run=256 | 总规格中前置为 Afalse，不加公开的合法-lg假设 |
| `Ustopped_post_nonvacuous` | 同一完整 post 只改 None→Some 0 | 独立停机完整 post 可满足；保留原数据与 local 所有权 |
| `Umissing_hook`／`Uno_EqDom` | 不伪造实现 | 当前程序缺少 hook，没有下一步；直接反证 EqDom CCprogram Uspec |

停机 post fixture 只复用既有 ghost END 状态与 call/allocation 前缀，**没有执行 clock++ 或 hook，不能拼成一条完整 tick trace**。运行完整 post 的独立非空实例本步仍未建立。clock 对照检查实际抽象时间槽，不冒称该对照执行了新 tick；run 对照另由真实物理 load 支持。

## 证据与复核

证据目录：`audit/logs/stage175-tick-uniform-spec/`。先记录 baseline、源码身份、不可变前瞻协议，再编译；每次尝试保留源码快照、退出码和日志。编译失败不是语义反例，不删除诊断。已移除一次尝试中不必要的函数外延性导入，最终用返回后条件逐点蕴含连接，不增加信任假设。

机器检查结果以本步 `trust.json`、`final-tests.json`、`final-documented-tests.json`、`cleanup.json`、`verification.json` 和最终 `checkpoint-evidence-manifest.json` 为准。结构测试只检查连接形态，不能代替 Coq 内核与递归 coqchk。旧失败集合不得删除或改写以制造全绿。

## 尚未完成什么

本步不是 CPU hook 实现、生产 ISR 安装、全程序 `WFFunEnv`、初始化或最终 `GOOD_OS`。事实上当前 fixture 的 `EqDom` 已被反证，不能用这两个 Spec 表项推导全程序环境良构。

下一步应把固定 task／共享资源族接到真实全程序的可变状态与函数环境，并处理生产 ISR／hook 保持和返回。不能再次将“clock/run 仍需每次更换 Spec”列作未完成，但“所有动态 task／中断状态都已由一份全局规格覆盖”也不成立。

固定 C、配置、AST、框架、旧证明、旧测试、旧冻结证据不修改。函数覆盖仍为94/1/1/1/1/0，没有新增无条件整函数信用。第一阶段 `GOOD_OS` 与同程序 K1–K4 未完成，uCOS3 未开始，总目标保持 active，不提交／推送。

## 本步实际检查结果

- Coq 8.18.0：生产与探针稳定编译通过；24个根的假设闭包及两个入口连同递归依赖的 coqchk 通过（416.88秒）。565份 Coq 输入检查期间未变；实际／允许仍为既有 classic、函数外延性和 Eqdep 三项，不扩大信任集合。
- 新增5项结构／证据回归全部通过；全套2033→2038，保留原423失败／1错误与完全相同的失败／错误ID集合，不宣称全套通过。
- `make build`、`project-audit.py` 退出0。`make audit` 仍退出2（原函数证据 input identity 过期）；`git diff --check` 仍退出2（原 inferules.v 581–586六行），未删除旧失败。
- 13次编译、9次非零的日志、源码快照和身份全部保留；编译期间不编辑源码。逐项清理及写入文档后的第二轮回归与最终不变性核对由 `verification.json` 确认；不回写旧冻结证据。
