# 第199步：把中断退出前缀放入真实全局任务映射

## 这一小步在解决什么

第198步已能在单任务状态中，从 `OSIntExit()` 调用一直执行到 `OSIntCtxSw()` 的函数执行入口。本步沿用完全相同的抽象函数和物理资源，把这条完整前缀接到框架原有 `lpstep` 全局执行关系，而不是再创建一个执行模型。

可以将三张映射理解为：`T` 保存各任务下一段代码，`les` 保存各任务局部变量环境，`aus` 保存各任务 IE／中断栈／临界栈。本步保证只更新当前任务的映射项，其他任务的三类现场均不变；共享内存按原函数前缀实际变化，不能把“任务现场保持”理解成“共享堆完全不变”。

**已有 `kint` 中断现场是入口条件，不是本步生成或安装的生产 ISR。端点仍停在缺失端口的 `sfexec`；实际任务切换尚未实现。**

## 不变的目标和源码身份

目标仍为固定配置 uC/OS-II V2.93.01、上游提交 `0c4a48e6fbc6e915714e816196619a5481accf0c`，不扩展授权修复范围。本步没有修改 C、配置、原 AST、既有抽象函数、framework、tactics、旧证明／测试或冻结证据。

`source-check.json` 重建授权修复后的预处理函数，并与锁定清单逐字节核对：

| 函数 | `os_core.c` 原定位 | 配置后定义 SHA-256 |
| --- | --- | --- |
| `OSIntExit` | 693–736 | `eface83f6f4b0aa36685c3996ec8df5d48091ea2ccb2f62918fb03a91f3bd789` |
| `OS_SchedNew` | 1751–1776 | `6d156edfff0548ed63fdff59a400e8d0ca0e69813ef6bf0142d0ce1902443d71` |

前缀继续使用 ADR-0005 已明确区分的临界宏抽象；不新增端口实现，不把该抽象称为原始端口语义保持。

## 主接口与证明连接

生产文件：`certiucos/v293/proofs/V293OSIntExitInterruptGlobal.v`。

稳定主接口 `V293_OSIntExit_interrupt_switch_entry`：

1. 要求输入中当前任务的真实 `T/les/aus` 绑定已存在，不通过预先覆盖映射来制造初始任务；程序由 `pumerge po pi` 给出。
2. 从独立资源中推导原调度前缀：fresh saved 四字节分配和初始化、`encrit`、nesting 1→0、两级 guards、真实 `OS_SchedNew` 调用和局部分配／释放、目标更新、不同任务比较、counter 模递增及真实端口调用入口。
3. 用已有 continuation locality 将局部 trace 嵌入既有 `kint`，逐步导出 `InOS`，再构造真实 `inapi_step/pt_step`；调用者不提供 trace 或逐步分类答案。
4. 以 `ltstep_goodks` 保持 continuation 条件。`intcont` 遇到 `kcall` 就停止，因此不能单凭“下面有 kint”推出分类：有定义的最近调用用真实 lookup；缺失调用与 `goodks/no_os` 的组合由下层 `kint` 排除。
5. 客户状态 `cst` 和当前执行任务 ID 保持。端点保留 `excrit → sret → kcall → kint` 整条待恢复 continuation，实际 IE=false，原 IE 压入临界栈；saved 四字节仍存活且归当前调用所有。

`V293_global_endpoint_other_tasks` 对任意其他任务逐点证明三张映射不变。主定理的终态就是这种单项更新形状。

## 独立正控与单因素对照

探针：`audit/probes/V293OSIntExitInterruptGlobalProbe.v`。复用第198步独立构造的非空 `SX` 空间资源，不从目标 trace 反向假定入口。

| 对照 | 保持不变／唯一改变 | 实际证明 | 不能据此声称 |
| --- | --- | --- | --- |
| 完整全局前缀 | 同一程序、堆、当前 waiting6、最高 ready4、其他任务现场；只改初始 IE | 两侧都从原调用到同一端口入口；端点 IE=false，分别保存 false／true，counter=20，saved 四字节存活，caller 的同名 saved=23、局部 running=0 保持 | 端口实现、切换或完整不同任务返回 |
| 其他任务现场 | 主接口对其他 code/env/aux 全量化，可分别替换 | 三张映射逐点 frame；另实例化非空 code、非空 `SXcaller` 和 `(true,[1],nil)`，并读取 caller 的 601 绑定 | 共享内存完全不变、所有任务已验证 |
| 完整前缀端点 | 原端口 lookup=None，IE=false，保留非空临界栈 | `GXprefix_endpoint_stuck` 排除所有 `lpstep` 构造，包括中断、客户端步和任务切换 | 只证明局部停顿就够了 |
| 独立边界 IE 控制 | 两侧均为同一 sfexec／程序／堆／T／les，原 critical stack **均为 nil**；只改当前 IE | false 无任何全局下一步；true 实际执行 `li_step/pint_step`，安装新的 kint，其他任务现场不动 | port 函数有实现，或把完整前缀端点只改 IE 就能触发中断 |

最后一行故意与完整前缀端点分开：原 `lintstep` 要求 `ci=nil`，而完整前缀端点有保存的 IE 栈。本步不修改规则，也不删除这个条件制造阳性。边界控制使用显式非生产中断表，只测该条原规则。

## 审查后收窄的结论

- “全局执行”仅指原 `lpstep` 中**存在一条不交错执行**，不等于所有交错保持不变量，也不是 no-stuck 的生产内核。
- 主接口仍有真实资源、函数 lookup、当前任务一致性及 continuation 有效性前提；它不是无前提的任意程序结论。
- 端口缺失的无全局下一步是待补义务的反证性边界，不是通过删除该路径来完成 safety。
- 框架 `switch` 原语只更新当前指针和执行者，不同步 `OSPrioCur`。本步没有把这种指针切换当成完整端口效果。
- 未新增抽象机制；保留原执行关系。开发中未被主证明使用的映射规范化辅助引理已删除。
- 失败编译的日志、原退出码及输入快照均保留；稳定源中无新增公理或证明孔。不声称语义 TDD。

## 如何复查

```bash
PYTHONDONTWRITEBYTECODE=1 python3 audit/logs/stage199-interrupt-global-entry/recheck-checkpoint.py
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s tests -p test_interrupt_global_entry.py -v
make build COQBIN=/data/home/lucentzhou/.opam/default/bin/ JOBS=2
```

实际检查数量、递归入口、依赖公理、两轮全量回归和旧失败有序 ID 见同目录 `verification.json`、`trust.json` 与测试日志；源快照及 manifest 将源码和证据绑定。Python 结构测试只检查接口和材料，不代替 `coqc/coqchk`。

既有审计的 stale function evidence input identity、423 个失败／1 个错误及 `inferules.v:581–586` 空白问题仍保留，不靠弱化 gate 获得通过。六门仍为 `94 / 1 / 1 / 1 / 1 / 0`。

## 下一步与最终目标

下一项实质义务仍是依据已接受的源码级任务切换／中断边界，确定 `OSIntCtxSw` 与框架原语、优先级缓存以及 continuation 恢复的可核查对应；不是自行补一个“会通过证明”的假 C 函数。随后还需生产 ISR/LocalInv、WFFunEnv、初始化及整核模拟。

源码级 `GOOD_OS` 未闭合，K1–K4 同程序回归也未成为整核结果；uCOS3 尚未启动，两阶段总目标继续 active。本步不提交或推送 Git。
