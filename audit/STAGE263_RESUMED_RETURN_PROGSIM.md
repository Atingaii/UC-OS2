# 第263步：切换至已有 pending 续体后的原模拟与实际返回

## 1. 本步要解决什么

上一步完成非调度分支的函数返回。调度分支不同：`switch` 立即改变正在执行的任务，切出者的剩余语句不会顺着原 C 调用栈立即执行。必须检查任务映射里被选中者实际保存了什么续体，再在该任务上继续证明。

本步从第一性语义事实出发：目标任务已在 `T` 中保存 `SKIP → excrit → sret → kcall`。不是创建或假设一次未来的公平调度。原 `ProgSim` 仍按全部后继、输出和异常检查，不是把一条成功有限轨迹冒充模拟。

## 2. 三个生产接口

| 接口 | 起点与结论 | 仍公开的条件 |
| --- | --- | --- |
| `V293_pending_exit_progsim` | 已存在的 pending 续体一直连接到 caller | 实际函数绑定、局部环境、保存栈顶=false、Tint32 的真实 free、最终 caller 端点模拟 |
| `V293_switch_pending_exit_progsim` | 原 switch 写 OSTCBCur，进入另一任务 pending，再完成返回 | 不同任务、真实 typed 指针读写、高层匹配、目标局部资源与最终 caller 模拟 |
| `V293_exit_call_resume_progsim` | 实际 OS_SchedNew 调用、指针更新、比较、计数、优先级复制、switch、目标 pending 返回 | 沿用既有实际读取／所有权与高层条件，只保留最终 caller 的 ProgSim |

源码：`certiucos/v293/proofs/V293ResumedReturnProgSim.v`。没有引入新的抽象执行器、替代模拟关系、额外源代码补丁或中间模拟 oracle。三个接口各自仅含最终后件和起点两个 `ProgSim`。

函数绑定本身不限定 body 必须等于规范 OSIntExit：该桥是符合上述续体形状的返回组合定理。实际来源、绑定和续体建立还须由调用方证明。`V293_exit_call_resume_progsim` 从 dispatch 语句开始，不覆盖完整 OSIntExit 函数入口、running/nesting 外层路径。

## 3. 独立实例：同一个非空物理堆

`audit/probes/V293ResumedReturnProgSimProbe.v` 中：

1. `RPstorage` 从既有 typed 非空分离堆构造目标指针 store、真实 OSTCBCur store 及保存局部块的四字节 free，并证明其他块不变。
2. `RPfinite_switch_and_return` 通过原 `lpstep` 的有限闭包执行 switch、目标 pending、excrit、sret、free 和 caller 恢复。
3. `RPactual_switch_and_resume_simulation` 在同一组 `M/Msw/Mret` 上同时给出该实际有限执行、原 switch 一步与原 `ProgSim`；定理没有任何 `ProgSim` 前提。最终终止 caller 的模拟由 `SPterminal` 独立建立。
4. 显式保留切出任务的 `HPpending`、其原局部环境和辅助栈。目标任务返回，不代表切出任务已经返回。

独立实例从物理 switch 开始，不是完整 OSIntExit 调用实例；没有独立建立完整调度调用加 pending 返回实例。实例的当前任务局部环境为空是 switch 点局部 fixture，不是从完整函数可达的证明。生产完整 dispatch 条件桥和该较短的独立实例不能混为一谈。

目标局部块用 `V293_cpu_lenv`；typed 分离堆的断言沿用既有 CG 环境，使用环境无关性转移实际保存块所有权，不以两个不同表示定义相等蒙混。初始 high=88，大于配置最低优先级12，因此非空 typed 堆不是完整全局 Inv，也不是初始化可达证据。

## 4. 事前冻结的单因素对照

协议在实现前冻结于 `audit/logs/stage263-resumed-return-progsim/protocol.json`。

- `RPnonempty_stack_steps` 与 `RPempty_stack_aborts`：固定代码、任务、物理堆、局部环境、中断状态，仅把目标 critical stack 从 `false::ncs` 改成空栈。前者实际执行 excrit；后者在原 `lpstepabt` 产生异常。不是只有语法 guard 拒绝，也不拿异常替代正常路径后续返回证明。
- `RPzero_high_match_rejected`：固定返回后物理状态，仅把高层 current 恢复为切出者；原 `ProgSim` 的 Cur 条件矛盾。这是端点匹配消融，不声称独立构造了整个错误高层 trace。
- 切出任务仍挂起：独立正常定理的映射结论直接检验，而非通过删去其映射制造一个单任务成功例。

## 5. 明确边界与下一步

- IE=false，保存栈顶=false；不推广到任意中断交错或 saved=true。
- 沿用 ADR-0005 的临界原语边界及 ADR-0010 的优先级缓存复制加 switch 边界；不是外部硬件端口 refinement。
- pending 在任务映射中已存在是公开前提；本步没有安装这个续体，也没有证明每个切出任务最终被重新调度。
- 最终 caller 端点模拟仍是生产条件；非终止 caller、完整共享／私有不变量和任意 client 尚未闭合。
- 不是完整 OSIntExit 所有分支；不是完整中断返回；不是 `WFInt`；不是 `GOOD_OS`。K1–K4 未闭合，uCOS3 未开始。未提交／推送。
- 后续先把真实调用中的挂起续体建立、完整调度前缀与本步返回连接，补齐独立同堆实例，再接共享不变量和顶层原模拟。不能用公平性承诺补掉实际语义义务。

## 6. 复现与证据约定

`audit/logs/stage263-resumed-return-progsim/` 保留事前协议、每次编译源码快照及失败日志、逐根假设、递归 coqchk、回归测试、旧输入差分和清理清单。Coq 检查串行运行，检查期间没有修改证明输入。构建、测试与只读复查的最终实测结果记录于后续表格及 verification.json；不把既有失败门改成通过。

## 7. 实测结果

| 检查 | 结果 |
| --- | --- |
| 稳定编译 | 生产 prod05/prod06、实例 probe10/probe11；每对源码哈希相同 |
| 信任检查 | 3个生产根、7个实例根；递归 coqchk 通过，约529秒；751项输入未改 |
| 假设 | 仅既有 classic 与 functional_extensionality_dep |
| 构建／静态边界 | 通过；339个活动 V293 Coq 文件 |
| 新增回归 | 5项全部通过 |
| 全量测试 | 2480项；428个失败、1个错误；相对262步失败／错误 ID 及相对顺序不变 |
| make audit | 退出2：旧函数证据输入身份过期，未刷新旧门 |
| git diff --check | 退出2：既有 inferules.v:581–586 六行空白，未改框架 |
| 旧输入 | 1901项只有4项允许的文档／构建元数据变化 |

前一检查点在前向元数据登记后的拒绝保留，旧 manifest 未改。依赖只增新模块3行，旧字节不变。历史覆盖94/1/1/1/1/0未重新验收。清理前逐路径、字节、SHA确认，删除8项一次性信任产物与已恢复的缓存备份，共709174字节；保留源码、日志、全部失败和可复用 Coq 产物。

只读复查：`python3 -B audit/logs/stage263-resumed-return-progsim/checkpoint.py`。本步是局部检查点，不是全仓通过。
