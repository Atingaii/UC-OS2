# 第164步：从同一共享 core 取出等待节点并执行原 tick 迭代

## 解决哪个实际缺口

第163步已经证明原 `encrit ; (delay ; (advance ; excrit))` 单次迭代，
但调用者必须提前交出规范等待记录、删去该节点的剩余任务记录、具体 ready 三字节等 focused 资源。
共享不变量实际保存的是整张 canonical taskmap，ready 值及部分物理 pend 值还藏在存在量词内。
不能把“从内存读得到”当作“拥有可写字节”，也不能把两个可能重叠的投影拼成可分离权限。

本步把这个缺口接通：按**同一组抽象槽绑定的真实任务表**中的 lookup，
从全部 canonical records 抽出当前等待记录，保留其余任务；打开 ready 的隐藏取值；
调用第163步原 InfRules，最后归还同一 clock/task/ready core 及所有残余字段和 caller frame。
没有修改 C、配置、AST、旧证明、框架、tactics 或任何旧冻结证据。

## 稳定接口

生产文件：`certiucos/v293/proofs/V293TimeTickCoreFocus.v`。

- `V293_tick_wait_core_pre`：一个展开见证后的原 core 加 scanner、Next 等缺失字段和 caller frame。
  它仍然拥有整张任务表的 canonical records，而不是 `del tasks current` 或 focused 记录。
- `V293_tick_wait_core_unfold` / `fold`：与原 `V293_time_ready_core` 加同一补片的无损打开／归还。
  打开任意 core 只产生其实际 current/tasks/events/time 见证，**不凭空产生某个任务正在等待的事实**。
- `V293_tick_wait_record_open`：规范记录的隐藏优先级与 lookup 中优先级通过 bounded repr 单射归一，
  事件等待的 pend 从记录自身取出；时间等待不在记录中拥有 pend，因此选择显式补片的 pend。
- `V293_tick_wait_core_focus`：联合资源的真实 focus；不复制 task/current 抽象槽，不丢弃 frame。
- **`V293_tick_core_wait_iteration`**：上层稳定 InfRules。任务表、事件表、clock 见证在前置存在量化，
  lookup 与同一任务表绑定；不要求 caller 另外提供 focused 记录或具体 ready 见证。
- `V293_tick_core_wait_iteration_semantics`：仅通过既有 `RuleSound` 正向导出。

主规则没有执行、表达式求值、另一个 Hoare 定理或成功执行的外部 oracle 前提。
它仍要求合法本地环境、`CurLINV`、frame 性质、合法栈顶、地址／delay／优先级界、非 idle 和真实等待 lookup。
`pend<256` 补片参数的额外约束**只在时间等待时要求**；事件等待的实际 pend 界来自原记录。

## pend 为什么不能统一猜成 0

| 等待种类 | canonical record 是否拥有 pend | 取值来源 | 额外资源 |
|---|---|---|---|
| sem / mbox / q / mutex | 是，存在量化实际字节 | 打开其已经拥有的真实 pend | Next |
| time | 否 | caller 显式提供的 pend 单元 | Next 和 pend |

所有等待种类都复用同一条泛化源程序规则，不新增执行模型。
返回以存在量化的实际 pend 表达精确残余布局，而不是为隐藏值编造确定值。
到期后不再属于 canonical ready 记录的 delay／pend／事件指针仍由第163步 post 保留。

## 非空与单因素核对

探针文件：`audit/probes/V293TimeTickCoreFocusProbe.v`。

1. 从第163步独立 encoded bytes 的 `RUspatial` 入口开始，把等待记录和其余记录联合
   `reassemble` 成完整 canonical taskmap，再联合 `RUabstract` 构造新前置。
   `CFentry_fixed` / `CFentry` **不调用 `RUentry` 或 `RUrules`**，不先假设新主规则成功。
   堆含 ready4、waiting6、readonly current、clock37、canary99、合法栈顶1。
2. `CFcore` 同时证实原共享 core 和完整补片可共存；`CFrules` 实例化新的泛化正式规则。
3. `CFmap_identity` 从真实抽象槽读出任务表身份；`CFreject_wrong_entry` 保持同一堆／控制／core，
   仅把 lookup 的优先级6换成7后拒绝。`CFwrong_lookup` 另核对错误 ready 状态。
   此处读取槽的 `Atrue` 投影只证明纯等式，绝不用于重造物理所有权。
4. 独立 pend7 字节堆：事件记录实际 pend7，而辅助 time 参数99不会替换它；
   时间记录的隐藏 pend 可选择0，但缺失字段补片仍为真实7。
   `CF_event_selected` / `CF_time_selected` 分别核对两条取值来源，`CFpend_load` 检查实际物理7。
5. `CFexecution_control` 在同一原真实迭代输出上检查到期 row80／group1、clock37、canary99及残余；
   保持全部物理输出与 END，仅中和抽象任务更新时仍由 task/ready 不一致拒绝。
   `CFcountdown` 核对 d=0／3，不误唤醒。这些路径**明确复用旧独立操作语义**，
   不是新 RuleSem 的运行测试，也不是删除版 AST 的执行实验。

前瞻协议：`audit/logs/stage164-tick-core-focus/protocol.json`。
所有失败编译快照与日志保留，早期技术失败不充当下游机制通过的证据。
结构测试红态仅反映新探针／验收材料尚不存在，不能当成行为消融。

## 实际验收

- 构建与清理后重建均退出0；稳定编译为 `focus04` / `probe10`。
- 新增生产9根、探针17根，共26根；334个活动模块与54个探针模块独立 `coqchk` 通过。
  检查期间543份 Coq 输入哈希保持不变，允许假设集合没有扩大。
- 新增7项回归通过。全套1979项，仍为旧423失败／1错误，完整旧 failure/error ID 集合保持；
  逐轮原始结果见本轮日志目录。不能把当前仓库称为全绿。
- `make audit` 的 project audit 通过，coverage audit 仍因旧 function evidence identity 过期退出2；
  `git diff --check` 仍仅报告旧 `framework/logic/inferules.v:581–586` 六行空白，退出2。
  没有改写旧冻结证据或删除失败使门变绿。
- 保留14次编译的全部源码快照与日志，其中10次非零结果，含 `probe09` 一次主动中断的符号计算。
  该中断后的修复只改成员关系证明：直接选择列表位置，避免对符号 pend 盲目展开 `Int.repr`；不改变命题。
- 确认 Coq 进程结束、逐项核对8个一次性目标后，清理687666字节，恢复两份既有缓存。
  源文件、旧失败、验证证据和可复用 Coq 产品均保留。
- 最终机器核对见 `audit/logs/stage164-tick-core-focus/verification.json`；旧文件基线为29028份。
  本步只允许说明文件前插、项目入口末尾追加与生成依赖更新，旧内容哈希逐一核对。

## 仍未完成的工作

- 本步限 IE=false 的单个未挂起等待节点；需要真实等待 lookup，不能把任意 core 或任意节点强行判为等待。
- canonical core 不拥有 Next 和所有链字段；补片仍须 caller 提供，没有声称已经从生产 IRQ 不变量借出。
- 非空 fixture 的当前任务不在该任务表，LocalInv 仍为旧空见证，不证明初始化可达。
- 尚未将共享 core 规则接到整条混合链／完整 tick／API／ISR；CPU hook 仍开放。
- 生产 Inv／LocalInv 安装、初始化／WFIFun／源码级 GOOD_OS 和同程序 K1–K4 尚未闭合。
- 六门仍为 94/1/1/1/1/0，本步无新增整函数信用；第一阶段未完成，uCOS3 未开始，总目标 active。

下一步应将整链循环的节点分类与共享 core 的取还组合起来，并使原 loop 的执行资源来自同一组共享见证。
不能继续把仅 caller 提供 raw 字段的 while 称为生产不变量已连接。
