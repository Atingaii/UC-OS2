# 第190步：OSIntExit 的临界调用改为任务／逻辑参数索引

## 这一步解决什么

上一轮虽然接通真实函数构造器，但内部临界调用规格只接受一个固定 owner 和空逻辑参数。把同一条规格放入全局函数表后，它不能自然服务其他任务。这不是改一个名称就能解决的问题：任务和逻辑参数必须参与资源解释，而且仍须通过框架真实调用规则。

本步新增 `certiucos/v293/proofs/V293OSIntExitIndexedPort.v`。一个 `fpre/fpost` 接受 `list logicvar -> tid -> addrval -> asrt` 资源族，调用方通过已有的 `logicl` 传逻辑参数，调用任务来自真实 `tid`，指针来自真实 `&saved` 的求值与类型证明。没有新造调用语义、替换原 AST 或假装已实现端口。

## 已接通的最小证明链

稳定上层接口为 `V293_OSIntExit_indexed_builder_contract`：

1. 用第189步真实原函数查询和 `BuildPreI/BuildRetI` 识别入口与返回断言。
2. 从局部 domain 和资源中取出存在的 saved 地址与任意旧值，推导不遮蔽。
3. 完整原函数体证明执行 saved 初始化、真实 running 守卫、索引临界调用、中段、出口调用和返回。
4. 中段直接复用第187步 `V293_OSIntExit_middle_bridge`；没有把整个中段或整个启用分支作为输入前提。
5. 返回重新包装同一局部单元和完整 domain，使用原返回构造器。

`V293_indexed_pointer_call` 使用实际 `call_rule`，保留 caller 的局部绑定／frame，callee 只持有其资源族。桥接／body／builder 逐层保持索引，不再要求固定 owner 或 `lg=[]`。

## 显式开放义务

泛型接口仍要求运行时资源族的四个特化等式：entry、acquired、leaving、restored 必须分别等于原 OSIntExit 各处真实需要的资源。**没有声称已经找到统一生产编码器、全部逻辑参数的资源关系或生产端口实现。**

唯一语句级残余仍是启用且不同优先级时的真实 `scall int_switch nil`。它对所有内部 saved block 量化，保留局部 domain／caller frame，counter 已为 `Int.add c Int.one`。不能把这里的条件契约误记为 `WFFunEnv` 或整核 `GOOD_OS`。

不运行时三个 lookup 和四个特化等式均被 `run=1` 守卫保护。主接口仍保留统一的调度数值／ready/table 条件；本步没有宣称它是非运行路径的最弱规格。第189步专用非运行接口仍可使用。

## 事先固定的协议与独立对照

协议先冻结在 `audit/logs/stage190-interrupt-indexed-port/protocol.json`。探针为 `audit/probes/V293OSIntExitIndexedPortProbe.v`；复用第189步物理构造辅助项，但正确资源由编码内存与分离连接独立构造，未把待证断言或整个函数正确性作为 oracle。

| 对照 | 保持不变 | 可得结论与边界 |
| --- | --- | --- |
| 同一 `IPspec` 的任务7／9、非空逻辑参数 | 同一函数201的查找条目和调用规则 | `IPtwo_tasks_one_spec` 对任意任务和值成立；具体两组入口非空。两组同时改变任务和值，不能单独当作单因素实验 |
| 仅改所请求的任务7→9 | 同一物理堆、逻辑参数0、saved 地址和值 | 同一查找仍成功，但真实当前任务指针 load 排除错误任务，不靠查找早拒 |
| 仅改逻辑参数0→1 | 同一任务7、同一物理堆、saved 地址15和值0 | 实际 saved load 排除错误解释 |
| 仅改物理 saved 值0→1 | 同一任务7、逻辑参数0、环境和地址 | load 排除错误值；另外证明15号块外每个字节不变 |
| 仅改物理当前任务指针 | saved 值和其他内存块 | 6号块外每个字节保持；与错误任务索引控制区分 |
| 旧 fixed-owner／空-lg 规格 | 旧规格定义原样保留 | 分别拒绝其他任务或非空逻辑参数，仅是输入层对照，不能证明调度或端口行为 |
| 运行中的完整原 builder | 固定单 idle 任务；非空逻辑参数携带任意 counter `c` | `IPrunning_builder` 从真实 builder 接完整原 body，嵌套2→1；`IPrunning_pre_nonempty` 独立构造任意 `c`／saved 旧值的入口，排除空前置的假通过 |
| 非运行完整 builder，所有 lookup 为 None | 同一原函数与资源族；lg=nil 在这些族中为 Afalse | `IPnot_running_builder` 仍闭合，表明未使用不可满足的 callee 特化等式 |

运行 fixture 的嵌套2→1使调度／switch 分支不可达。它**没有实际覆盖启用调度或不同优先级切换**；泛型定理仍直接复用已证明的中段并保留真实切换义务。资源非空、前后快照和 Hoare 推导不是调用／分配／释放执行 trace；空 LocalInv 不是生产 ISR 不变式。

## 验证与保留的失败

本步两入口共29个引理／定理根，逐根 `Print Assumptions`，并用 `coqchk` 递归检查依赖；只允许既有信任白名单。稳定编译输入身份见 `stable-compiles.json`，最终结果见 `trust.json`、`verification.json` 和证据清单。

所有编译尝试的源码快照、日志和 JSON 均保留。一次对合并内存整体 `vm_compute` 的编译过慢而被停止，exit=-15 和终止说明保留；最终改为独立物理资源构造、通用 load 引理与冲突比较，没有改变控制目标或降低门槛。其他编译失败是语法、导入和引理实例化问题，不掩盖为成功。新增结构测试曾误把 `apply` 限定成 `eapply`；保留失败测试快照／日志，修正为接受两种实际引理应用语法，未更改证明结论或旧测试。

新增6项结构／身份回归；语义结论来自上述 Coq 根，不来自字符串测试。两轮全量测试各2114项，保留基线423失败／1错误的全部有序 ID。构建、project audit、旧 stale-evidence 的 make audit 失败与旧 inferules.v 空白失败分别记录，不把局部检查点说成全仓通过。

复核入口：

```bash
make build COQBIN=/data/home/lucentzhou/.opam/default/bin/
python3 -m unittest discover -s tests -p 'test_interrupt_indexed_port.py' -v
python3 audit/logs/stage190-interrupt-indexed-port/recheck-checkpoint.py
```

## 接下来的真实缺口

先确定可供真实生产临界实现使用的索引资源编码／关系，消除四个特化等式的生产实例义务，并接通同一 Spec 的全任务环境；不是继续增加互不相干的固定任务示例。然后连接真实 `OSIntCtxSw`、生产 ISR/LocalInv、初始化／完整环境与全交错 simulation。实际局部分配／释放语义也未由本步新增。

覆盖仍为 `94/1/1/1/1/0`，`WFFunEnv`、源码级 `GOOD_OS` 和同程序 K1–K4 未完成。总目标 active；uCOS3 未启动，待阶段一完整完成后按老师附件继续。没有提交或推送；源码、配置、原 AST、旧证明和冻结证据保持。
