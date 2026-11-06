# 第170步：真实 tick 调用分配接入共享后缀入口

## 本步解决什么问题

第169步已经允许 `ptcb` 扫描槽为真正的 `Vundef`，但探针入口仍是手动构造的堆，不是一次真实函数调用分配出来的两个局部变量。本步连接这两段：

1. 从 caller 的 `scall tickfn nil` 开始。
2. 按原函数声明分配 `ptcb` 与 `cpu_sr`。
3. 执行原 `cpu_sr = 0`。
4. 到达真实 `scall OSTimeTickHook nil` 调用点。
5. 在**同一个分配后内存 `Ms`** 上得到第169步共享后缀的完整资源入口，且实际读取 `ptcb = Vundef`、`cpu_sr = 0`。

这里只到 hook 调用点，**尚未跨过 hook**。后缀入口资源此时已经就绪，不代表 hook 返回后仍然持有它；后者是下一步必须证明的调用契约。

## 固定对象与接口

固定版本、上游提交、配置和两类授权修复不变。`OSTimeTick` 精确位置仍为 `os_core.c:937–1008`，对应源码与配置后函数身份见 [source-identity.json](logs/stage170-tick-call-context/source-identity.json)。没有修改 C、配置、既有 AST、框架、策略或旧证明。

生产文件：`certiucos/v293/proofs/V293TimeTickCallContext.v`。

| 接口 | 结论 | 不是何种结论 |
| --- | --- | --- |
| `V293_tick_call_pack` | 重排新分配槽及原共享资源，得到现有后缀入口 | 不执行代码，不创建新不变量 |
| `V293_tick_call_shared_to_hook` | 构造真实调用／分配／初始化 trace，并在同一 `Ms` 给出完整入口与两个实际 load | 不执行 hook，不假设 hook 为 `skip` |
| `V293_tick_call_suffix_hoare` | 用原正式 `InfRules` 后缀证明，保留新增 `cpu_sr=0` 槽作为 frame | 不等于完整函数 Hoare，也未证明 raw CPU critical wrapper |

共享资源仍是同一个 `V293_time_ready_inv`，没有新 `Inv`、执行 oracle 或新公理。边界仍限制 `IE=false`、ISR clear、合法有限未挂起链及既有空 `LocalInv` 见证。

### callee 环境的关键区别

生产入口的资源前提明确在**最终 callee 环境**上评价，但其内存尚不含将分配的两个局部对象；操作 trace 则从 caller 环境开始。这是一个有边界的条件接口，不是“任意 caller 断言都能搬到 callee”的定理。

探针为这个前提提供独立实例：

- 旧扫描槽70仍是 caller 数据，初值为 idle 指针；新槽确实 fresh，为171和172。
- 不把旧 `PCbindings` 的 `ptcb→70` 运到新环境。先剥离旧绑定，将其资源归入 `Atrue`。
- 仅对已单独证明 `GoodFunAsrt` 的 `CCbare` 使用环境运输；环境敏感的断言不属于这个集合。
- 在新 callee 环境独立建立 `CCbindings`：`ptcb→171`，各全局标识不被 locals 遮蔽。
- 精确保留 canary90=99、原槽70、全链缺失字段、globals及其他具名 frame 资源。`Atrue` 不代替这些具体资源。

## 前瞻负控与独立入口

[protocol.json](logs/stage170-tick-call-context/protocol.json) 在实现前冻结，保持4组控件及原限制。

独立探针：`audit/probes/V293TimeTickCallContextProbe.v`。入口从既有四任务实际字节堆 `PCjoint` 构造，经 `SCpack → CCstrip → GoodFunAsrt` 环境运输及独立新绑定进入；不调用新的主连接定理或后缀 Hoare 来制造入口。随后才应用主接口执行真实 prefix。

| 检查 | 保持不变 | 单独变化／可观察结果 |
| --- | --- | --- |
| fresh locals | 原四任务、13项优先级表、readonly current、clock、globals、canary与旧槽70 | 实际分配171/172；到 hook 点 load scan 为 `Vundef`、saved 为0 |
| 错误 saved 见证 | 同一实际 `Ms`、抽象 map/code、共享不变量、scan、全部 frame | 只把完整入口 saved 见证0换成1，由实际 load 矛盾拒绝 |
| 错误旧绑定 | 同一实际 callee 环境 | 要求 `ptcb→70` 的局部绑定资源被拒绝；这是绑定资源负控，不夸大为完整错误 shared-frame 反例 |
| caller 资源 | 同一实际 prefix 端点及完整正确入口 | 实际读取 canary90=99、原槽70仍为 idle 指针 |
| 分支实例 | 原运行值范围与共享契约 | run=1、run=0/255以及最大clock入口均实例化 |

`CCsame_endpoint_controls` 把实际 trace、完整入口、两新槽、canary、原槽及错误 saved 拒绝放在同一 `Ms` 上，避免把不同执行端点拼成一个结果。负控拒绝直接来自 saved／环境绑定，不借助 bitmap 早拒冒充下游机制有效。

`CCprogram` 只定义真实 tick 函数，hook2002没有定义，因此其 trace 有意止于 hook 调用处。`CCwrap` 只证明最大clock时的 prefix 和入口，**没有在本步执行时钟回绕**；第169步旧回绕证据不冒充新执行。`CCsemantics` 是 `RuleSound` 从 `CCrules` 导出的后缀 `RuleSem`，不是独立全函数运行。

## 验证与失败证据

生产及完整探针分别编译通过，活动构建退出0。独立检查23个新增证明根、340活动＋60探针模块通过；555份 Coq 输入在检查期间保持不变。允许假设仍仅为既有 classical、Eq_rect_eq 和 functional extensionality，未扩大。

新增5项结构回归全部通过；全套2013项保留旧423失败／1错误，三轮完整失败与错误 ID 集合均同基线一致，清理后构建退出0；最终结果见 [verification.json](logs/stage170-tick-call-context/verification.json)。`make audit` 仍退出2：项目审计通过，coverage 仍报旧 `stale function evidence input identity`；`git diff --check` 仍只报旧 framework 第581–586行六项 whitespace。

逐项确认后，仅删除临时信任检查输入／产品和本步缓存备份，共8项689181字节；既有 `.lia.cache`、`.nia.cache` 按原哈希恢复，源码、全部失败快照／日志、信任日志及可复用 Coq 产品保留。旧27722份文件及第169步 manifest 的116项不可变证据逐项核对；根文档仅前插，`_CoqProject` 仅末尾追加。

全部15次编译快照和日志保留：3次生产、12次探针，其中12次非零均为普通 Coq 证明／API使用错误，没有将这些错误当作内核反例。第一次 shell 使用环境不存在的 `python` 返回127，未执行修改或构建，随后改用已有 `python3`；诊断单独记录。新增结构测试首次因独立信任报告尚未生成而出现1项错误，保留原日志，不将“报告未生成”描述为语义失败。

完整旧失败、源码身份审计失败和 framework 六行 whitespace 必须保持，不删改旧测试或降低门槛刷绿。结构测试只检查连接与证据身份，不能代替 `coqc` / `coqchk`。

## 对抗性复核与未完成工作

逐条检查见 [adversarial-review.json](logs/stage170-tick-call-context/adversarial-review.json)。本步只关闭“真实两 local 分配及 callee 环境能否接同一共享后缀入口”这个缺口，没有关闭：

- CPU hook 的实际调用契约、资源保持与返回；
- 原函数完整正式 Hoare、void 返回释放与统一函数上下文；
- 生产共享／局部不变量及 ISR 的安装与初始化可达性；
- 全程序 `WFIFun`、源码级 `GOOD_OS` 和同程序 K1–K4。

六门仍为 `94/1/1/1/1/0`，不给 `OSTimeTick` 增加整函数覆盖信用。第一阶段未完成，uCOS3未开始；总目标保持 active，不提交／推送。
