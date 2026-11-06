# 第178步：同一物理堆上的时间 API 调用者与强共享资源

## 这一步补什么

第177步已经证明原 `OSTimeGet / OSTimeSet` 的真实函数 builder 契约使用既有强 `V293_time_ready_inv`，但“契约存在”与“强 core 独立非空”不能推出二者能够同时分配。它们可能争用同一字节，或者各自依赖不兼容的名字和状态。

本步构造一个明确的联合堆，证明 **`strong core ** actual caller pre`**，不是两个独立状态的逻辑合取。不改变 C、配置、AST、框架、不变量、旧证明或已冻结证据。

## 生产接口与资源布局

新增 `certiucos/v293/proofs/V293TimeReadyEntry.v`：

- `V293_current_entry_context`：在 `OSTCBCur` 全局绑定不变的前提下，运输已有当前任务只读资源；不改变内存或抽象 map。
- `V293_time_ready_entry_context`：同样运输已有强 core；TCB／bitmap／priority-table payload 直接沿用已有上下文引理。
- **`V293_time_ready_entry_halves`**：从真实 `SWINVt` 拆出 `strong core ** CurTid t`。当前任务指针的两份只读半权限来自原全权限，不复制可写所有权；移除的 IRQ 标志本来就是零足迹。

探针 `audit/probes/V293TimeReadyEntryProbe.v` 在旧独立 TCB／ready／table／clock 堆上，加入两个互不相交的实际编码局部变量：

| 对象 | 物理位置 | 作用 |
| --- | --- | --- |
| OSTCBCur | block 1 | core 与 caller 各持兼容只读半权限 |
| ready row／group／priority table | blocks 80／81／82 | 保留既有实际字节与同一 taskmap 关系 |
| clock | block 150 | 既有强 core 的物理时间 |
| ticks 参数／临时槽 | block 160 | getter 任意 raw value，setter 必须等于传入 n |
| saved 槽 | block 161 | 任意 raw value，原函数会初始化 |

这些地址是审计 fixture 的固定符号地址，不是生产地址或启动初始化。`Jjoint_join` 和 `Jlocals_join` 分别证明实际内存可分离，`Jraw_joint` 建立一份完整空间断言。

`Jget_allocated_contract / Jset_allocated_contract` 对同一个精确 pre 同时核对真实 `BuildPreA'`、`BuildRetA'`、原完整 body 的 `InfRules`，以及联合堆上的空间满足关系。它们通过已有 builder 的 `Some` 等式识别 pre，不把 body 证明当成非空 oracle。

`Jconcrete_ready_entry` 选用实际在 `OwnershipTasks` 中优先级为4的 ready 任务，而不是 map 外的虚构当前任务；clock=37、ticks=42、saved=Vundef。getter与setter使用相同物理堆和抽象 map，但各自具有正确的不同 ghost action；不声称两个 action 在同一状态同时成立。

## 前瞻协议与单因素对照

协议在实现前锁定于日志目录 `protocol.json / protocol-identity.json`。

| 对照 | 保持不变 | 机器证明的结果 |
| --- | --- | --- |
| 联合正控 | 同一堆、同一任务 map、实际 locals 与名字 | getter／setter builder pre 与强 core 空间共存 |
| `Jclock_control` | caller action／pre、locals、全部非150块字节、旧抽象 clock | 只替换150块编码时间后 caller pre 仍可满足，强 core 由实际 load 与抽象时间不符而拒绝 |
| `Jsetter_slot_control` | 原参数 n、setter action、旧抽象 map、clock 和全部非160块字节 | 只替换160块参数值后强 core 仍可满足，固定 n 的 caller pre 由实际参数 load 拒绝 |
| `Jraw_getter_control` | 同一 getter builder 与共享资源 | 接纳 Vundef／Vundef，也接纳整数1／Vnull；不额外要求 raw locals 预初始化为0 |

两项负控分别证明另一个边界仍接受，不能把 clock 的早拒绝当作参数槽有效，或把参数拒绝当作共享资源有效。这里只构造并比较字节堆，不声称已经执行真实 store。getter 的 raw value 不要求能够作为 Tint32 表达式求值，原 body 会在读取返回局部值之前写入它。

## 明确不声称什么

- 上下文运输把名字／local env／IRQ aux／action换成 fixture 所需环境，**不是** `encrit / excrit` 或任何动态机器步骤。只证明已分配入口资源的可满足性。
- `strong core` 不是带全部 IRQ 标志的完整 `SWINV`。这里只给出调用者与共享物理／抽象资源的兼容布局，不据此宣称一个全局初始化状态有效。
- 不证明真实 API call 分配 locals，也不证明单条完整 call→body→return 运行轨迹；不能拼接独立 fixture 得到 trace。
- LocalInv仍为 name-only，不是所有生产私有资源。三API／内部调度器的同Spec组件证据沿用177，不自动安装 tick、hook 或 ISR。
- 完整函数环境、生产共享资源、初始化、同程序 K1–K4 和最终 `GOOD_OS` 仍开放。六门仍为94/1/1/1/1/0，第一阶段未完成，uCOS3未开始，总目标 active。

## 复核入口

日志目录：`audit/logs/stage178-time-ready-entry/`。`stable-compiles.json` 指向通过的源码快照；所有失败尝试也保留。`trust.json` 检查本步27根假设及两个入口的递归依赖，不冒充所有历史入口重检。新增5项 Python 回归检查来源锁定、空间布局、独立对照及稳定编译身份；文本形状检查不替代 Coq 语义证明。

实际构建、完整测试、原失败ID比较、旧文件哈希、清理与最后冻结结果以 `verification.json` 为准；不通过修改旧 coverage identity、删除失败或削弱检查门制造全绿。

下一步应把这一联合布局接到真实 API 调用分配／函数执行边界，并继续统一生产全局函数环境；本步已经消除“caller 与强 core 只有分别非空见证”的局部缺口，不能再重复计作新增成果。

## 本次已观测的结果

- 生产第3次与探针第14次编译通过，交付源码与对应快照完全一致。共17次编译，13次非零诊断全部保留，不将中间失败计为消融成功。
- 27根 `Print Assumptions` 和两个入口的递归 `coqchk` 通过，后者297.18秒；571份Coq输入在检查期间不变。实际仅用既有 classic 与 functional_extensionality_dep，允许假设集合不扩大。
- 新增5项回归全部通过。完整测试2048→2053项，保留旧423失败／1错误及完全相同的完整ID；本文定稿后还运行第二次全套，由最终 verification.json 再核对两次结果，不以文字代替原始记录。
- `make build`、项目范围审计通过。`make audit`仍是旧 stale function evidence input identity，`git diff --check`仍为inferules.v 581–586六行旧空白；本步新增源码和文档无行尾空白，不修改原有失败来制造通过。
- 清理前逐项列明本步Trust驱动及产物、原缓存备份、新测试的可再生Python缓存；恢复原lia／nia缓存，删除清单内一次性材料。保留所有交付源码、诊断、快照、原始日志及可复用Coq产物。结果由cleanup.json和最终证据清单确认。
- 未提交／推送，未授予新增无条件整函数覆盖，最终目标继续active。下一步不重复构造分别非空的资源，转向真实调用分配与生产环境连接。
