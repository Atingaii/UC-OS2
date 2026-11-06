# 第137步：真实调度调用返回与目标交接

## 从哪处缺口继续

第136步证明的是内联两条选择赋值＋一条目标赋值，没有真实 call／return。这次不增加另一套调度模型，而是复用同一 ready Inv 和已有手工 AST，把原 `OS_SchedNew` 的实际函数调用接到同一个目标赋值。

固定目标仍为 V2.93.01、提交 `0c4a48e6fbc6e915714e816196619a5481accf0c` 与既有配置及两类授权修复。`Source/os_core.c` 中原 `OS_SchedNew` 的局部 `y`、两条赋值、返回，以及 `OS_Sched` 的调用与目标赋值均沿用原 AST；C／配置／AST／framework／tactics 不改。六项事前检查在 `audit/logs/stage137-ready-call-return/protocol.json`。失败编译及其源码快照保留，旧冻结证据不改。

## 稳定接口与内存事实

生产文件 `certiucos/v293/proofs/V293ReadySchedCall.v`：

- `V293_ready_sched_call` 接收实际程序中的函数绑定、全局变量绑定、lookup loads、同一 ready Inv 和 `GoodInvAsrt` caller frame。局部地址不是前提；由有界内存选出避开已用全局块的 fresh 块，实际分配局部字节。
- 初始字节确为 `Vundef`，不能套用要求旧值为合法 Tint8 的 owned-record 接口。`V293_ready_sched_raw_updates` 接收 raw mapsto，执行原第一次赋值建立合法字节，再执行第二次赋值；不增加初始化语句、不修改旧接口。
- 实际 `scall`、函数执行、局部分配、原两赋值、`sret`、`free` 和恢复 caller 环境都在同一 `cstepstar` 中。返回实际 `free Tint8 b Ms=Some Mf`、已释放地址为 None，且除 high 的一个字节外，其他全部地址与调用前逐地址相同。
- `V293_ready_dispatch_call` 是上层稳定入口：再组合原 `V293_OSSched_unlocked_prefix` 的目标赋值，构造 typed pointer store，保留同一 tasks／ready Inv，导出 `SWPRE` 及成员／非成员分支。不要求调用者提供最高任务、`AHprio` 或 scheduler 结论。

改变局部环境需要 `GoodInvAsrt R`：本接口不承诺保留依赖 caller 局部名字解析的任意断言。caller 环境本身确实保存和恢复。局部块由实际 fresh 分配得到，不把调用者现有局部单元冒充 callee 的新局部。

另一个明确边界：框架 `SWPRE` 分别存在量化 current／target 的 pointee type，而实际 `pswitch_step` 要求两者相同。复用的旧联合实例 current 为 `Tptr Tvoid`，target 为 `Tptr V293_tcb_type`；因此不能把这个实例直接当作实际切换实例。下一步必须在真实绑定处对齐类型并重新联合验证，不能凭 SWPRE 自动跳过此义务。

目标单元只作为调用前缀的 frame；**不把目标指针当作私有 frame 跨上下文切换保存**。本步没有 switch 执行。

## 同一完整调用前缀的联合检查

探针 `audit/probes/V293ReadySchedCallProbe.v` 在同一非空 ready＋waiting 内存上实例化生产接口；使用具体 `RCprogram` 真正把函数107绑定到原函数体，而不是留下可能不可满足的程序绑定前提。caller 的 `y` 仍绑定块90并持有99，callee 独立 fresh 分配。

`RCjoint_call_handoff_and_omission` 在一个定理中覆盖：

1. 共同前缀为完整实际调用返回：已实际释放 callee 局部、恢复同一 caller 环境、high=4、ready Inv 成立，旧 target 仍指向 waiting。
2. 正例追加原目标赋值，使目标实际指向 ready；给出实际 typed store、SWPRE 与同一 ready Inv。两种 current 分别得到 SWPRE_NDEAD／SWPRE_DEAD。
3. 单因素对照仅省略最后目标写入；不省略 callee 的返回或释放，不换 tasks／环境／Inv，证明 SWPRE 拒绝。正反内存在目标四字节之外完全相同。
4. caller 的旧局部 canary 在调用返回和最终状态实际 load 都仍为99；不是只证明全局结果正确。
5. `RCundef_not_typed_byte` 直接证明 raw Vundef 不可能满足旧 typed owned-record 前提，锁住桥接必要性，防止把未初始化值偷偷当已初始化字节。

这是无交错存在性执行和联合可满足实例，不是初始化可达性、所有交错、任意分配选择或全程序安全的证明。

## 验证与复现

实测以 `audit/logs/stage137-ready-call-return/checkpoint-report.json`、`verification.json`、`stable-compiles.json` 和冻结 manifest 为准。新增8项 Python 结构／身份回归不替代 Coq 语义证明。信任检查打印本步全部证明根，并对全部活动模块与历次附加探针运行 coqchk；不扩大框架假设白名单。

```sh
make build COQBIN=/data/home/lucentzhou/.opam/default/bin/
PYTHONDONTWRITEBYTECODE=1 python3 -B -m unittest discover -s tests -p test_ready_sched_call.py -v
PYTHONDONTWRITEBYTECODE=1 python3 -B audit/logs/stage137-ready-call-return/verify-checkpoint.py
```

实测11个证明根（生产6＋探针5）、303个活动模块与23个附加探针通过信任检查。实际假设仅 `Classical_Prop.classic` 与 `FunctionalExtensionality.functional_extensionality_dep`。全量1789项回归的完整失败 ID 集合与第136步逐项比较，旧423失败／1错误及 `make audit` 的 `stale function evidence input identity` 保留。六门仍94/1/1/1/1/0，不因一次局部完整调用就新增实际整函数可调用覆盖信用。最后先核对一次性目标再清理：仅删除本步 Trust 临时编译文件与缓存备份、恢复旧 lia／nia 缓存；保留源文件、可复用 Coq 产品及全部失败证据。

## 仍未完成与下一步

不是生产全局语义 Inv；仅已选 TCB 字段、有限就绪关系与空 LocalInv。完整池／链／事件、初始化建立、API／ISR 保持、Hook／栈、WFIFun、完整 OS_Sched 与实际 switch 均未闭合。手工 AST 也不是已验证 C 前端。

下一步把已建立的 SWPRE 接到框架真实切换步骤及其 continuation／共享资源边界，不让共享 target 作为私有 frame 穿过切换；随后仍须连接同一程序的初始化与各活动函数。最终 GOOD_OS／同程序 K1–K4 未完成，uCOS3 未开始，总目标 active；本步不提交／推送。
