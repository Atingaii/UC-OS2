# 第116步：把真实取出的私有 TCB 接到原18个字段写入

## 本步改变了什么

第115步已经从共享空闲链取出一个完整56字节 TCB，并在退出临界区时向同一不变量归还剩余链。本步继续证明原来的18个字段赋值，不要求调用者预先提供“旧字段快照”，也不把初始化后的节点当作前提。

通俗地说：上一步拿到了真实空白任务控制块，这一步把任务栈、优先级、状态和等待信息写进去。共享链头已经归还，不会再作为写字段时的私有资源。

## 生产接口

文件：`certiucos/v293/proofs/V293TCBAllocatedFields.v`。

- `V293_tcb_allocated_payload_open` 从实际拥有的类型化 payload 中打开18个旧值，构造内部存在量词 `old`；旧值不是外部 oracle 或快照前提。
- `V293_tcb_allocated_inputs` 只持七个真实参数单元及绑定和调用者 frame；ptcb、CPU 局部单元仍由原启用状态统一管理，不重复持有。
- `V293_tcb_allocated_fields` 接入既有 `V293_OS_TCBInit_fields_hoare`，在原字段 AST 上证明全部18次写入。参数类型有效、优先级小于13、地址不回绕及局部不变量保持仍是明确的前置条件。
- `V293_tcb_free_pop_fields` 闭合原右结合的 `pop; excrit1; fields` 片段，同一个 Inv 接受归还后的尾链。该定理声明只有一个 `InfRules`，没有字段执行、load 结果或成功后缀的证明前提。
- 供上层使用的稳定整函数体接口是 `V293_OS_TCBInit_free_body_after_fields`。它复用第115步原函数前缀与空池返回66证明，把非空分支的剩余 `InfRules` 前提推进到 **全部字段初始化之后的 Hook／成功后缀**。
- **整函数体接口仍是条件组合定理，不是非空成功返回0、标准整函数契约或 `WFIFun`**。不能因为字段前提消去了，就把尚未证明的 Hook／发布／return0 算作完成。

没有修改 C、配置或 AST。准确源码仍是固定版本 `os_core.c` 的 `OS_TCBInit`（2022–2151行）；字段段从2050行开始。函数切片与模型哈希由 `source-identity-check.json` 核对。本步没有重放历史逻辑修复目录。

## 56字节资源如何分配

18个被写字段的起始偏移为：`0, 50, 48, 49, 44, 4, 12, 8, 16, 18, 55, 52, 51, 54, 53, 28, 36, 32`。具体类型和最终值复用原 `V293_tcb_init_final_fields`，不另造初始化模型。

剩余资源沿分离 frame 保留：

| 未在该段写入的部分 | 偏移／宽度 | 保留方式 |
| --- | --- | --- |
| Next | 20／4字节 | 完整 typed cell，显式保留取出时的后继值 |
| Prev | 24／4字节 | 原 `V293_storage` 类型化单元 |
| flags-ready | 40／2字节 | 原 `V293_storage` 类型化单元 |
| 填充 | 42、43／各1字节 | 原 `V293_storage` 单元 |
| 调用者资源 | 节点外 | 原参数、CPU、局部绑定及 R 的分离 frame |

这些资源没有被字段段消费；但 storage 谓词对值作存在抽象，本步**不额外声称已在后置条件中建立 Prev 等旧值的显式相等关系**。共享 head 字节不在字段 frame 中；保留全局名字绑定不等于私有持有 head 内存。

## 排除不可满足前提

探针：`audit/probes/V293TCBAllocatedFieldsProbe.v`，只用于审计，不进入生产依赖。它明确复用冻结的第115步 `V293TCBFreePoolProbe` 字面堆与唯一 `FPInv`，不是第二个生产不变量。

- 七个参数单元201–207实际编码到堆；优先级5，栈顶／底指针701／702，identity11，size64，extNULL，options0。
- `AFWholeEnabledLiteral` 给出 CPU 初值99、ptcb未定的 IE=true 完整入口，与原双节点共享池共存。
- `AFActualPopInput` 给出真实双节点临界区输入；`AFPopFieldsChecked` 在同一个 `FPInv` 上实例化闭合的弹出／退出／字段片段。
- `AFPrivateFieldsSpatial` 给出取出节点501、Next为502、完整参数和调用者资源的非空私有字段输入。
- `AFCallerNoShared` 证明原调用者没有401、501、502的共享字节；`AFPrivateNoSharedHead` 证明拿到私有节点后仍不持有共享head401。

这些是可满足的局部内存实例，不是从生产初始化到该入口的可达性证明。池上界13及测试用空局部不变量的局限沿用第115步；未建立全局已用／空闲节点全集、优先级表与就绪位图关系。

## 前瞻单因素消融

实现前 `protocol.json` 固定省略 priority store 的检查。首次变体运行之前，`controls-plan.json` 进一步固定：同一 `AFFieldsInput`、同一满足的空间前提、同一地址501+50与 Tint8 类型、实际旧优先级0／输入参数5、同一期待读回5。两份检查源只允许 `Action` 一行不同：

1. 执行该物理字段 store 后读取5；
2. 省略该 store，保持其他内容不变，仍期待读取5。

两份源均先检查 `AFPrivateFieldsSpatial` 和两个真实读取结果，输出 `COMMON_INPUT_CHECKED` 后才检查结果。`AFOmittedPriorityDiffers` 另行正向证明未写时仍为0、不等于5；不单凭编译失败推断语义错误。

该对照仅隔离一次物理字段写入，**不是完整18写入变异体、整个 API 或中断交错的消融**，也不证明 Hook／发布有效。

## 验证与当前状态

最终实测以 `audit/logs/stage116-tcb-allocated-fields/checkpoint-report.json`、编译日志、`trust.json` 和冻结清单为准。失败诊断快照保留，不覆盖、不改写旧冻结材料。

实测：生产证明251行／9个证明根，探针280行／21个证明根；稳定编译为 `proof09`、`probe11`。30个根的假设闭包仅有既有 `Classical_Prop.classic` 和 `functional_extensionality_dep`。282个活动模块及新增探针（含其复用的旧探针依赖）由 `coqchk` 检查通过，耗时406.84秒。没有新增项目公理。

清理前和清理后 `make build` 都通过，是增量构建，不冒充全新干净构建。保留1410个生产产品，其中原1405个产品哈希全部不变；新增／旧探针产品各5个均保留。一次性文件先记录路径、大小和哈希并全部核对，再删除15个文件、111008字节；旧算术缓存已恢复，未删除既有文件。清单见 `cleanup-inventory.json`。

`make audit` 仍因旧函数证据身份过期退出2；`git diff --check` 仍报告既有框架六行空白，输出与第115步相同。这些不是本步修复结果，保留失败状态。根 README／状态页仅前置本步说明，历史后缀逐字节保留。

新增结构测试首次误把复用已证明命题的语法限定为 `apply`，实际闭合证明使用 `rewrite ... by exact B`，因此首次新增测试为8通过／1失败，首次全量多出该一项失败（1608／424／1）。保留该源快照、日志和 `test-diagnostic.json`；修正为检查实际带同一前提的精确 rewrite 后，新增9项在清理前后均通过，清理前复跑和清理后全量均为1608／423／1，失败／错误ID与第115步一致。未改变 Coq 语义输入、预期或任何覆盖门槛。

## 下一步

从本步初始化后的私有节点开始接原 Hook 调用、共享任务列表／优先级表／就绪集合发布和 return0，再接回任务创建预留所有权。统一生产 Inv、标准函数环境、初始化、源码级 `GOOD_OS` 及同程序 K1–K4 仍开放。阶段一未完成，六门94／1／1／1／1／0不变，uCOS3未开始，总目标 active。未提交／未推送。
