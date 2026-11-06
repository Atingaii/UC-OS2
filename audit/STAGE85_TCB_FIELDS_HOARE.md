# 第85步：成功路径的18次真实字段写入接入 Hoare

## 从哪里继续，实际补上了什么

第84步只把空闲链表为空的错误分支接入框架；第83步的成功调用链仍是带两个未兑现 CPU Hook 契约的存在性执行轨迹。二者都不能代替成功路径的 `InfRules` 证明。

本步直接对既有 `V293_TCBInit_fields` 的18次真实 `sassign` 使用 `assign_rule`，再用 `seq_rule` 顺序组合。新增生产文件是 `certiucos/v293/proofs/V293TCBFieldsHoare.v`，稳定接口为：

| 接口 | 实际结论 |
| --- | --- |
| `V293_OS_TCBInit_fields_hoare` | 18次字段写入的 `InfRules`；任意旧字段值变为精确初始化值 |
| `V293_OS_TCBInit_fields_semantics` | 对同一程序及前后置，经既有 `RuleSound` 得到 `RuleSem` |
| `V293_OS_TCBInit_fields_records_hoare` | 同一组实际写入的资源后果：保留全部旧任务记录，建立新 ready 记录，保留11个剩余字段和全部输入 |

这不是把“存在一次正确执行”作为前提再包装成 Hoare。稳定接口不要求调用者提供求值结论、执行轨迹或该程序的另一份 Hoare 证明。内部通用赋值引理的求值义务，在18处具体写入中由实际环境和空间字节资源逐一兑现。

## 前后置条件：哪些东西已经在入口准备好

1. 已有8个局部绑定及输入单元：`ptcb`、优先级、栈顶、栈底、id、栈大小、扩展指针、选项。**本步不分配这些对象，也不执行空闲链表弹出。**
2. 调用者拥有18个目标字段，原值任意，包括 `Vundef`。这些字段共44字节，不是完整56字节 TCB 所有权。
3. 优先级满足当前固定模型的 `p < 13`；TCB 基址非负，`base + 55 <= Int.max_unsigned`。6个非优先级参数满足现有的类型有效性条件。
4. 空间帧 `R` 提供 `CurLINV`；真实分离资源要求各可写区域与其余帧不重叠。定理不要求把全局启动不变量作为已证明事实。
5. 任务记录版本额外要求新 TCB 的任务标识不在原 `tasks` 中，并实际持有全部旧任务记录。

结果精确保留输入单元、绑定、帧和抽象操作。对于两个位图掩码，先真实写入坐标字段，再从刚写入的字段读取坐标、求移位结果、写入掩码；不是把最终掩码作为外部前提给定。

任务记录版本把七个已初始化字段组合成新 ready 记录，其余11字段继续保留；原任务映射中的所有记录作为帧保留。后置里的 `set tasks ...` 是**规格参数的资源组合**，不是已经执行了框架抽象状态 `O` 中的一次任务映射更新，更不是已完成发布。

## 前提不是空的：两个独立字节实例

`audit/probes/V293TCBFieldsHoareProbe.v` 不导入任何旧探针模块。它独立列出字面字段与最终值，证明真实编码内存中的分离资源，不只是列出若干不相干的 load。

- 基础实例：28个单元、74字节。18个新字段全部为 `Vundef`，8个输入共25字节，另有只读当前任务指针和值77的哨兵。具体新任务优先级11，坐标为1和3，掩码为2和8。
- 记录实例：35个单元、84字节。在同一份内存增加一个优先级12的已有 ready 任务；它与待初始化 TCB 使用同一 block、不同 offset。入口同时持有旧记录、新字段、输入、绑定、局部不变量和哨兵；新任务 fresh 条件也单独证明。
- `FieldsChecked` 和 `RecordsChecked` 独立写出精确接口；`FieldsLiteralEntry` 和 `RecordsLiteralEntry` 证明这些接口的联合前提有实际实例。
- 字面实例的中断状态为关闭、原临界区栈任意；这不是整套启动 `Inv` 的非空性证明。生产字段定理只要求相应 `CurLINV` 帧，不把实例的具体中断状态泛化成整函数入口保证。

## 控制与不利结果全部保留

前瞻协议在首次证明编译前写入，原文未事后改写。它还计划了真实 prefix 连接，**该项本步没有交付**：只完成18字段 Hoare 及任务记录资源连接，空闲链表 pop／临界区退出的 Hoare 连接仍是下一项工作。

控制只改变一个因素：后置中目标字段的优先级11改为10，程序、前置、其他字段、输入及证明体 `Proof. exact FieldsChecked. Qed.` 全部不变。有效正控 `Positive02` 编译通过，`WrongPriority02` 在接口类型不统一处被拒绝。

第一组控制都因缺少 `V293_byteval` 导入而失败，**不能当作有效负控**。原计划、源码快照和两个失败日志原样保留；统一修正导入后，另写前瞻计划再运行第二组。上述控制只检查接口一致性，不证明任意错误实现都会被拒绝。另有 `FieldsPriorityRead` 从真实空间后置导出读11，`FieldsWrongPriorityRead` 排除读10；也不因此授予 Hook 或发布步骤信用。

生产证明与探针共25次编译，其中18次实现失败；最终生产证明为 `proof17`，最终探针为 `probe08`。4次控制编译单独计数，其中最初2次是基础设施失败，第二组包含1次正控成功及1次预期拒绝。所有日志和精确源码快照均保留。新增结构测试初次误把掩码写入索引写成5/6而非13/14；失败日志及原测试快照保留，按真实语法修正索引，没有删除检查或放宽期望。

## 源码、信任与最终核验

固定 V2.93.01 提交和两类授权修复不变。此函数沿用既有手工 Coq 语法、变量重命名及临界区抽象；`os_core.c` 第2022–2151行的文件及函数行哈希与冻结身份一致。字段段来自该函数第2049–2101行的选定配置。本步没有建立一个已验证 C 翻译器，也没有修复完整预处理树的历史身份问题。

所有命令及最终结果在 `audit/logs/stage85-tcb-fields-hoare/`；以 `final-report.json` 和只读核验为交付依据：

- 251个活动源文件增量构建通过，148个属于当前目标、103个属于通用框架／tactics。不是 cold build；`make build` 未重新编译 Coq 模块，因为已直接编译新模块。
- 6项新增结构检查通过；它们不代替 Coq 内核检查。
- 全部251个活动模块及1个独立探针的 `coqchk` 通过。28个定理根的 `Print Assumptions` 联集只有框架既有三项：`Classical_Prop.classic`、`Eqdep.Eq_rect_eq.eq_rect_eq`、`FunctionalExtensionality.functional_extensionality_dep`。
- 全仓1406项测试仍为423失败、1错误；与第84步的424个旧诊断 ID 按原序逐项相同，没有删除、重分类或增加诊断。
- 默认 `make audit` 的工程检查通过，覆盖检查仍因旧函数证据输入身份过期退出2。`git diff --check` 仍因既有 `framework/logic/inferules.v` 行尾空白退出2；本步不修改旧框架来掩盖该结果。
- 清理前逐个登记一次性文件的大小和 SHA-256，并在首次删除前统一复核；仅删除28个本步一次性文件、共1456779字节，逐项清单见 `cleanup.json`。保留生产产物、探针源、全部失败日志／源码快照，恢复原 `.lia.cache`／`.nia.cache` 身份。清理后再次增量构建及全仓测试，诊断与清理前一致。
- 第84步1250个生产产物与其余冻结证据保持原身份；未提交、未推送。

## 仍然没完成什么，下一步怎么做

**本步程序边界从18字段初始化段开始，在首个 CPU Hook 前结束。** 不包含真实 prefix、free-list pop、临界区退出、两个 Hook、优先级表和链表发布、return/free。没有整函数 `WFIFun`，没有独立总正确性或终止保证。

下一步应先把真实非空分支的空闲链表 pop 与临界区退出按框架规则接入本步入口，保留同一帧；随后兑现或明确链接两个 CPU Hook 的真实规格，再连接发布及返回，形成可被 `WFIFun` 使用的整函数接口。不能直接把第83步的存在轨迹拿来当这些 Hoare 子证明。

六门仍是 `94 / 1 / 1 / 1 / 1 / 0`，整核源码级 `GOOD_OS` 及同程序 K1–K4 尚未完成，uCOS3 未开始；总体目标保持 active。

## 复查入口

```bash
export COQBIN=/data/home/lucentzhou/.opam/default/bin/
make build COQBIN="$COQBIN" JOBS=2
"${COQBIN}coqc" -q -R . CertiOS audit/probes/V293TCBFieldsHoareProbe.v
"${COQBIN}coqchk" -R . CertiOS \
  CertiOS.certiucos.v293.proofs.V293TCBFieldsHoare \
  CertiOS.audit.probes.V293TCBFieldsHoareProbe
PYTHONDONTWRITEBYTECODE=1 python3 -B -m unittest discover \
  -s tests -p test_tcb_fields_hoare.py -v
```

以上复查不会覆盖本轮记录，但会生成探针临时编译产物；不应重新运行本步 `finalize.py` 改写冻结证据。两个有效控制源码可从 `Positive02.v.snapshot.txt` 和 `WrongPriority02.v.snapshot.txt` 复现。
