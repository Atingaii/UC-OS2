# 第84步：OS_TCBInit 空闲链表为空时的框架函数体证明

## 这一步改变了什么

前一步第83步建立的是成功路径的**存在性调用轨迹**，并保留两个尚未兑现的 CPU Hook 契约。本步不把它包装成 Hoare 定理，而是直接使用框架推理规则，证明另一个尚未接入 Hoare 的实际分支：**空闲 TCB 链表为空时返回错误**。

生产文件：`certiucos/v293/proofs/V293TCBEmptyHoare.v`。

稳定接口：

- `V293_OS_TCBInit_empty_body_hoare`：`InfRules` 推导；
- `V293_OS_TCBInit_empty_body_semantics`：通过既有 `RuleSound` 得到 `RuleSem`。

两者的程序都是既有完整 `V293_TCBInit_function_body hi hc`，不是剪掉成功路径的替身。两个 Hook 调用仍保留在真实成功分支中；本分支不执行它们，也不需要 Hook 契约。

## 规格的精确范围

前置条件：

1. 函数体入口，`ptcb` 和 `cpu_sr` 两局部对象已经分配；其初值可任意，包括 `Vundef`。
2. 环境将现有三个变量名绑定到正确类型；全局 `OSTCBFreeList` 不被局部同名变量遮蔽。
3. 空闲链表头为 `NULL`，只需要其**只读权限**。
4. 入口中断**已经关闭**，临界区栈 `cs` 任意。
5. 其余资源 `R` 同时满足 `GoodFrm R` 和 `R ==> CurLINV li tid`。

证明按照实际语法依次完成：

| 步骤 | 证据 | 保持不变的部分 |
| --- | --- | --- |
| 初始化 `cpu_sr = 0` | `assign_rule` | 空闲头、原 `ptcb`、`R`、中断状态 |
| 进入临界区 | `encrit2_rule` | 中断仍关闭；向原 `cs` 压入 `false` |
| `ptcb = OSTCBFreeList` | 实际只读加载和 `assign_rule` | 链表头字节及权限、`cpu_sr=0`、`R` |
| 判定非空 | 真实表达式求值为整数0，`ift_rule` | 不以外部给定分支结果为前提 |
| 不可达成功路径 | 求值0与 `Aistrue` 矛盾，`pfalse_rule` | 不对其中 Hook 或发布代码授予成功信用 |
| 退出临界区 | `excrit2_rule` | 恢复原 `cs`，不是强行清空栈 |
| 返回错误 | `rete_rule` | 返回 `Some (Vint32 (Int.repr 66))`，保留全部资源 |

这里的语义接口是框架基于 `MethSimMod` 的 `RuleSem`：返回分支受返回值66的断言约束；本步没有另立总正确性或终止性定理，不把安全模拟解读为独立的终止保证。

返回断言仍拥有两个局部对象：`ptcb=NULL`、`cpu_sr=0`。**本步未把调用分配、返回释放、调用者恢复纳入这个 Hoare 定理**。第83步已有的调用轨迹不能替代尚未建立的框架调用连接。

## 非空前提、独立检查和负控

`audit/probes/V293TCBEmptyHoareProbe.v` 不导入任何旧探针。

- 字面内存是5个单元、17字节：两个4字节可写局部对象初值 `Vundef`、4字节只读空闲头 `NULL`、4字节只读当前任务指针、1字节值77的哨兵。
- 独立证明真实空间前置条件 `EmptyLiteralEntry`，对任意原临界区栈成立。
- 同时提供 `EmptyRGood` 和 `EmptyRCurLINV`，避免仅写一个可能不一致的局部不变量前提。
- `EmptyBodyChecked` 独立写出精确返回值与前后置，检查稳定接口类型。
- `EmptyBodyNoHook` 在完全无函数规格条目的 `EmptyNoHookSpec` 上实例化。本例只说明空闲头为空的分支不需要 Hook，不说明成功路径中的缺失 Hook 可执行。
- 正控使用 `exact EmptyBodyChecked`；负控**只将后置返回值66改为0，证明体完全相同**。计划先于控制编译写入。该控制只检查接口一致性，不等价于对全部错误规格的否证。
- `EmptyPostRejectZero` 从实际返回断言排除返回0；`EmptyGuardNotTrue` 独立排除成功守卫。守卫排除只授守卫信用，不证明后面的成功路径。

## 源码与信任边界

固定上游提交和两类授权修复不变。当前 `csrc/upstream/v2.93.01/checkout/Source/os_core.c` 第2022–2151行的函数哈希与冻结清单一致。函数不受两修复影响。完整修复／预处理目录的历史身份问题未在本步修复。

Coq 语法沿用现存手工变量重命名和既有临界区抽象，不是新建的已验证 C 翻译器。硬件、CPU 状态寄存器 token 的具体实现仍不属于这个源码抽象证明。

## 验证与未完成事项

详细命令、所有失败尝试、源码快照和结果见 `audit/logs/stage84-tcb-empty-hoare/`。最终验证状态以同目录 `final-report.json` 为准。

已完成增量构建和6项新增结构测试。`coqchk` 对全部250个活动模块和1个独立探针的内核复核通过；19个定理根的 `Print Assumptions` 联集仅含框架既有的 `Classical_Prop.classic`、`Eqdep.Eq_rect_eq.eq_rect_eq`、`FunctionalExtensionality.functional_extensionality_dep`，没有新增公理。全仓1400项测试仍为423失败、1错误；与第83步相比，424个诊断ID逐项相同，无删除或重分类。结构测试不代替 Coq 检查。默认 `make audit` 的工程检查通过，覆盖检查仍因旧函数证据输入身份过期退出2；旧框架行尾空白仍使 `git diff --check` 退出2。没有修改旧测试或冻结证据来制造全绿。

清理前对全部目标登记大小和SHA-256，并在首次删除前统一复核。本步仅删除22个一次性文件，共815373字节；保留生产构建产物、探针源、全部失败日志和源快照，原有 `.lia.cache`／`.nia.cache` 身份保持不变。清理后的增量构建通过；再次运行全仓1400项测试，仍为423失败、1错误，全部424个诊断ID与清理前及第83步逐项相同。

本步不增加“整个函数已验证”的覆盖信用：六门仍为 `94 / 1 / 1 / 1 / 1 / 0`。未证明启中断入口、成功路径 Hoare、CPU Hook 实现、`WFIFun`、完整 OSInit／启动／全局不变量、源码级整核 `GOOD_OS` 或同程序 K1–K4。uCOS3 尚未开始，整体目标保持 active。

下一项实质工作应继续补足真实成功路径的 Hoare 资源转换与显式 CPU Hook 规格连接，再形成可用于 `WFIFun` 的整函数契约；不能把本步错误分支当成整个 `OS_TCBInit` 已完成。

## 如何在仓库根目录复查

```bash
export COQBIN=/data/home/lucentzhou/.opam/default/bin/
make build COQBIN="$COQBIN" JOBS=2
"${COQBIN}coqc" -q -R . CertiOS audit/probes/V293TCBEmptyHoareProbe.v
"${COQBIN}coqchk" -R . CertiOS \
  CertiOS.certiucos.v293.proofs.V293TCBEmptyHoare \
  CertiOS.audit.probes.V293TCBEmptyHoareProbe
PYTHONDONTWRITEBYTECODE=1 python3 -B -m unittest discover \
  -s tests -p test_tcb_empty_hoare.py -v
```

以上是复查入口，不会覆盖本轮日志。负控源码保存在本轮 `Positive.v.snapshot.txt` 和 `WrongReturn.v.snapshot.txt`，失败日志没有删掉。首次实现有9次生产证明编译失败、5次探针编译失败；随后生产证明成功两次（第二次删除无用辅助引理），独立探针成功一次。所有17次编译均保留精确源快照，不将实现中的失败尝试当成预期负控。
