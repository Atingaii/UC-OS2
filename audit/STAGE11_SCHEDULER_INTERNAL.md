# 第十一阶段：调度器内部构造器与单函数环境

## 验证对象与不变项

继续验证冻结的 V2.93.01 `OS_SchedNew`，不改变 C 源码、固定配置、两份授权补丁、查表、函数体翻译或框架内存表示。源码身份仍为 `74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da`，不导入旧内核专用证明。

本次新增的是**内部函数构造器和参数化单函数 `WFFunEnv` 检查点**，不是已连接真实共享不变量的整函数覆盖，更不是 `GOOD_OS`。六门保持 `94 / 1 / 1 / 1 / 1 / 0`，调度器仍只记 `located`；只有 `OSVersion` 获得后续四门证据。

## 新增证明及接口

`certiucos/v293/proofs/V293OSSchedNewInternal.v`：

- 对外资源只含四个全局环境绑定、实际只读表／行／组字节、最高就绪优先级可写字节、`CurLINV li tid`、关闭中断状态及抽象操作。局部变量地址不进入 `funasrt`，并证明 `GoodFunAsrt`。
- 同一个规格表通过框架逻辑参数 `lg` 接收两行快照和抽象操作，不把行值固定在组件参数里。独立探针逐项检查合法分支的精确前后置；其他格式为 `Afalse`。
- `BuildPreI` 提供局部值／地址存在量词及准确局部定义域；由全局标识不同于 `y` 推出没有局部遮蔽，再接上上一阶段的函数体接口。局部旧值任意，不假定为零或 `Vundef`。
- 返回时将局部绑定和仍可写的字节重新组合成 `EX v, LV y @ Tint8 |-> v`，连同局部定义域交给真正的 `BuildRetI`，不丢弃仍分配的局部资源。

**这证明资源交接符合框架构造器，不是新增具体 alloc/free 执行轨迹。** 分配／释放的通用执行语义及 soundness 继续使用已修复框架。

稳定根如下：

| 接口 | 内容 |
| --- | --- |
| `V293_OSSchedNew_internal_contract` | 对任意包含准确函数体的程序表，连接实际 `BuildPreI`／`BuildRetI` 和 `InfRules` |
| `V293_OSSchedNew_WFFunEnv` | 非空单函数程序表与规格表的定义域、签名、局部声明及函数体规则一致 |
| `V293_OSSchedNew_internal_builders` | 空 C 参数时，两个构造器均确实返回 `Some` |
| `V293_OSSchedNew_internal_precondition_witness` | 存在实际状态满足构造器生成的整个入口前置 |

最后一个根位于 `V293OSSchedNewInternalWitness.v`，复用上阶段的有界分离内存：输入块 1／2／3，输出块 4，局部块 5，当前任务指针块 6；行值 `0/16`、组 `2`、候选优先级 `12`，中断关闭，局部环境恰好只有一个 `Tint8 y`。

见证中的空局部不变量只是可满足性夹具。主组件仍对任意满足 `GoodLInvAsrt` 的调用方不变量量化；该结构条件不等于已经建立真正的内核共享不变量。

## 验收协议（执行前确定）

新检查器 `scripts/v293-scheduler-internal.py` 在主函数门禁内运行。先在空目录从源构建全部活动文件，再编译独立重写的资源／规格选择器／函数类型探针，打印四个根的实际假设并检查依赖闭包。探针不从导出定理自动生成期望类型。

五项单因素控制保留同一 C、实际函数体、其它断言及证明步骤：

| 只改变一项 | 必须观察到的结果 |
| --- | --- |
| 删除准确局部定义域 | 在 `V293_sched_entry_context` 的环境桥接处拒绝 |
| 删除内部程序表入口 | 在 `V293_OSSchedNew_internal_domains` 的 `EqDom` 处拒绝 |
| 返回结果从 `None` 改成带值 | 在 `V293_sched_return_post` 处拒绝 |
| 契约增加 `False` 前提 | 隔离变异定理先编译成功，再由独立 `checked_internal_contract` 拒绝 |
| `fpre` 改成全 `Afalse` | 隔离变异选择器先编译成功，再由独立 `checked_pre_selector` 拒绝 |

后两项的隔离原版也必须先通过同一探针，不能利用删除下游定理本身制造失败。前三项检查错误行确实位于指定义务；所有变异先决的七个调度器模块必须成功。原调度器十五根／九项控制，以及 `OSVersion` 六根／四项控制全部保留并重跑，不用新检查替代旧门禁。

## 实际结果

Coq 8.18.0 正式门禁退出码为 0，排他新建 [function-evidence-stage11.json](function-evidence-stage11.json)，不覆盖历史记录。正向和变异检查使用本次从源重编的依赖，不复制工作区旧 `.vo`；门禁末尾重新确认全部绑定输入未改变。

| 检查 | 实测结果 |
| --- | --- |
| 空目录全量构建 | PASS；122 个文件，即 19 个 V293 文件和 103 个通用框架／工具文件 |
| 新增四根、独立接口／选择器、两个隔离原版及 `coqchk` | PASS |
| 新增五项单因素控制 | PASS；分别命中协议指定的义务 |
| 原调度器十五根／九项控制及 `OSVersion` 六根／四项控制 | 全部保留并通过 |
| Python 全套回归 | PASS；158 项，含真实 C 矩阵、11 项逐机制消融及新增 15 项内部证据反向测试 |
| 工程与六门覆盖审计 | PASS；覆盖不变 |
| 源码冻结重放 | PASS；94 个定义、16 个边界，源码身份不变 |
| 既有 C 证据重放比较 | PASS；实际重跑 368 次并与冻结 JSON 逐字比较 |
| 六文件小模型、三个无全局假设根及 `coqchk` | PASS；不授予函数覆盖 |

新增根实际假设并集为 `Classical_Prop.classic` 和 `FunctionalExtensionality.functional_extensionality_dep`，未扩大允许列表，不声称无公理。

正式 JSON 的 SHA-256 为 `01fc5c12d503b59876afb7dbce00dec6dac5c48bf329939f673d32c01f43b8bd`。`coverage.json` 仅更新 `OSVersion` 的报告路径与哈希，不改变阶段布尔值或函数定位；stage10 JSON 仍为原 SHA-256 `950dda6c7539e81ce35b9221947cae4769d4e166643a6bb864e968f7975fe3fb`。

C 矩阵通过表示符合既定预期：两项修复全部启用的 92 次执行通过，原版／单补丁版本的 112 次预期失败继续保留，不能将 368 次全部描述为内核行为通过。

可重放命令：

```sh
export COQBIN=/data/home/lucentzhou/.opam/default/bin/
export PYTHONDONTWRITEBYTECODE=1
make check-functions
make test
make audit
make source-freeze-check check-c-evidence check-models
```

`make check-functions` 实时重查，不覆写已发布报告；发布命令的 `--record` 排他新建。正式报告在 Git 中保留完整命令输出及身份，不依赖本机忽略日志才能审计。

## 失败记录与证明边界

首次本地入口见证使用 `vm_compute; auto` 后仍有就绪性的析取义务，改为在同一目标上用 `intuition lia` 完成；不改变夹具或断言。首次删除程序入口的变异在未使用参数的隐式类型推断处提前失败，门禁正确拒绝计作定义域证据；为同一程序表定义补显式 `fid`／`var` 参数类型后重跑，控制才到达预定 `EqDom` 义务。失败和成功日志均保留于本机忽略目录 `audit/logs/stage11/`，正式证据不从这些失败记录拼接。

尚缺真实 `OS_Sched` 关闭中断调用上下文、位图与 TCB／优先级表对应、完整符号布局、共享不变量、所有函数规格／组件、初始化以及最终 `GOOD_OS`。当前标识和块地址是参数，不是完整链接器结果；见证也不是所有内核状态的模拟。

下一步继续同一调度链，从真实调用方提供内部前置并连接实际任务关系。源码级 `GOOD_OS` 与同程序 K1–K4 未全部闭合前，不启动 uC/OS-III。总目标保持活动。

中文入门见[第十二课](../docs/阶段/12-内部函数构造器与WFFunEnv.md)。

## 清理记录

逐项确认后，仅删除本轮工作区一次性独立探针 `audit/logs/stage11/InternalContract.v` 及其 `.vo`／`.vos`／`.vok`／`.glob`／`.aux` 六项；所有验证日志和正式 JSON 保留。正式门禁和定向检查的任务专用目录由 `TemporaryDirectory` 自动清理，既有缓存、可复用 Coq 依赖、源文件、用户数据和凭据未删除。
