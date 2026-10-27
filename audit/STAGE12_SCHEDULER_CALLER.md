# 第十二阶段：调度器调用规则与真实任务指针读取

## 对象与范围

继续冻结的 V2.93.01 调度链，不改 C、配置、两份授权补丁、框架或历史 JSON。冻结身份仍为 `74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da`。

本阶段是**内部调用规则与目标指针读取的检查点**。虽然准确翻译了 `OS_Sched` 未锁定分支的前两句，但尚未组合成两句的 Hoare，更不是完整 `OS_Sched` 或 `GOOD_OS`。两个函数均不获得新的六门覆盖；覆盖保持 `94 / 1 / 1 / 1 / 1 / 0`。

## 源码对应

- `OS_Sched`：`Source/os_core.c` 第 1702–1732 行。
- 源文件 SHA-256：`96eef5dc1a519887499cffd8f9a6c8873b96978ed9646c42e52eb6992422fea5`。
- 配置后函数体 SHA-256：`4bbf6819f5a458dfdadb30dbc8aeaad5156553b98f1b6466d4b89054cbd965e9`。
- 重放冻结修复与配置，分别用 GCC／Clang 预处理，再由 Clang 解析。
- 手写预期的整个调用方 AST，核对声明身份、保存令牌的取地址、两层 guard、两句顺序、13 项指针数组、计数器后缀自增和切换／退出调用。
- 只发射 `OS_SchedNew();` 与 `OSTCBHighRdy = OSTCBPrioTbl[OSPrioHighRdy];`；用逐字比较绑定提交的 CoqImp 代码。整个函数 AST 检查不等于整个函数翻译或证明。
- 前端与受限发射器仍属显式受信任工具，不声称 C 编译器正确性。

## 五个稳定根

| 根定理 | 实际结论 |
| --- | --- |
| `V293_OSSchedNew_call_rule` | 在准确规格查找、任意合格 frame 和局部不变量条件下，应用框架真实 `call_rule`；不向调用方泄露 callee 局部地址 |
| `V293_ready_selection_task` | 全称位图／任务成员与任务／表项关系推出实际就绪任务、表项相等与最高优先级 |
| `V293_scheduler_good` | 此任务表调度谓词满足框架 `GoodSched`，不额外声称任意状态存在任务或唯一性 |
| `V293_OSSched_target_task` | 从同状态的指针表空间资源、抽象 TCB 表及优先级字节实际读取 TCB 指针，结果满足该状态的调度谓词 |
| `V293_OSSched_target_precondition_witness` | 构造 13 项物理指针表、独立优先级字节与抽象任务表，证明整个目标读取前置可满足 |

`V293_bitmap_tasks` 与 `V293_priority_table` 是未来共享不变量必须建立和保持的**全称关系**，不是选中结果 oracle。本轮未证明它们在所有 C 更新后保持，未完成真实 TCB 的独立挂起／等待状态对应。指针元素 4 字节，但不解引用 TCB 字段，指向类型保持参数化。

## 预先固定的单因素控制

其余源码、规格、框架和探针保持不变；每项必须命中指定义务，不能仅因早期输入身份失败而算检验成功。

| 改变 | 指定结果 |
| --- | --- |
| 位图成员关系改为 `True` | `V293_ready_selection_task` 拒绝 |
| 表项指针相等关系改为 `True` | `V293_ready_selection_task` 拒绝 |
| 仅空间资源步长 4 → 1 | `V293_read_pointers_load` 拒绝 |
| 调用定理额外增加 `False` | 所有新增模块先编译，独立 `checked_call` 拒绝 |
| 目标读取定理额外增加 `False` | 所有新增模块先编译，独立 `checked_target` 拒绝 |

两个空洞前提控制没有编译依赖该变异根的额外下游组合证明；原版用完全相同的模块和探针先通过。新探针另写位图关系、表项关系、最高就绪定义、空间资源步长及完整导出接口，不从被检验 `.v` 动态生成预期类型。

## 正式验收

Coq 8.18.0 正式门禁退出码为 0，排他新建 [function-evidence-stage12.json](function-evidence-stage12.json)。所有正向证明、探针与变异使用本次空目录构建的依赖，不使用工作区旧 `.vo`；结束时重新检查全部绑定输入未改变。

| 检查 | 实测结果 |
| --- | --- |
| 空目录全量构建 | PASS；127 个文件，即 24 个 V293 文件与 103 个通用框架／工具文件 |
| 新增五根、独立接口、目标读取前置见证与依赖闭包 `coqchk` | PASS |
| 新增五项指定单因素控制 | PASS；删除关系、改变步长各命中指定证明；两个空洞前提变异全部先编译，再被独立接口拒绝 |
| 既有调度器十五根／九项控制、内部组件四根／五项控制、`OSVersion` 六根／四项控制 | 全部保留并通过 |
| Python 全套回归 | PASS；191 项，包含新增 19 项调用方 AST／引用身份测试与 14 项证据反向测试 |
| 工程与六门覆盖审计 | PASS；`94 / 1 / 1 / 1 / 1 / 0` |
| 源码冻结重放 | PASS；94 个定义、16 个边界，源码身份不变 |
| 既有 C 证据重放比较 | PASS；368 次实际执行与冻结 JSON 一致，包括原版及单补丁版本的预期失败；不是 368 次内核行为都通过 |
| 六文件小模型、三个无全局假设根与 `coqchk` | PASS；不授予函数覆盖 |

五个新增根的实际假设并集为 `Classical_Prop.classic` 与 `FunctionalExtensionality.functional_extensionality_dep`，未扩大允许列表，不声称无公理。

正式 JSON 的 SHA-256 为 `54d40d85e500fd4b9ea3e468d271b7fdc03dc3bbca9073baed516826dea9639c`。`coverage.json` 仅更新 `OSVersion` 证据路径和哈希，未改变任何函数定位或六门布尔值。stage11 JSON 保留原 SHA-256 `01fc5c12d503b59876afb7dbce00dec6dac5c48bf329939f673d32c01f43b8bd`，不回写历史结果。

可重放命令：

```sh
export COQBIN=/data/home/lucentzhou/.opam/default/bin/
export PYTHONDONTWRITEBYTECODE=1
make check-functions
make test
make audit
make source-freeze-check check-c-evidence check-models
```

`make check-functions` 实时重查而不覆写正式记录；发布时 `--record` 排他新建新路径。正式 JSON 包含检查输出和输入身份，不依赖本机忽略日志才能审计。定向编译过程中发现的导入、数组基址化简和整数范围证明错误已修正，失败日志仍保留于 `audit/logs/stage12/`；不把这些早期错误冒充指定控制的成功。

## 仍开放的义务

- 内部规格查找在完整真实环境中的兑现。
- 调用后置到目标读取前置的分离资源交接，以及指针输出可写资源。
- 两句顺序组合的 `InfRules`，及随后分支／计数器／切换。
- 保存令牌的临界区进入／退出与关闭中断不变量；准确全局符号表与 TCB 布局。
- 实际 TCB 状态、共享不变量、全 API／内部环境、真实初始化、最终 `GOOD_OS` 和同程序 K1–K4。

uC/OS-III 尚未开始；两个阶段的总目标保持活动。

## 清理记录

逐项确认后仅删除本阶段不再使用的调试备份 `/tmp/Target-stage12.v`；正式门禁与小模型的一次性目录由各自上下文／退出清理自动移除，正式门禁目录已核实不存在。保留 Coq 源文件、可复用的本地编译依赖、历史 JSON、新正式证据和本机验证日志；未删除既有缓存、用户数据或凭据。
