# 第86步：OS_TCBInit 非空路径接入框架 Hoare

## 这一步实际推进了什么

上一步只证明18次字段初始化。本步直接证明它前面的真实赋值和临界区操作，把它们接到**既有完整函数体**：

1. `cpu_sr = 0`；
2. 进入临界区；
3. `ptcb = OSTCBFreeList`，允许局部对象原值为 `Vundef`；
4. 从实际加载的非空指针求值真实守卫，选择成功分支；
5. `OSTCBFreeList = ptcb->OSTCBNext`，实际读取并写回表头；
6. 退出临界区，恢复原 `cs`；
7. 执行上一步证明的18次真实字段写入；
8. 接到尚未证明的真实后续段。

三个新增赋值和18字段合计21次赋值；不是把已有执行轨迹当作 Hoare 前提。真实空分支仍在函数体语法中，在这个非空入口下证明其不可达。

## 稳定接口与明确的开放义务

代码：`certiucos/v293/proofs/V293TCBSuccessHoare.v`。

| 接口 | 已证明内容 | 仍需前提 |
| --- | --- | --- |
| `V293_OS_TCBInit_pop_fields_hoare` | 真实pop → excrit → 18字段段的框架 `InfRules` | 范围、输入类型、空间资源、`GoodFrm`、`CurLINV`，无suffix义务 |
| `V293_OS_TCBInit_nonempty_body_with_suffix_hoare` | 既有完整 `V293_TCBInit_function_body hi hc` 的条件 Hoare | 上述资源条件，加实际 `V293_TCBInit_success_suffix hi hc` 的 `InfRules` |
| `V293_OS_TCBInit_nonempty_body_with_suffix_semantics` | 经 `RuleSound` 得到同一完整函数体的框架 `RuleSem` | 同一个未兑现的suffix Hoare前提 |

**后续段没有证明完成。** 开放前提覆盖两个真实CPU Hook调用、优先级表、发布和return；不是空Hook实现，也不是可删除的装饰条件。前提只从18字段完成后的真实状态开始，不循环假设本步cpu初始化、load、guard、pop、临界区退出或字段段。

入口限定中断已关闭，`cs`任意。进入临界区把`false`压栈，退出后恢复原栈；字段初始化在该次临界区外，和既有程序顺序一致。局部对象已分配，本步不证明调用分配/free。

## 可满足的独立空间入口

探针：`audit/probes/V293TCBSuccessHoareProbe.v`，不导入其他探针。

- 29个核心cell：18字段、8输入、cpu对象、全局free-head、TCB的next字段，合计**81字节**。
- 加只读当前任务指针4字节和哨兵1字节：完整实例**31个cell／86字节**。
- 新TCB位于`(301,128)`，next值指向`(301,256)`；当前任务指针指向`(301,8)`；哨兵为77。
- 初始18字段全`Vundef`，两个局部对象初值也可以为`Vundef`，真实参数优先级11。
- `SuccessInitialEntry`证明原始入口；`SuccessPopEntry`证明pop前联合入口；`SuccessRGood`、`SuccessRCurLINV`与实际Hoare接口共同实例化。
- `SuccessChecked`不依赖suffix义务，检查pop／临界区退出／18字段组合；`SuccessBodyChecked`保留真实suffix开放前提。
- `SuccessHeadRead`从实际后置导出表头为next，`SuccessWrongHeadRead`排除仍为旧head，`SuccessNextPreserved`证明next字段未变。

这不是56字节完整TCB所有权，不是全局启动`Inv`，也不包含全部旧任务记录的联合实例；第85步的记录资源后果仍是独立成果。

## 单因素控制与编写失败

前瞻控制只将**后置free-head的值**从`SuccessNext`改为`SuccessHead`；程序、前置、其他cell、导入和证明体保持相同。正控通过，负控在接口类型不统一处失败。此控制只证明接口一致性；具体读取排除由上述独立读回定理负责，不借早期拒绝给Hook或其他字段授信。

编写过程中误写核心尺寸为77字节，`probe02`被内核拒绝；准确的`typelen`合计为81字节，`probe03`通过。第一次完整测试与此修正并发，已导入的77字节结构断言读取了修正后的81字节探针，多出一项编写时失败。原运行、日志和快照全部保留；固定最终证明／探针／测试文件后重跑，`full-tests02`恢复原来的424项旧诊断。没有改写旧测试或降低验收门槛。详见`authoring-correction.json`。

## 验证及不可扩大解释的边界

证据目录：`audit/logs/stage86-tcb-success-hoare/`。

- 252活动源（149目标源）增量构建通过，非cold；新增6项结构检查通过。
- `coqchk`覆盖252活动模块和1独立探针；33个根的假设检查仅允许框架既有三项。
- 稳定完整回归1412项，仍423失败、1错误；与第85步424个旧诊断ID按原序一致。
- 默认`make audit`仍因覆盖证据身份过期退出2；`git diff --check`仍只报既有框架行尾空白，退出2。
- 固定C函数及既有模型哈希复核；未修改C、配置、两类授权修复、框架、旧证明、旧测试或冻结证据。此身份核对不等于已经验证C到模型的翻译器。
- 一次性控制源／探针和信任检查产物、缓存备份按全量清单复核后清理；旧缓存恢复，正式产物和所有失败记录保留。清理后构建、完整回归及最终清单见`final-report.json`和只读核对脚本。

正式六门仍为`94/1/1/1/1/0`。没有整函数`WFIFun`、独立终止／总正确性、完整OSInit／startup／global Inv、源码级`GOOD_OS`或同程序K1–K4闭合；uCOS3未开始。下一步是兑现真实suffix的框架Hoare义务，不能把它仍作为开放前提就声称整函数完成。
