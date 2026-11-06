# 第112步：预留槽位的半权限所有权与失败回滚

## 先用一句话说明进展

第111步证明“能借出槽位并写 NULL”，但没有证明“这个槽位仍属于本次任务创建”。本步用已有的物理半权限补这个局部缺口：**预留后创建者拿一半，共享池拿一半；回滚必须先把两半拼回完整写权限。** 它不能清除与自己预留值不同的任务指针。

这不是整个内核已完成，也不是完整 `OSTaskCreateExt` 已完成。最终目标仍先完成固定 uCOS2 的源码级 `GOOD_OS` 和同程序 K1–K4，再按老师附件推进 uCOS3。

## 具体接通的源码片段

新增 `certiucos/v293/proofs/V293TaskCreateReservationOwnership.v`，不改 C、原 AST、框架或旧证明：

| 接口 | 实际连接内容 | 仍需的条件 |
| --- | --- | --- |
| `V293_OSTaskCreateExt_owned_reservation` | 原 RESERVED 赋值、真实 `excrit1`、共享归还与创建者保留半权限 | 已在 NULL 槽分支，生产 Close 转换 |
| `V293_OSTaskCreateExt_owned_stack_fragment` | 上述预留、退出临界区、实际栈 Hook 调用连续片段 | Hook 标准资源契约；函数体／函数环境义务未因此自动完成 |
| `V293_OSTaskCreateExt_owned_rollback` | 实际 `encrit1` 借池、合并权限、NULL 写入、`excrit1` 归还 | 同一生产 Inv 的 Open／Close 转换 |
| `V293_OSTaskCreateExt_owned_empty_call_suffix` | 七个真实 TCB 实参、调用及 err 赋值、原完整后缀、失败清槽并返回66 | 空闲 TCB 头为 NULL 的标准 callee 契约 |

不是把“执行已发生”“槽位未改变”作为前提，也没有删除原成功／调度分支。保留的 owner 进入调用者 frame；真实失败回滚消费 owner，返回者不再持有它。两段连续片段目前**尚未拼成完整合法 NULL 分支或完整函数契约**，不能把接口数量记作函数覆盖。

## 为什么权限必须由值决定

池允许任意类型正确的指针值，但权限唯一决定：

- RESERVED：共享池只持半权限，创建者持另一半。
- NULL 或其他任务指针：共享池持完整权限。

`V293_reservation_pool_precise / pool_good / pool_isr` 已检查。`V293_reservation_compatible_values` 从 join 后同一物理内存的两次实际类型化读取推导值相同；`reacquire` 因而只能得到完整 RESERVED 权限，接着才可写 NULL。

任意允许同值的半／全权限并不满足 `precise`，独立探针给出共同完整内存下的反例。这里没有新增 ghost 身份、抽象状态编号或公理，决策原因见 [ADR-0009](../docs/adr/0009-预留槽位复用值决定的半权限.md)。

**唯一性边界：**孤立的两份半权限本来可以合并，不能宣称 owner 自身不可复制；`single_owner` 要求共享池在场，第三份半权限才会与池一起发生冲突。还没有证明所有内核 API 都保持这个协议。 RESERVED 符号与真实任务 TCB 指针不冲突的生产域条件仍按 ADR-0004 开放，不能仅靠半权限证明推出。

## 同一个字面不变量，不靠不可满足前提过关

独立 `audit/probes/V293TaskCreateReservationOwnershipProbe.v` 不导入其他审计探针：

- 只有一个 `ROInv`；NULL、RESERVED、其他任务指针的实际字节都能满足同一共享池。
- `ROOwnedWholeLiteral` 给出带 owner 的真实七实参调用者与完整共享资源共存的实际总内存；不是各自孤立可满足。
- `ROBuilders` 检查原 TCB 七参数／两局部的 `BuildPreI / BuildRetI`。
- 同一有限 `ROSpec`、同一 `ROInv` 检查本步调用后缀和原完整空头 TCB 函数体；同一 Inv 还实例化预留／退出片段。

**尚未建立**此 Inv 下预留片段的独立字面入口、完整 callee 内部入口字面见证、初始化可达性、`WFFunEnv / WFIFun`。不能把别的不变量下的旧入口见证当成本步已完成项。

## 前瞻消融与反例

`protocol.json` 早于首个证明快照。精确控制只改 `Action` 一行：保留 `ROOwner` 或移除为 `emp`。共同地址、类型正确的其他任务指针、共享池、期望排斥性质和证明脚本不变。

接受的第02版两组均先证明实际共同输入和删除后的兼容反例，再进入目标：保留组通过；删除组在最终排斥目标失败。`ROOwnerRemovedAdmitsWrong` 是 Coq 已检查的正向反例，避免把 tactic 失败误认作性质不成立。第01版两组缺少显式类型导入，在共同输入前失败，完整保留日志／快照，仅算技术失败。

第02版协议和首个快照的文件系统时间戳相等，不能据此证明亚时钟刻度的严格先后；运行脚本先写协议再生成源码并启动编译，原始时间戳及此边界保留在 `controls-timing.json`，没有重写时间制造顺序。

这个对照只测**物理权限兼容性**，不执行整个中断、Hook、调用或 API；不能据此宣称每个下游机制都被独立消融验证。

## 验证、身份与下一步

固定上游提交 `0c4a48e6fbc6e915714e816196619a5481accf0c`；配置后身份 `74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da`。本步重算实际存在的上游 `OSTaskCreateExt` 347–407行及 `OS_TCBInit` 2022–2151行切片、整文件和旧模型输入。修补树路径是冻结重放的逻辑路径，本步没有重新生成该树，不声称做了新的 C 翻译或修补重放。

生产稳定编译为 proof19，独立探针为 probe10；所有技术失败快照仍保留。新增10项结构回归不代替 Coq。完整终态、假设闭包、内核复核、旧失败集合对比与清理结果统一记录在 `audit/logs/stage112-reservation-ownership/checkpoint-report.json`，以该机器报告为准。

| 复核项目 | 本步实测 |
| --- | --- |
| 稳定生产／独立探针 | proof19／probe10，均 exit0 |
| 独立 coqchk | 278个活动模块＋1个探针，exit0，约394.3秒 |
| 新定理假设闭包 | 58根，仅 classic 与 functional_extensionality_dep |
| 全量测试 | 1574项，423失败／1错误；旧失败ID集合不变 |
| 生产产物 | 1390个；原1385个全部字节不变 |
| 清理 | 先完整核验清单再删除29个本步一次性文件，共672233字节；旧文件零删除，算术缓存恢复 |

`make build` 通过；`make audit` 仍因旧的 `stale function evidence input identity` 退出2；`git diff --check` 仍是旧 `inferules.v` 第581–586行六处空白。未弱化门、未重写旧冻结证据、未提交／推送。六门 **94/1/1/1/1/0** 不变。

下一步把该所有权协议接入真实完整 NULL 分配分支，统一 Hook 后的局部变量交接，再接已有 TCB 调用／后缀；成功发布任务指针还须正确消费 owner。生产全局 Inv、非空分配、WFIFun、初始化、`GOOD_OS` 和同程序 K1–K4 都仍开放；uCOS3 未开始，总目标 active。
