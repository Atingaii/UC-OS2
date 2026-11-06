# 第93步：OS_TCBInit 非空成功路径的标准函数构造器契约

## 解决的问题

第92步只连接空 free-list 的失败分支。本步沿用未修改的真实完整函数体，把非空成功分支接到框架 `BuildPreI`／`BuildRetI`，供后续调用层复用，不再让调用者自行选择局部变量地址及旧值。

稳定入口为 `V293_OS_TCBInit_success_internal_contract`；底层资源定理为 `V293_OS_TCBInit_success_internal_resources`，源码见 `certiucos/v293/proofs/V293TCBSuccessInternal.v`。

- C 顺序为 prio、top、bottom、id、size、ext、options；框架 builder 接受逆序实参，`fpre` 接受经 `rev` 还原的 C 顺序。两者不可混淆。
- 七个参数及 ptcb、cpu_sr 两个局部共九份资源，从真实 `buildp` 解包，返回时按真实 `buildq` 全部交回。
- 精确的九项声明域留在调用者 frame 中；六个全局名不被局部遮蔽由此推导，而非增加 oracle。
- 外部 Hook 资源不能包含局部定义域／局部绑定：其 `GoodFunAsrt` 边界不允许这样做。本步使用 `GoodI` 和 `frame_rule_all` 保留域，不把域塞入 Hook 规格。
- 保留两个真实 CPU Hook 调用及其外部规格查找；没有替换成 skip，也没有提供或宣称验证了 CPU port 实现。

## 独立验证与消融边界

`audit/probes/V293TCBSuccessInternalProbe.v` 自行写出字面资源，不依赖历史探针：相同 block 的不同 offset、NULL／非NULL旧任务链表、35／36个核心 cell、当前任务及独立 sentinel。构造器入口和返回的可满足性分别检查，不能用入口通过推断返回正确。

具体有限规格表区分初始化 Hook 与创建 Hook；`GoodI` 使用已经证明可实例化的受限 shared invariant，不是整核目标 invariant。独立实例的标准契约、返回码0及排除66／None、外部资源读回分别验证。

返回布局控制预先冻结，正控使用完整七项声明，负控只删 options（107）一项，预期标准 `buildq` 不变，编译器与证明脚本不变。此控制只检验返回布局身份，**不是**缺失资源的语义执行反例，也不证明分配／回收或 downstream 正确性。首个控制草稿误用普通 list filter 处理 `decllist`，在类型检查处失败，不能算有效负控；日志与快照保留，另行冻结修正后的单因素对照，不改写旧结果。

证据目录 `audit/logs/stage93-tcb-success-internal/` 保留所有编译尝试、源文件快照、基线、信任检查、测试与清理记录。生成脚本是过程草稿，最终源曾手工修订；不能把草稿生成脚本称作最终源的可重复生成器。最终文件身份以快照、manifest及只读核验为准。

## 仍未完成

本步是有明确前提的成功分支函数契约，不是完整 `WFIFun`，不新增调用分配／释放执行轨迹、不闭合全局 invariant／可达性，不证明独立终止性。两个调用现场特化的 Hook 规格不等于统一全局 port 规格。

原 C、配置、framework、tactics、既有证明／测试／冻结证据均保持；六门仍为94／1／1／1／1／0。既有测试失败、默认审计失败及旧空白错误必须原样报告，不能通过调低门槛消除。

`GOOD_OS` 与同程序 K1–K4 仍未完成，uCOS3 尚未开始，目标保持 active。本步未提交或推送。下一步需要将空／非空两类标准契约统一到实际调用与程序规格，并继续处理全局连接义务。

## 检查点复核入口

```bash
PYTHONDONTWRITEBYTECODE=1 python3 -B audit/logs/stage93-tcb-success-internal/verify-readonly.py
```

该命令只核对冻结证据，不重新生成或覆盖旧证据。真实编译命令、逐次退出码和最终稳定源 SHA 见本步日志。常规增量构建不等于冷构建；独立 `coqchk` 才承担本次全部活动模块的内核复核。

全量1456项测试包含本步新增6项结构回归，仍保留423失败、1错误，旧424个有序诊断身份不变。默认 `make audit` 因已有函数证据输入身份过期退出2；`git diff --check` 仍仅报告旧 `framework/logic/inferules.v` 空白错误。未修饰或删除这些失败。
