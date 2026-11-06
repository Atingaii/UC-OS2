# 第187步：把原 OSIntExit 调度中段接入真实临界调用

## 本步解决什么

第185步已经证明真实的递减、嵌套／调度锁守卫、OS_SchedNew、最高任务指针发布、优先级比较和切换计数递增；第186步证明真实的 `&saved` 调用规则，但仍要求调用者提供整个中段的 Hoare 证明。这两个结果的资源布局不同，尚不能直接连接。

本步稳定接口是 `V293_OSIntExit_resource_bridge`，位于 `certiucos/v293/proofs/V293OSIntExitResourceBridge.v`。它直接组合两个实际指针 `scall` 和已经证明的中段，不再接收整个中段的 Hoare 前提。

## 资源如何连接

- `V293_exit_physical_pre` 与 `V293_exit_physical_tail` 保留 ready 输入、scheduler 内部资源、真实 TCB 指针表及抽象任务表、当前优先级、目标指针、切换计数以及嵌套／锁字节。
- `V293_exit_caller_bindings` 留在 caller 的 `GoodFrm` 中。这里包含全局绑定与对应的局部不遮蔽事实，不是“只有局部变量”，也没有删除全局绑定。
- saved 的物理单元进入 callee 资源；`Alvarenv saved` 留在 caller。callee 的资源逐一证明 `GoodFunAsrt` 和 `CurLINV`。
- `pre_split/pre_join`、`tail_split/tail_join` 均为双向所有权保持的蕴含，未以 `Atrue` 替代交付资源。
- 没有引入通用 assertion 转换器；绑定整体移动、分离合取重排已经足够。物理资源的 admissibility 引理清除了无用名称参数。

中段稳定接口 `V293_OSIntExit_middle_bridge` 的唯一语句级残余义务是实际 `scall int_switch nil`：只在减后嵌套为0、锁为0、选中优先级不同于当前优先级时需要。其前置拥有 `Int.add c Int.one` 的 counter、已发布的最高任务指针、完整 ready/table/TCB、嵌套／锁、saved 及 caller 绑定。counter 不是仍为旧值。

## 预先规定的对照与证据

协议先于本步实现保存在 `audit/logs/stage187-interrupt-resource-bridge/protocol.json`，身份另存。探针独立重建第185步形式的非空物理堆，只导入生产证明／见证模块，不依赖旧 audit probe。

| 对照 | 不变项 | 观察与严格限度 |
| --- | --- | --- |
| 双向资源分解 | 同一所有权 | pre/tail 均可拆回、合回，没有漏掉表、TCB、计数或字节 |
| caller 局部遮蔽 | 完全同一物理堆、全局环境、抽象状态 | 不遮蔽时完整入口接受；仅新增 nesting 局部遮蔽后，callee 物理资源仍接受，完整 caller 资源拒绝。它只检验名称边界，不是 scheduler 语义验证，也不声称两个局部环境 domain 相同 |
| counter 旧值错误 | 相同局部／全局环境、其他资源 | 修改 counter 后正确完整入口接受，错误旧值在同一堆上由 `load Tint32` 冲突排除；14号块外所有字节保持 |
| 删除 lookup | 其他函数 lookup 不变 | 仅检查 Some/None 输入，不声称无法推出任何 InfRules，更不代表 port 实现语义 |
| acquired/tail 完整非空 | 实际 ready/table/TCB/saved/caller | 各自构造物理快照，不把两个快照称为实际执行 trace |

fixture 使用空 LocalInv、单 idle 任务；`nc` 的对照不证明生产 current-task 一致性。实际生产 ISR/LocalInv 仍开放。

## 如何复核

```bash
python3 audit/logs/stage187-interrupt-resource-bridge/check-source.py source-recheck
python3 -m unittest discover -s tests -p 'test_interrupt_resource_bridge.py' -v
make build COQBIN=/data/home/lucentzhou/.opam/default/bin/
```

实际运行的逐次编译快照、所有失败日志、稳定编译身份、逐根 `Print Assumptions`、两入口递归 `coqchk`、两轮全量测试、旧失败有序 ID 对照和清理结果均见同目录 `verification.json` 及其关联证据。未把旧423失败1错误清零；构建／审计各命令结果分开记录，旧 coverage audit 和旧 inferules 空白问题不掩盖。

## 仍未完成与下一步

这仍是条件片段连接，不是完整 `OSIntExit` body、函数 builder 或 `GOOD_OS`：

1. enter/exit lookup 仍采用第186步固定 owner、空逻辑参数契约。没有证明同一个生产 Spec 对所有任务、所有 saved 资源成立；本步去掉整个中段前提，并未去掉端口实现前提。
2. `OSIntCtxSw` 的实际调用实现与其后置资源族仍须证明；当前明确保留该调用的条件 Hoare 义务。
3. saved 的真实分配、初始化与本步入口的纵向连接、running 守卫、BuildPreI/BuildRetI、ISR 安装、生产 LocalInv、初始化和完整全局环境仍待完成。
4. 全交错 simulation、同程序 K1–K4 和顶层源码级 `GOOD_OS` 尚未闭合。六阶段覆盖仍为 `94/1/1/1/1/0`；uCOS3 未启动，总目标 active。

下一步应继续同一函数的真实 builder／running 入口及生产临界接口，而不是另开互不连接的证明分支。旧证据、C/config、旧 AST、framework/tactics、原测试不改写；没有 Git 提交或推送。
