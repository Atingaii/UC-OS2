# 第255步：同一续体上的完整优先级复制至切换模拟

## 这一步解决什么

当前目标仍是固定配置 uC/OS-II V2.93.01 的源码级整核证明，随后才开始 uCOS3。前面发现：优先级缓存复制完、抽象当前任务尚未切换的瞬间，新 GHinv 无法闭合。因此不能直接把新不变量代入要求切换前 SWINV 的旧 switch_rule。

本步直接使用原 `ProgSim` 语义，把整个临界片段一起连接，不要求在该瞬态重建 GHinv。没有修改 C/config/AST/framework，也没有改旧 Inv/LI/BDspec、旧证明、测试或冻结证据。仍采用已接受的 [ADR-0010](../docs/adr/0010-中断切换调用点采用显式源码级抽象.md)：这是调用点的显式源码级抽象，不是原外部端口调用的语义保持证明。

## 生产接口

`certiucos/v293/proofs/V293HandoffProgSim.v` 的稳定接口为 `V293_handoff_progsim`。

输入包括真实代码与局部状态查找、IE=false、合法 OS 续体、优先级读写与指针读写、高层调度匹配和切换后的原 ProgSim；结论是整个“复制 → switch”片段的原 ProgSim。目标任务代码不限定为终止代码，续体参数保持完全相同。

复制部分不是只证明一条成功执行：

1. 展开顺序语句；
2. 进入赋值求值；
3. 读取最高就绪优先级；
4. 转入左值求值；
5. 获得当前优先级地址；
6. 执行字节写入；
7. skip 接上 switch。

每个微步均由原 cstep 构造；非写入步用原确定性引理，写入步独立反演证明唯一后继。原 lpstep 的中断、client、OS、切换与栈操作分支被穷尽，另证无输出和无异常。不能把存在一条 cstepstar 当成所有执行均安全。

`V293_os_silent_progsim` 把一个 OS 静默步向前组合，`V293_handoff_copy_progsim` 组合七步，最后复用原 switch 模拟。中间堆可以暂时不满足 GHinv；这不等于取消调用者其他资源义务。

## 独立、非终止的 typed 实例

`audit/probes/V293HandoffProgSimProbe.v` 的 `HPactual_handoff_simulation` 从实际空间所有权构造 M、Mc、Mf，不假设写入成功或假设结果定理。

- `HPpending = CGpending ## CGouter`；复制、切换及保存旧任务时都使用该同一续体。真实外层函数绑定支持 InOS，不凭空宣称处于 OS。
- 复制前当前优先级为6，最高就绪为4；复制后当前字节为4，抽象当前仍为 Waiting。`GHrejected` 保留任意分离 frame 下中间态拒绝。
- 原物理 switch 写入当前 TCB 指针；原 hswi_step 把抽象当前任务改为 Ready。
- 切换目标是尚有两条 skip 待执行的有限纯 client，`HPtarget_not_ended` 独立证明它不是 IsEnd。
- `HPfinite_simulation` 在全局原 ProgSim 中证明这两步，分别处理全部低层后继、输出和异常；只有执行完两步后才使用终止情况。不是在切换时把目标换成已结束任务。

生产接口的高层匹配与后续模拟仍是显式前提；该 typed 实例为特定有限 client 独立满足它们，并非任意 client 的通用解。第254步的任务级 TaskSim 与本步全局 ProgSim 也不是同一个关系，不能仅凭前者冒充后者。

## 单因素对照与边界

| 检查 | 固定什么 | 改变什么 | 结果及可作出的结论 |
| --- | --- | --- | --- |
| 中间 guard | 同一复制后的 Mc、抽象 Waiting 及所有权布局 | 尝试以新 GHinv 闭合 | 任意 frame 均被拒绝；桥未偷补一个不成立的不变量 |
| 高层当前任务 | 后置物理状态、任务映射、续体和 client 不变 | 仅省略高层 current 更新 | `HPzero_high_match_rejected`；所需后置模拟不成立 |
| 中断边界 | HPcode、堆、环境、向量、空栈不变 | 仅 IE=false 改 true | false 无 lintstep，true 有原 pint_step；不能把关闭区间的全后继结论泛化到任意交错 |
| 导入精简 | 所有命题、证明体及编译参数不变 | 依次移除两个不使用的 import | 每项分别完整编译验证；不改变数学前提 |

IE 对照是单独的空栈入口边界，不把完整 typed handoff 的非空临界栈换成空栈，也不声称中断开启时 handoff 必然不安全。目标 finite client 的全局模拟要求其 IE=false；第254步的 true/nil/nil 初始化契约不能替代这个区间条件。

## 验证与尚未完成

真实编译记录、失败快照、Print Assumptions、递归 coqchk、构建和测试报告放在 `audit/logs/stage255-handoff-progsim/`。Python 测试只检查接口和证据身份，不代替 Coq 数学检查。历史失败不会被删除，实际计数以 verification.json 为准。构建另自动刷新既有 `.Makefile.coq.d`，只追加新模块三行依赖，去掉这三行后的字节与基线完全相同。这项生成缓存变化不在前瞻的三份文档／注册文件清单中，已单列偏差；保留真实构建结果，不通过恢复旧依赖缓存掩盖旧身份测试可能新增的失败。

本步不是任意 client 的 TaskSim，不是完整中断返回，不是 `WFInt`，不是 `GOOD_OS`。还需把同一桥纳入实际 Exit/Sched 及返回环境、独立建立一般暂停任务的后续模拟，再连接初始化与全部 API。K1–K4 未闭合；uCOS3 未开始。函数覆盖保持 94/1/1/1/1/0；局部语义桥不增加 full_target_linked。

未提交／推送。当前整仓审计和旧回归仍有已记录失败，不宣称仓库全绿。

## 本步实测结果

| 检查 | 实际结果 |
| --- | --- |
| 生产14根、独立 probe 15根 | 重复编译、29根 Print Assumptions 及递归 coqchk 均通过 |
| Coq 输入冻结 | 独立检查运行期间734个 Coq 输入未变 |
| Coq 8.18.0 构建 | 通过 |
| project-audit | 通过 |
| 新增回归 | 6/6通过；不是用结构匹配代替 Coq 检查 |
| 完整测试 | 2440项，427失败、1错误；失败／错误 ID 与顺序同第254步，无新增或删除 |
| make audit | 仍因既有函数证据身份过期而失败；未改写证据 |
| git diff --check | 原 inferules.v 六行空白失败不变 |

检查仅使用原有 classic 与 functional_extensionality_dep，无新增公理。所有实际失败编译及其源码快照均保留。最终冻结检查、清理清单与结果见同目录 checkpoint.py、verification.json；本步一次性信任驱动和产物按清单删除，原有缓存恢复，可复用证明产物保留。
