# 第201步：完整中断退出调用、实际切换与目标任务返回

## 本步接通什么

上一步在 `pswitch_step` 后停下：执行者/当前指针/优先级缓存已到 ready4，但原 waiting6 的 `excrit / sret / kcall / kint` 仍挂起。本步不是把 waiting6 强制改成 ready；而是消费 **ready4 输入映射中本来存在的另一份返回现场**。

生产接口 `V293_OSIntExit_call_switch_resume` 从真实 `T/les/aus` 中的完整 `scall` 开始，复用第200步正常缓存同步程序，执行实际 switch，再让被选中的任务退出临界区并完成返回。前提是源码 lookup、空间所有权、实际映射绑定和地址不别名；没有要求调用方提供 trace、free、store、分配结果或分类答案。

后置分别给出：目标 saved 释放、目标 caller 与目标 IE/critical-stack 恢复；当前指针/缓存/counter 保持在切换后的值；原 waiting 任务的代码/局部环境/辅助状态仍挂起，原 fresh saved 四字节仍存活。目标现场的历史来源仍是输入边界，不是本步证明生成的生产调度历史。

## 独立见证与消融

| 检查 | 不变项 | 改变项与实测性质 |
| --- | --- | --- |
| `RXboth_initial_IE` | 同一程序、同一物理初始堆、同一目标现场 | 仅原任务 IE=false/true；两侧都完整调用→switch→目标返回，原任务保存各自 IE |
| `RXboth_target_IE` | 同一程序、同一物理初始堆、原任务 IE | 目标保存 IE=false/true；两侧目标完整返回，恢复各自 IE |
| `RXstack_top_ablation` | 同一返回程序、同一真实非空物理堆和 free 结果、代码与局部环境 | 仅删除 `enabled :: negb enabled :: ci` 顶位；两侧都退出/释放/返回，恢复 IE 分别为 enabled / negb enabled |
| `RXexplicit_exint` | 非空 waiting/ready 资源、真实目标 saved 与源码绑定 | 显式 `exint` 尾，两种保存 IE 都恢复指定被中断代码/表达式续体/环境，弹一层中断栈并按原规则令 IE=true |
| `RXbare_kint_rejects_auto_pop` | 非空程序，任意堆 | `SKIP + kint` 没有局部 loststep；不把它说成 IE=true 时全局不会再次接中断 |

目标 saved 是在原 `SXmemory 1 6` 的全块 fresh 地址7000上，调用已有 alloc/store 构造接口得到；通过 `V293_cpu_initialized_frame` 加到真实空间前置，不是任意假定一块堆。`RXcomplete_initialized` 是复用这个初始化结果的内部接口；不带初始化答案前提的两 IE 正控实际构造该结果。目标原现场来自真实 `GXtasks/GXenvs/GXaux` 绑定，生产定理不覆盖或伪造它们。

消融在返回尾段、显式 exint **之前** 观察；不声称是两份完整调用程序的消融。若先 exint，原规则总设 IE=true，便会掩盖保存位的作用。裸 kint 的局部拒绝也不代替有 exint 的完整正控。

## 关键审查发现

`GoodInvAsrt` 允许断言依赖中断栈。它能支持 excrit/return 的所需上下文变化，但不能凭它就宣称任意 R 在 exint 弹栈后保持。例如对当前中断栈的断言就能反驳这种扩大。于是显式 exint 接口只报告实际 trace、free、删除与块外 frame，不声称任意 R、SWINV 或生产 ISR invariant 已跨弹栈保持。早期失败编译快照保留，可追溯这一边界。

## 检查与复现

证据：`audit/logs/stage201-interrupt-resumed-return/`。`protocol.json` 在实现前冻结；所有尝试的编译快照/日志保留。`stable-compiles.json` 指向最终源码身份，`trust.json` 和逐根假设表记录动态枚举根与递归 coqchk；`verification.json` 冻结回归、旧文件哈希、构建/审计实测结果和清理清单。

复现稳定编译：

```bash
/data/home/lucentzhou/.opam/default/bin/coqc -q -R . CertiOS certiucos/v293/proofs/V293OSIntExitResumedReturn.v
/data/home/lucentzhou/.opam/default/bin/coqc -q -R . CertiOS audit/probes/V293OSIntExitResumedReturnProbe.v
python3 -m unittest discover -s tests -p test_interrupt_resumed_return.py
python3 audit/logs/stage201-interrupt-resumed-return/recheck-checkpoint.py
```

不重新运行会覆写身份的冻结编译/信任/终结脚本。上面独立 coqc 会使用并可能更新已有算术缓存；只读 recheck 应先执行，冻结时已恢复缓存原字节。

## 仍未完成

沿用 ADR-0010 显式源码调用点抽象，未证明原 OSIntCtxSw 原始端口 refinement。没有调度/唤醒原 waiting 任务；没有证明任意交错、生产 ISR 现场安装及 LocalInv、WFFunEnv、初始化/全局环境、全系统模拟、同一程序 K1–K4 排除或 GOOD_OS。uCOS3 未启动；六阶段覆盖仍为 94/1/1/1/1/0，总目标 active，未提交/推送。

下一步应连接生产 ISR 的具体入口/退出现场和不变量，特别是显式 exint 的中断栈条件，而不是继续假设目标现场具有所需形状。
