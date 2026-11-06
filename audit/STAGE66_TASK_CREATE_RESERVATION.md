# 第66步：任务创建的优先级预留与栈调用准备

## 完成的最小连接

- 源码：固定配置后 `os_task.c:347–407` 的 `OSTaskCreateExt`；94函数身份完全相同，AST逐项核对CPU声明、guard和成功分支次序。
- 代码：`certiucos/v293/code/V293OSTaskCreateExtPrefix.v`。
- 稳定接口：`V293_OSTaskCreateExt_to_stack_call_setup`，辅助接口 `V293_OSTaskCreateExt_prefix_reserved`。
- 在合法优先级、非ISR、空槽及入口所有权下，无Hook返回假设，构造CPU初始化、真实槽位写入、临界退出与scalle准备的连续局部执行。
- 同一Mf拥有预留槽、原优先级、零嵌套、零CPU局部值和任意分离frame；IE恢复入口值，si/ci不变。

终点是 `scall OSTaskStkInit` 及 `kassignr psp` 延续，不是Hook的sfexec。四个实参尚未求值，task函数指针尚未建模；独立探针明确task变量无绑定。它不能提供“已运行端口”或“缺Hook处stuck”信用。

## 验证与证据

`audit/logs/stage66-task-create-reservation/` 保留全部计划、源身份、编译快照和日志。

- 两份字面内存入口p0/p12，各读回8项；不是四份独立IE入口，IE在定理中普遍量化。
- 三项负控：同一成功证明体，仅改终点IE／目标槽／caller保护字，分别在对应结论失败。
- 单因素消融：相同赋值入口、环境、LHS和延续，仅改RHS为保留值或NULL；两边都真实执行并读值，再比较NULL判定。CPU保持23，故不冒领prefix或下游信用。
- proof01–14、probe01、ablation01的失败全部保留；初始generate.py不是最终源码重建器，最终proof15快照绑定当前生产源码。
- 整体构建、Print Assumptions、coqchk、精确旧诊断回归、缓存恢复与清理结果以 final-report.json 为准。增量构建不等于冷构建；旧测试仍有失败，不宣称全绿。

## 严格边界与下一步

采用既有ADR0004统一符号保留地址（非数值地址1），ADR0005临界宏归一化（擦除CPU_SR token字节效应）。手工前端，body-entry非函数分配，成功前缀非完整函数；错误分支保留但未执行证明。真实TCB非碰撞及全局共享标记仍需上层不变量。

下一连接：核对task函数指针表示／四实参求值 → 真实栈初始化返回义务 → 连接第65步OS_TCBInit → 创建后缀和OSInit七调用实际内存。五个端口Hook仍缺实现，不用空操作替代。

只有存在性无交错局部轨迹，没有local Hoare、全执行safety或GOOD_OS；六门仍94/1/1/1/1/0，同程序K1–K4开放。最终目标active，第一阶段未完成，不启动uCOS3；本步不提交／推送。

## 本步最终检查结果

- 227个活动源增量构建通过；1125个旧产物逐hash未变，保留1135个可复用生产产物。
- 56个信任根的Print Assumptions及coqchk通过；仅既有classic／funext／eq_rect_eq允许假设。
- 新增5项测试全通过。完整1306项：395 failures、1 error，与stage65的396个旧诊断ID及分类逐项一致，无新增失败；不是全绿。
- scope／固定C检查／diff检查通过；默认make audit仍exit 2，覆盖门未闭合，不降低标准。
- 两个既有缓存按原字节恢复，生成字节另存证据；只清理已确认的一次性目录和probe构建产物，保留源文件、失败记录、用户数据及生产产物。
