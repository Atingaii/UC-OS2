# 第67步：四个实参求值与栈Hook真实入口

## 最小纵向连接

固定配置后 `os_task.c:347–407` 的 `OSTaskCreateExt`，94个函数身份从新鲜预处理/Clang AST核对一致。AST再次确认 `psp = OSTaskStkInit(task, p_arg, ptos, opt)` 的四个纯变量读取及原始类型。

新增生产证明 `certiucos/v293/proofs/V293TaskCreateStackEntry.v`，稳定接口 `V293_OSTaskCreateExt_to_stack_hook`：从body-entry环境和所有权出发，连接第66步真实前缀、赋值调用准备及四个实参的语义执行，停在 `sfexec` 和 `kassignr psp`。公共接口不要求中间eval/执行轨迹，四次读值都来自前缀执行后的同一Mf；任意分离frame保留，IE/si/ci恢复。

## task表示决定与必要限制

[ADR0007](../docs/adr/0007-任务入口复用框架函数标识符.md)复用既有框架整数函数标识符，不改C或通用框架。生产证明显式要求uint32范围，并证明解码准确和范围内单射。最小实验比较相同vtoZ解码器：整数selector有效、对象指针None；移除范围时0/2^32发生回绕碰撞。

这只是手工源码表示决定，**不是C函数指针转整数的实现、ABI或机器地址证明**。同程序源码函数与pc f/参数/实际任务体的一致连接仍开放；没有调用旧栈初始化primitive替代真实创建主体。沿用ADR0004/0005边界。

## 独立证据

证据目录 `audit/logs/stage67-task-create-stack-entry/`：

- p0/p12 × target700/701四份有限字面入口，全部参数已绑定，各读回同一Mf的12项；IE普遍量化，不把IE取值算成额外入口。
- 对任意P，若P900=None，实际到达sfexec且无loststep；这是声明兼容部分程序的条件实例，不是固定94函数全程序已链接。区别于第66步task变量无绑定处的早期拒绝。
- 三项负控只改结论、保持证明体，positive先通过；分别在参数次序、selector目标、caller frame结果拒绝。
- selector-spike01–05及probe01失败完整保留；最终spike06、生产proof01、probe02通过。prepare-probe.py只生成初稿，最终probe02显式补导既有V293NullBytes lemma。
- 表示消融只授解码器层信用，无完整前缀/Hook或下游信用。最终构建、59信任根、coqchk、精确旧诊断回归、缓存恢复及清理以final-report.json为准，增量构建不等于冷构建，旧测试不全绿。

## 边界和下一步

到达sfexec不等于查到Hook、分配形参、进入函数体或返回；psp未更新。固定源五个端口Hook缺实现，未造noop，未授Hook成功返回信用。尚未证明调用分配、创建后缀、连接第65步TCB成功调用或七调用实际Mf。

只有存在性无交错局部轨迹，非local Hoare、全执行safety或GOOD_OS。六门94/1/1/1/1/0不变，同程序K1–K4开放；第一阶段未完成，uCOS3未启动，目标active，本步不提交/推送。下一步明确真实栈Hook返回/保护义务，再连接psp赋值、TCB初始化和创建后缀。
