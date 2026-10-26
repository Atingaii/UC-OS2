# 源码分析适配头，不是运行端口

这里的两个头文件仅用于生成固定配置的源码清单：

- `app_cfg.h` 不引入应用定义；固定配置已关闭应用 hooks。
- `os_cpu.h` 固定分析所需类型、指针宽度与条件分支，并保留外部操作的声明。

Clang 使用 `i386-unknown-none-elf`，GCC 使用 `-m32`；两者都使用 freestanding C11 和 `-nostdinc`。没有链接、生成可运行内核或验证具体 CPU。静态断言检查 8／16／32 位类型及 32 位指针。

`OS_ENTER_CRITICAL`／`OS_EXIT_CRITICAL` 展开为 `V293_EnterCritical(&cpu_sr)`／`V293_ExitCritical(&cpu_sr)`。它们仅声明、没有实现，不能解释为无效操作。后续 CoqImp 翻译需要将其连接到框架的中断状态保存／恢复规则，而不是把它们当成普通无副作用 C 函数。

`OS_TASK_SW` 展开为 `OSCtxSw()`；`OSStartHighRdy`、`OSIntCtxSw` 同样只有声明。上游头中提供的 CPU hooks 也保留；应用 hooks 关闭不等于 CPU hooks 关闭。所有边界的契约仍待证明，清单明确记为 `OPEN_BOUNDARY_CONTRACT`。

生成器检查关键边界调用没有整体消失，并比较最终宏值与 `os_cfg.h` 中所有数值配置，防止适配头悄悄修改固定配置。这不是适配头的完整语义证明；适配文件哈希、代码审查和未来边界精化义务不能省略。

设计理由见 [ADR-0001](../../docs/adr/0001-源码清单与端口边界.md)。
