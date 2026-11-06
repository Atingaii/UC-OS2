# 第68步：栈返回赋值与TCB七参数入口

## 本步纵向进展

固定配置后OSTaskCreateExt源身份未变，新鲜预处理/Clang AST再次核对全部94函数、psp赋值及OS_TCBInit七参数的名字、类型和顺序。新增手工alpha-renamed调用片段V293OSTaskCreateExtCalls.v和生产证明V293TaskCreateTCBEntry.v，不改旧源码。

稳定接口 `V293_OSTaskCreateExt_to_TCB_under_stack_return` 从body-entry连续连接已有前缀与四参数栈Hook入口、显式真实返回轨迹、实际psp赋值、err赋值调用准备、七个实参的真实求值，到TCB的sfexec。仅Hook轨迹及owned/frame保护由调用者提供，公共接口不假设psp store、eval或TCB执行。允许Hook改变未拥有内存，不能偷换Mr；赋值及读取都使用真实Mr/Mf。

`V293_OSTaskCreateExt_after_stack_to_TCB` 是不含Hook返回前提的**返回后锚点**定理；它不证明缺失Hook可到达该点。`V293_missing_stack_hook_cannot_return` 排除缺定义时零步或非零步返回。

## 独立实例、负控与消融

独立probe不导入旧auditprobe。p0/p12两个body入口从字面有限内存出发真实到sfexec900；P900=None时无loststep。p0/p12 × NULL/nonnull四个返回锚点另有独立内存所有权，实际到sfexec901；每例同Mf读回17字段（14owned+3frame），新psp与第二源参数相同，err旧值9仍保持。IE任意且si/ci保持。

positive先通过；同证明体只改结论的三负控分别拒绝psp旧NULL、第二/第三TCB实参换序、caller77改0。返回指针与bottom指针是不同块及偏移，非换相同值的伪负控。

前瞻单因素消融只移除返回延续的kassignr wrapper，同BridgeValue true、BridgeEntry12、env、IE/si/ci和AblTail，两条真实语义均到同一下一语句：保留赋值得到新指针，删除后保留NULL，caller77两边保持。**仅赋值锚点信用**，未执行被消融后的7实参或TCB body，无前缀/Hook/下游信用。ablation01仅因raw-read tactic缺显式展开wstate失败，完整保留；02仅添加该展开。

## 验证与范围

230活动源增量构建复用1140旧产物；非冷构建。最终Print Assumptions、coqchk、回归、缓存恢复与清理数字以 `logs/stage68-task-create-tcb-entry/final-report.json` 为准。既有396个失败/错误诊断必须按ID与分类保留，不能宣称全绿。成功和失败Coq尝试均保留源码snapshot与日志，草稿生成器不代替最终snapshot。

5端口缺实现；该条件body接口尚非固定程序成功实例。沿用ADR0004/5/7手工保留地址/IE宏/selector边界，非已验证C前端/ABI或CPU_SR原始字节语义。caller函数分配、TCB body/第65步完整成功连接、err返回赋值及创建后缀未完成。只是存在性无交错轨迹，不是localHoare/全执行safety/GOOD_OS。七次OSInit实际Mf未接；六门94/1/1/1/1/0不升，同程序K1–K4开放，uCOS3未启动，goal active，未提交/推送。
