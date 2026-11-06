# 第58步：OS_TCBInit 的连续18条初始化写入

## 源码连接和稳定接口

- 模型：`certiucos/v293/code/V293OSTCBInit.v`。
- 稳定接口：`certiucos/v293/proofs/V293TCBInitFields.v` 中 `V293_OS_TCBInit_fields_execution`。
- 既有任务记录连接：`V293_tcb_init_record_connection`。
- 独立有限入口：`audit/probes/V293TCBInitFieldsProbe.v`。
- 完整过程证据：`audit/logs/stage58-tcb-init-fields/`；最终验收看`final-report.json`／`final-evidence-manifest.json`。

重新物化锁定C、配置及两项授权修复；94个函数身份全部一致。记录Idle／Stat→OSTaskCreateExt→OS_TCBInit的准确函数体，当前STK_CHK=0，没有OS_TaskStkClr调用。OS_TCBInit成功分支中，在free-list pop／退出临界区之后、OSTCBInitHook之前恰有18条连续赋值。新鲜Clang i386分析布局与全部18项字段偏移一致，TCB大小56；这是源码分析交叉检查，不是ABI或编译器正确性证明，前端仍手工连接。

入口只要求18项可写旧字段、8项局部／参数、环境绑定、参数类型有效性和p<13及base边界；不假设表达式求值、执行结果或callee已经返回。旧字段可以是Vundef。逐条执行实际sassign，保持其余所有权；掩码真正从已写的Y／X字段读取后移位、窄化，不把掩码当作参数。

## 所写字段（结构内偏移）

| 字段 | 偏移 | 结果 |
| --- | --- | --- |
| StkPtr | 0 | ptos |
| Prio | 50 | p |
| Stat | 48 | 0 |
| StatPend | 49 | 0 |
| Dly | 44 | 0 |
| ExtPtr | 4 | pext |
| StkSize | 12 | stk_size |
| StkBottom | 8 | pbos |
| Opt | 16 | opt |
| Id | 18 | id |
| DelReq | 55 | 0 |
| Y | 52 | p>>3 |
| X | 51 | p&7 |
| BitY | 54 | 1<<Y |
| BitX | 53 | 1<<X |
| EventPtr | 28 | NULL |
| FlagNode | 36 | NULL |
| Msg | 32 | NULL |

合计写44字节。未写的是Next20..23、Prev24..27、FlagsRdy40..41及padding42..43，共12字节，不暗中清零或发布。

## 独立端点与前瞻实验

独立probe不导入旧audit probe，自己构造有限内存并证明可写所有权，目标18项全是Vundef。TCB位于301:8，非零base；输入和frame也按字面构造。每次在同一Mf闭合31项typed load：18个字段、8项局部／参数、5项frame。frame含未写的12字节和外部保护字77，Next／Prev为非NULL，FlagsRdy及padding为非零。p12和p11分别执行得到Idle／Stat参数对应结果，共62项读回，**不是两个任务在同一轨迹共存**，更不是实际栈分配或任务创建成功。

只把整个18写入片段替换为sskip；P、ks、环境、有限入口、参数、frame不变。计划先冻结，正例与删除后的六项测量都由机器检查：

| 测量 | 原片段 | 整段删除 |
| --- | --- | --- |
| 优先级 | 12 | Vundef |
| 内部状态 | 0 | Vundef |
| 延时 | 0 | Vundef |
| 栈顶 | 401:508 | Vundef |
| 消息 | NULL | Vundef |
| 外部frame | 77 | 77 |

只是存在性执行端点，不是C运行时测量。只授整片段信用，不授18个内部机制各自信用。第一候选错用需要类型有效性的typed-load引理读取Vundef，被拒绝；第二候选全图VM计算持续高CPU／内存，被明确SIGINT中断（218秒），快照和日志保留。后续只改为精确所有权字节切片读取与load单调性，保留所有语法、作用域和参数推断失败候选；第八候选通过，所有候选的最终定理陈述逐字相同，没有把Vundef改成合法类型值。两个局部helper及端点的Print Assumptions均在日志中。

另外四项负控只改单一结论，证明正文完全不变：错误优先级11、错误栈顶504、错误延时1、损坏frame78。正控先通过；四负控分别在预定的24／27／26／29行最终读回证明拒绝，不把语法或提前失败算作机制证据。

## 信任、保留与明确未完成项

215源构建复用1065旧生产产物，非source-only冷构建；57根Print Assumptions、四模块coqchk通过，仅允许既有框架三项公理。旧213源、1065生产产物、C／配置、旧测试和旧冻结证据不改；两缓存恢复本轮前精确字节，生成字节另存。新加8项回归，要求保留第57步396个诊断ID；默认make audit仍因旧function evidence身份过期退出2，不能假报全仓绿色。

**本步不是完整OS_TCBInit**：free-list取出／失败路径、两个port hooks、优先级表、TCB全局链、ready位图、任务计数和返回尚未执行。APP_HOOKS=0不代表可以删除实际port Hook。OSTaskStkInit只有声明，没有函数体；函数地址表示仍开放，未新增其合同或把它伪装成数据指针。TCB记录里的rdy仅是内部状态，不是ready bitmap membership、栈有效性、任务可调度或API成功。

**尚未接到第57步七调用的实际返回内存**。无交错cstepstar存在性不是local Hoare、所有执行safety、完整94函数程序或源码GOOD_OS；六门仍94／1／1／1／1／0。整体运行不变式、OSStart及同程序K1–K4仍开放，阶段一完成后才做uCOS3。未Git提交／推送。清理先完整列单、完整二次核对后才unlink，仅清本轮临时与probe编译物，保留全部生产产物、源、失败和成功证据。
