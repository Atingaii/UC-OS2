# Stage26：同一完整返回的SEM/MBOX头数据对应

本轮重新阅读老师附件及活动范围。上一轮属实际进展，不是停止或纯状态复述。最终目标维持源码级GOOD_OS、同程序K1–K4全部闭合后才进入uC/OS-III；两阶段均完成才是最终停止目标。

## 固定决定与证据

先重新实例化锁定源码、固定配置和两授权修复，实际预处理／Clang定位OSTaskChangePrio，函数定义hash仍c29b633e...；另记录锁定上游os_event及OSSemCreate/OSMboxCreate字段赋值。源码身份与手工模型定位不授验证C前端或ABI信用。

在同一活动文件末尾追加：SEM/MBOX头数据关系、完整typed-load frame和一个完整返回适配接口。原6851行逐字保留、全部旧接口不动；不复制底层执行证明，不改旧测试、gate、历史报告、C/config/port/framework或正式覆盖。新关系明确不表示队列后备存储／互斥锁owner，不借False分支声称这些功能已完成。

完整适配根只有一次原完整队列执行调用，保留全部原输出，同一Mf/Os'/OO'及同一实际events查询data。数据关系是入口成立蕴含出口成立，不是已建立初始化／全局不变量。SEM使用完整Tint16 count、65535上界和完整NULL指针；MBOX使用零count与完整消息指针。

固定新probe在执行前安装类型3、完整NULL、完整count0，再重建全部物理资源。具体控制将分别检查完整返回后的count0≠1、低字节同为0但256≠0、同种类非空邮箱指针≠NULL。后两者只授各自头数据语义信用，不授未执行的正常调度或整邮箱API信用。

## 前瞻验证与反对意见

protocol在运行正式gate前落盘。两个负控只改变最终数据内容因素：SEM计数加一、MBOX消息变NULL；保持完整目标Proof。只授固定Proof后置敏感性，downstream_credit=false。独立语义控制另行检查，不能靠负控早拒绝推断下游机制。

gate隔离目标前缀，不含新完整目标；正控只导入该前缀和依赖，不导入候选生产模块。计划17项实际检查：生产、隔离前缀、完整正控、9probe、2负控及3coqchk；假设解析覆盖4正控根及9probe根。未结束前不宣称通过。

旧895项基线在本轮追加后实际303失败、1错误；前轮302个诊断按重数全部保留，新增两项trace分别是上一轮生产快照字节比较与门禁输入SHA过期。没有改旧报告／测试制造绿灯。详见added-diagnostic-01/02.log及old-test-comparison.json。

## 当前限制

只增加局部头数据连接。物理SELF41与抽象current60仍未一致；run1/ISR1/lock0调度受阻；正常调度、共享不变量、API/ISR保持、初始化、源码GOOD_OS和K1–K4仍开放。阶段一未完成，uC/OS-III未启动。实际验证结果与最终身份见下文。

## 开发失败与修正记录

开发probe01在类型字节frame处失败：小于写入起点的分支无需编码长度，强制rewrite反而令rewrite tactic整体不适用；仅修正侧条件。probe02在256的首字节证明失败，补充32位无符号范围和8位模256等价；probe03/04分别暴露手写load化简及其不可转换问题。把最后一处缩成独立CheckLow后，复用既有V293_encoded_byte_load实际编译通过，不改命题或计数读取宽度。最小harness第一次有括号语法错误，修正后的实际日志也保留。

gate01在注意到development04退出1之前已误启动；实际前11项成功、第12项新probe于同一line593不可转换处失败，未运行负控／coqchk，不授17项成功信用。退出时全部冻结输入保持，临时树按manifest清理。保留完整报告、源快照及失败日志；修正probe后另建gate02，不覆盖gate01。生产一般证明和6851行旧前缀均未因此改变。


## 实际验证结果（gate02）

| 项目 | 实际结果 | 授予的范围 |
| --- | --- | --- |
| 生产／冻结前缀／完整正控coqc | 3次退出0 | 当前局部证明可编译；正控不导入候选目标 |
| 九个固定probe coqc | 9次退出0 | 全部旧8probe及新9根probe实际检查 |
| ChangedSemCount、NullMailboxMessage | 2次预期退出1 | Proof始于162行，首次175行tauto拒绝，仅固定Proof敏感性 |
| coqchk | 生产、新probe、隔离正控3次退出0 | 各自及其依赖的内核检查 |
| 假设 | 4正控根、9probe根；并集classic、functional_extensionality_dep | 无额外公理；不等于整个GOOD_OS根闭包 |
| 冻结输入 | 189个不同路径，退出时及复核均保持 | 166＋9＋12＋Before／baseline／gate＋2helper，3源路径重叠 |
| 新Python测试 | 8项通过 | 协议与实际报告一致性；语义信用来自实际Coq检查 |
| 全量Python测试 | 903项，303失败1错误 | 与本轮旧895项基线的304诊断按重数相同，无新诊断／无删除 |
| 范围／源码冻结／diff | 退出0 | 固定目标与两修复保持 |
| 增量make | 退出0，无Coq重编 | 不授全量干净重建信用 |
| 默认make audit | 退出2，stale function evidence input identity | 失败保留，正式六门94／1／1／1／1／0不变 |

当前生产7054行／467,008字节，SHA256 b6b11977b5914a6cf857793f5b77ef7b69ee68b58a73c6986d0bc95ce0589686。旧6851行逐字保持，其他165活动源、12受保护输入、7630历史证据与HEAD未改。当前边界维持上文限制，不将SEM/MBOX头数据关系的局部保持晋级成整API或全局不变量。


## 清理

已先逐路径／类别／大小／SHA确认全部目标，再清理69个专用一次性文件，共21,541,763字节：工作树新Coq产物50、开发临时树18、具有逐字保留快照的一次性generator1。903个基线缓存路径全部保留，不声称缓存字节不变。生产源／probe／gate／测试／中文文档、成功及失败证据、精确开发快照、依赖和用户数据保留；gate01／02及配置源码临时树按各自manifest清理，另计。详见cleanup-plan.json与cleanup-result.json。
