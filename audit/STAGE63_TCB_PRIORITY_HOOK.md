# 第63步：首Hook返回后写优先级表，到第二Hook实参求值

## 1. 固定对象与最小接口

仍为uC/OS-II V2.93.01、既定配置与两类授权修复；C、配置、framework、旧生产源码／证明／测试和旧证据不改。fresh物化94项函数身份与冻结输入相同，source identity为`74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da`。OS_TCBInit仍为os_core.c:2022..2151，源码片段及Clang AST保存在本步source目录；继续使用第61步保留的完整手工归一化函数。新增唯一活动源为`certiucos/v293/proofs/V293TCBPriorityHook.v`。

稳定无条件片段接口`V293_OS_TCBInit_priority_to_second_hook`只要求首Hook返回锚点的locals／global绑定、p<13和三个精确可写单元加任意frame，不要求调用者提供内部执行结果。它实际展开原full-function continuation、enter、计算数组地址、执行赋值、exit、scall与实参求值，停在第二Hook的sfexec；同Mf保有更新槽与frame，任意IE／si／ci恢复。片段不要求P含外层函数定义，因为未执行外层lookup；上层条件接口另要求实际P f绑定。

三个单元为priority byte、ptcb pointer、所选表槽。旧槽无需typed-load，可为Vundef；本步只描述赋值，不证明OSTaskCreateExt是否准许覆盖已占用优先级。第二Hook缺定义时同终点无loststep。

## 2. 条件纵向连接不等于真实Hook实现

`V293_OS_TCBInit_call_to_second_hook_under_contract`复用第62步由M自动构造九fresh块的入口证明，然后显式要求HookReturn：在实际callee环境及Mi中从首Hook sfexec真实运行至返回锚点Mr，且保持18字段、8参数／局部单元、两链接、saved0、表槽与caller frame。它不要求Mi=Mr，允许未拥有内存变化；但这些精确保护条件是否适用于未来端口实现仍需验证。

真实Mr接入本步赋值获得Mf，三轨迹用同P、同状态连续组合，条件并非公理。不过固定输入五个端口Hook只有声明，HookReturn尚未证明；条件定理不能视为真实源程序已执行成功分支。`V293_missing_hook_cannot_return`证明缺定义时不存在从该sfexec到skip的local_steps，包含对零步伪返回的排除。没有造noop、测试Hook或新增受信契约。

## 3. 独立有限内存与反证控制

独立probe不导入其他probe；逐项列出priority201、ptcb202、table310、ready group401=2／row402:1=2、count403=7、caller601=77／602=88，TCB值为301:8。表邻居310:0为NULL、310:4为398:16；选中槽为p12:48或p11:44，旧值为399:8或Vundef。四份内存、IE任意，每份10项typed-load；IE两值共8参数实例、80读回，不是8次coqc，也不是两个任务共存。

此fixture的首Hook返回锚点是合成入口；缺Hook程序下没有证明它从函数入口可达。测得ready／count未变化只表明本片段未发布，不证明所有其他内存未变或任务已可调度。

positive及三项只改终点结论的负控均执行前冻结，全部证明体相同。错误第二Hook指针、表槽、caller字分别在34／48／62行拒绝，仅验证接口终点敏感性，不授机制消融信用。

## 4. 单因素消融与保留的失败

只将实际待执行continuation中的表槽赋值替换为skip，enter／exit、两Hook语法、publication尾部和原kcall full body均保持。cursor仍为skip，P、GE、LE、输入M、p11／p12、参数、IE／si／ci相同；起点continuation仅此语句不同，终点代码与第二Hook实参完全相同。实际执行所选槽为301:8，变体保留399:8，七frame单元及IE／si／ci不变，只授本条写入信用，不授Hook执行、任务准入、发布或return信用。

ablation01因未显式import V293_TCB_publish失败；02补imports后暴露生成器将helper结论执行M误替换、所有权仍Mf的断链错误。没有修改旧失败证据：plan03前瞻冻结更强的共同Mf连接，外层AblatedConcrete／AssignmentEffect测量语句、fixture、因子及所有版本Proof体逐字不变，03通过。未削弱门槛或删除不利结果。实验检查脚本验证全部差分。

生产proof01..07调试失败、08仅片段通过、09含条件接口、10新增no-return证明tactic失败、11最终通过；全部保留。probe01缺import；02／03均在首单元分离性证明处失败，03已将首单元值显式实例化而仍失败；04在03基础上只修证明tactic展开byteval后通过，原fixture／结论不变。最终以proof11、probe04及正式build／trust记录为准，不从早期局部pass推断后续机制通过。

## 5. 信任、回归、清理与未闭合目标

223源增量构建复用1110旧产物，保留1115生产产物；不是cold build。50个Print Assumptions根（含三个新生产定理、两个probe根）及framework顶层／新生产模块／probe三模块coqchk，5项新增测试、完整回归、396条旧诊断逐ID比较、缓存精确恢复和旧14559文件保护，以`audit/logs/stage63-tcb-priority-hook/final-report.json`及manifest为准。默认审计旧失败不删、不改门槛；新假设只使用既有框架允许项。

仍是手工前端、ADR0005临界宏映射和CPU_SR token字节擦除，不是verified frontend或原端口调用。定理只给存在性无交错轨迹，不是local Hoare／所有执行safety。首Hook执行、第二Hook执行、与第60步发布纵向连接、成功return／free、caller恢复、实际七调用Mf、OSTaskCreateExt／stack／function地址、OSStart及runtime Inv仍开放。正式六门94/1/1/1/1/0不晋级，源码级GOOD_OS与同程序K1–K4未完成，uCOS3未开始，目标active，未提交／推送。

任务临时目录及probe五产物在所有验证后先全盘点、再全量复查、再首个删除；保留生产可复用产物、全部源码／用户数据／凭据／旧缓存及成功失败证据。下一步必须落实真实端口边界，或继续明确标注未兑现条件的纵向连接，绝不把条件当作完成。
