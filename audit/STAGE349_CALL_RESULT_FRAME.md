# 第349步：保留调用者资源并执行真实返回值赋值

## 这一步解决什么

此前的真实`sfexec`入口已经连接TCB初始化和原抽象创建步骤，但后置只有`shared_ready_records ** Atrue`。它不承诺保留调用者`err`单元的明确所有权，不能凭空再假设有一个可写`err`，也不能另跑一次初始化得到不同的好堆。

新稳定接口：`V293_OS_TCBInit_call_assign_shared_under_hooks`，生产文件为`certiucos/v293/proofs/V293CallResultShared.v`。

它从带真实`kassignr (evar err) Tint8 ks`继续体的函数入口出发：

1. 使用原九局部分配／实参写入／CPU_SR初始化，得到`Mi`，不在入口预先要求这些局部单元。
2. 原连续初始化／发布／释放接口只调用一次，得到同一个`Mr`上的真实执行和强就绪payload。
3. 在`Mr`上调用原创建桥，构造原`hpcrt_step`以及独立客户状态`clientM'`上的参数分配／写入／读取。
4. 不使用创建桥丢掉frame的弱后置，而从同一`Mr`的payload加当前指针、其余可写单元，重新打包原共享谓词，保留调用者frame。
5. 真正执行返回赋值，从`Mr`构造`Mf`，使`err`变为零，同时保留整个共享就绪谓词及其余返回资源。

输出保留`V293_TCBInit_return_frame ++ before ++ err(0) :: afterframe`，不是仅给一个load等式。`clientM'`和内核`Mf`是原语义中的独立状态分量，不把客户分配当成修改内核堆。抽象创建与物理返回依然是对应的两条轨迹，尚未包装成整个调用者的`TaskSim`。

## 为什么资源没有被复制

`V293_return_ready_current_keep`把当前指针的一个读半份用于`CurTid`，另一个半份留在`Atrue`，保留其余raw cells。新共享打包先证明payload加当前指针不占抽象槽，再对raw cells的纯物理部分保留原内存，仅丢掉其`Atrue`承载的旧抽象状态，最后放入更新后的四个原共享槽。

这不是对任意断言进行抽象状态替换：`V293_return_raw_abstract_reset`只接受`V293_rdy_raw_cells cells Atrue`，通过归纳重建每个原物理所有权，不允许保留旧抽象数据断言后再复制到新槽。

真实赋值复用原`V293_return_value_assign`，以原完整`V293_shared_ready_records`作为frame。没有假设store成功、没有假设赋值后的好堆，也没有改写原谓词、执行规则或C源码。

## 闭合对照：只省略赋值

事前协议为`audit/logs/stage349-call-result-frame/protocol.json`。`CRSAssignmentContrast`复用原字节级非空任务／强就绪fixture，实际分配并写入调用者`err=66`，取得一个无外部执行前提的返回入口；再执行真实返回赋值。

同一个返回堆、调用者环境和完整共享就绪frame不变：正向实际写入后load为0且保持共享frame；负向只省略这次赋值，原堆load仍为66，不是0。这不是缺函数或某个早期门拒绝，因而只给返回赋值本身授予验证信用。初始fixture包含两个任务及真实位图／13槽表，不是空映射的真空证明。

该入口是独立的返回现场，不是完整两hook调用的可达实例；不能把这条闭合赋值轨迹冒充整条有hook前提的调用链已经闭合。

## 核实出的运行期预留槽缺口

固定上游`Source/os_task.c`第382–392行：`OSTaskCreateExt`在空槽检查后先将`OSTCBPrioTbl[prio]`写成`OS_TCB_RESERVED`，然后调用栈初始化和`OS_TCBInit`，并将返回值赋给`err`。

第346–348步沿用的初始化profile却要求`nth p entries Vnull = Vnull`，并持有该槽的`Vnull`。`CRSReservedSlotBoundary`检查同一物理堆不可能同时满足“该槽load是预留指针”和“该槽拥有null”。因此新接口仍是null-slot初始化profile；虽然确实执行了调用者的返回值赋值，**不能直接与真实运行期预留槽前缀拼接**。

这不是发现C代码错误，而是已有证明接口对运行期入口不适用。后续应给预留槽引入准确的暂态关系并证明真实覆盖写入后恢复原强不变量，不能把真实预留写入删除、把预留指针当null或削弱最终共享谓词。原始字节、源码身份和旧证据均不改。

## 仍未完成的边界

- 两个原CPU hook契约仍作为前提；固定树只有声明，未提供实现，不伪造空实现。
- 入口实参已经求值，九局部块互异／新鲜、当前线程和`spec_crt`仍是前提。
- 未闭合运行期预留槽入口、整段`OSTaskCreateExt`成功分支／调度／返回或整个`TaskSim`。
- 未证明冷启动`OSInit`、完整链表强不变量、真实ISR的`WFInt`或具体内核`GOOD_OS`。
- 同程序K1–K4及uCOS3未完成；总目标继续active，不登记`full_target_linked`。
- 非验证前端、ADR0005及既有审计问题保持原状态。

## 验证与失败保留

本步新增生产／探针逐根信任检查、递归`coqchk`、重复编译、构建、自动检查和两轮全量回归；实测只以`audit/logs/stage349-call-result-frame/verification.json`为准。所有失败候选、源快照和日志保留。旧测试和冻结证据不修改；必要的工程追加注册可能使旧的精确注册快照失败，这种失败仍计入增量门，不豁免。

新增测试使用保留旧工程前缀且新文件只注册一次的检查，允许后续合法追加；本步冻结时另核对精确新增行，避免再制造无语义必要的未来快照失效。
