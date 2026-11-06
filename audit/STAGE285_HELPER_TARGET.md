# 第285步：helper 调用接上目标赋值与需要切换的后缀

## 本步解决什么

第284步已证明原 `OS_SchedNew` 的调用、全部 fresh 局部分配、两个赋值、释放和返回，
但公开定理仍要求恢复后的 caller continuation TaskSim。本步直接用已证的目标赋值和
changed-priority 后缀承担该义务，得到唯一生产公开接口：

`V293_exit_helper_target_TaskSim`

起点是 `scall helper nil`，后继 continuation 为原目标赋值、优先级比较、计数与
handoff/switch、临界区退出和外层返回。结论对该调用切点建立 TaskSim；公开前提没有
TaskSim、执行轨迹、求值结果或 store/free 结果。仍要求函数绑定、环境绑定、任务映射、
当前任务缓存一致性、旧任务不是最高 ready、资源所有权等具体条件。

源码身份沿用固定 V2.93.01，`os_core.c:708–714,723,1751–1759`，详见
`audit/logs/stage285-helper-target/source-identity.json`。没有修改 C、配置、AST、
框架、ADR-0010 或旧生产证明。没有重跑预处理，不新增源码覆盖完成声明。

## 资源权限为何需要另半份

helper 的 unmap 表输入是半份只读权限；已有 switch 后缀把该表纳入共享 storage，
需要完整存储权限。半份只读权限不能直接转成完整权限。本步最小连接方式为：

1. 调用前持有两份半权限，helper 使用一份，外部 frame 保留另一份；
2. helper 返回后把两份重新合并为完整数组权限；
3. 将 unmap 的256个字节单元接到既有 rest storage 前面，交给既有后缀。

`V293_helper_decoder_storage` 证明合并，`V293_exit_helper_target_resources`
证明资源重新分区。没有丢弃保留份、凭空补足权限或放宽旧不变式。
代价是初始资源更强，而且后缀返回的共享不变式只要求表存储权限，不承诺原表值不变。
这是既有共享不变式的布局实例，不宣称已证明不同 storage 列表置换等价。

## 非空实例与单因素控制

`HTbase` 和 `HTentry` 用 ready 任务、blocked 旧任务、完整 unmap 数组、high/current/
目标指针/计数与保存区，构造真实非空物理堆。`HTnonempty_call_cut` 实例化公开定理，
使用已存在的程序绑定与 caller continuation，不以 TaskSim 结论作为前提。
该实例仍保留 getsched 的配置条件，没有由此实例化整核高层程序或初始化。

**这是构造的 helper 调用切点，不是原完整活跃调用入口可达性。** 旧完整调用 trace
只提供半份 unmap；尚需在外层入口借出/保留/归还完整表权限，才能连接该实例与原入口。
不能用本步新构造堆冒充旧 trace 的同一堆。

`HTpermission_control` 固定地址、原字节、读取和写入值，仅改变权限：
两边均能读取0，半权限写4失败，完整权限写4成功。它是局部存储权限对照，
**不是完整外层调用执行消融**，也没有单独测定两条 helper 赋值或其他下游机制的必要性。
权限合并的一般正确性来自生产证明，不由该单字节例子替代。

## 检查口径与保留失败

前瞻协议、每次编译源码快照、两次稳定编译、逐根假设与递归 coqchk 见
`audit/logs/stage285-helper-target/`，实际结果以 `verification.json` 为准。
允许的基础限既有 classic 和 dependent functional extensionality；无新增公理或占位。
保留全部失败尝试，包括直接计算抽象单例堆过慢而中断的一次；最终改用标准 map 引理。
删除重复 import 后发现 scope 顺序影响数字解析，该失败也保留，修正后重新稳定编译。

全套测试按第284步 `verification.json.full_tests_evidence` 指定的正式结果比较，
不用其首次缓存变化导致的失败结果冒充基线。保留既有434失败、1错误，逐项核对身份和顺序。
Coq/build 结束后先恢复本步开始时的既有 `.lia.cache/.nia.cache`，再跑正式全套。
README 与 VERIFICATION_STATUS 只前插说明，保留历史字节。未提交/推送。

## 未闭合的义务

- 本步只覆盖需要切换分支：仍要求 `~V293_highest_ready tasks t`；等优先级返回待连接。
- 外层 guards、完整分配入口与此调用切点的 TaskSim 尚未连接。
- `si=nil`、ISR 全清、空 LINV、ADR-0010 的既有边界不变；强 current guard 缺口不变。
- 不是无条件 WFIFun/WFInt，更不是整核 GOOD_OS；同程序 K1–K4 未闭合，uCOS3 未开始。

下一步优先把完整 unmap 所有权从外层入口带到此切点，再连接外层 guards 与等分支。
整核 GOOD_OS 与同程序 K1–K4 闭合前不切换到 uCOS3。
