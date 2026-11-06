# 阶段29：真实 OSTimeTick 的未到期递减路径

## 目标与实现

按老师要求仍先完成固定 uC/OS-II V2.93.01 的整核源码级 GOOD_OS 和同程序K1–K4，再开展uCOS3；本步不改变最终目标。

沿用固定 `os_core.c:937–1008`，源身份 `74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da`，配置后函数体SHA256 `6103dfdd986ce129a03e1b8919997bea850989041632905f3d0ee0962ae1d251`。实现前冻结10890项已有文件及单因素协议，见 `audit/logs/stage29-time-tick-countdown/`。

新增 `V293TimeTickCountdown.v`，复用原AST与字段／所有权／执行帮助引理，不改旧169个活动源或C/config/port/framework/tactics。新模块仅在 `_CoqProject` 末尾登记一行；共170活动源＝67目标＋103框架／tactics。

稳定接口 `V293_tick_countdown_iteration_owned_execution` 要求 `2<=d<=Int.max_unsigned`，局部ptcb完整指针权限、实际Dly／Next字段权限和任意分离R。它构造Dly store得到M1，从M1所有权重新取得指针、Dly和Next读取，证明第二个判断为假，再构造ptcb store得到Mf。实际loststep执行完整循环体；Dly减一、最终ptcb、节点与R均在同一Mf归还，IE／控制栈恢复；两个写范围之外内存保持。既不是给出成功store／执行前提，也不是拼接两个独立存在的终态。

## 非空入口与反对性检查

字面入口用编码字节独立构造，当前节点 `(81,8)`、不同后继 `(82,12)`、非空控制栈、任意初始IE。Stat=SEM、StatPend=OK、ready group／row=8及额外99作为R中的资源，在同一Mf读回。额外执行定理覆盖2→1与4294967295→4294967294。不是完整TCB／抽象等待关系／初始化可达实例。

预登记两项单因素负控：

- 仅把算术辅助根下界2改为1，整个后续原文不变；在减一后非零的算术根被拒绝，不给执行链下游信用。字面算术根另明确1减一为0。
- 仅把主定理最终Dly load结论从d−1改为d，完整主定理Proof后缀及其入口／模型不变；在最终readback连接被拒绝。

开发编译的三次失败与整源快照保留：过度归约后无法改写Int.eq；框架exists tactic不接受逗号；写范围的加法表达式需算术归一化。第四次编译成功，未修改框架或旧证明。

第一次完整门禁 `gate01` 的五条Coq命令已达到预期，但新harness把正常的 `Cannot find witness` 算术失败误判为缺失依赖，未进入kernel检查。失败日志、原runner快照与原因保留。修正新harness使其精确拒绝namespace／inconsistent-assumption错误，并额外要求算术拒绝的确切诊断及行号；所有检查从新目录 `gate02` 重新执行，不重写gate01。不修改既有假设解析器或白名单。

## 信用边界

只处理循环体中未到期递减路径，没有完整函数Hoare、guard／整链表／时间递增／hook／ISR交错／初始化／完整Inv／GOOD_OS信用；Dly=1的到期执行仍开放。语句模型是已有手工C映射，不是已验证C前端或机器码证明。复用既有.vo依赖，不声称当前170源source-only全仓干净构建。正式六门仍94／1／1／1／1／0，uCOS3未启动，未提交或推送。

## 回归与下一步

旧1007测试358失败、1错误：上一轮358项诊断全部保留，新增1项是stage28门禁输入检查发现 `_CoqProject` 新登记导致hash变化，不重绑旧证据。范围只读核对通过；冻结C首次误用了不存在的脚本名，退出2及日志保留，改用既有 `freeze-v293-source.py` 的只读默认模式后通过。默认 `make audit` 仍exit2，原因 `stale function evidence input identity`；没有运行check-functions重写旧身份。

最终编译／独立kernel、六根假设、新测试、清理后全量回归及清理记录见本轮 `final-report.json`。失败状态不能因局部证明成功而改称全仓通过。

下一步证明Dly=1：真实递减到0，再连接Stat清位／独立StatPend／suspend／group和row写入及联合返回，之后再向全链表和整核不变量推进。

[中文教程与已填表格](../docs/开发中/时钟中断如何跳过零延时任务.md#已继续非零延时但减一后尚未到期)。

## 最终实测

`gate02` 七条命令全部达到预期（四次正向编译、两次负控拒绝、一次独立coqchk检查两模块）；生产两根／字面四根的假设检查只含既有classic、functional_extensionality_dep或全局闭合。新增9测试全通过；清理后全量1016测试仍358失败、1错误，按kind／id重数与本轮旧1007测试的359项诊断完全相同。不是全仓测试通过。

按全部目标的类别／大小／SHA先清单、全体核验再首次unlink，清理534项（507软链接、27实文件／676441字节）和57目录；只涉及三棵隔离负控树、三个audit probe的15个编译产物及一个重复快照。源、实际成功／失败日志与快照均保留；原845个依赖产物不改，新生产模块5个可复用依赖保留。`git diff --check`通过；HEAD未变。
