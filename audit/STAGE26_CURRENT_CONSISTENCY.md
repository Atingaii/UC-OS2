# 当前任务纯对应穿过同一次完整返回

本轮固定V2.93.01、原配置和两授权修复，不改C/config/port/framework、旧门禁、旧测试、旧报告或正式覆盖。原7054行逐字前缀保持；baseline的166活动源中其余165、12受保护输入、7829历史文件及HEAD要求不变。903个既有缓存路径保留，不声称缓存字节不变。

## 前瞻协议

`audit/logs/stage26-current-consistency/prospective-protocol.json`先于生产／probe编辑及正式gate落盘。先实际重新执行配置后Clang定位、核对两授权修复与函数SHA c29b633e...，不授C前端／ABI信用。

复用现有块frame、共享字段所有权及普通任务表单点更新，不引入第二套current概念。追加一个就绪成员保持lemma及完整执行适配接口，旧根只调用一次，所有原始入口条件、输出和同一Mf/Os'/OO'保留。新增的是条件式纯对应，不从load反推拥有权限的CurTid，也不假装入口共享不变量已建立。

新具体入口另外构造：选择器8，当前指针块80存ready60而非wait41；标准OSTCBCur标识符60显式映射到该指针块。抽象current60、tasks、events均不改；逐项重建全部执行前提，不复用另一输入的完成trace。run1/ISR1/lock0仍是实际受阻调度；正常调度未接入。

两个预定负控分别只改变最终物理指针、最终抽象current为等待目标；保持完整目标Proof。downstream_credit=false，只授固定Proof结论敏感性。另以同一次完整Mf/OO'的语义定理排除错指针／错current，并保留旧入口41/60错配反例。隔离正控只导入不含目标根的FrozenPrefix和依赖，不能导入候选生产模块。

## 已保留的失败

production01失败于直接将`get OO'`目标交给以`get(getabst s)`为结论的通用lemma，Coq无法反向推断完整state。保留完整失败源和日志；修正为显式完整state的可转换目标，不改变命题、旧前缀或执行条件。依赖编译在该失败后尝试导入生产模块，因.vo不存在而失败；记录保留，不授依赖编译通过信用。

全量旧903项在追加后实际305失败1错误。对照前轮304个诊断，全部按重数保留，新增两条trace均为上一轮生产快照／门禁输入SHA过期，不是被删除或弱化的语义反例；见added-diagnostic-01/02.log。未将旧快照重绑到新源码。

## 边界和下一步

仍缺CurTid物理权限与共享不变量保持、正常无锁调度、API／ISR保持、初始化、同程序K1–K4及源码级GOOD_OS。阶段一未完成，uC/OS-III未启动。正式六阶段仍94／1／1／1／1／0；默认审计仍须保留真实失败。实际结果见下文，不将局部通过计为整核完成。

## 开发补充

probe01把仅支持Tint8的旧写字节load lemma用于指针读取，修正为完整块frame；probe02遗漏旧probe的局部tactic定义，显式保留所需三项本地tactic；probe03/04揭示普通选择器的SELF条件已经被既有discriminate自动关闭，原手工SELF bullet因此错位，诊断Show的实际goal和失败源保留，移除该多余bullet及无用SELF中间断言；probe05补齐新内存到旧payload内存的frame；probe06的反例定理中op没有出现在结论，需显式标注spec_code类型。未改入口条件或最终语义结论。probe07实际coqc退出0。所有快照／失败日志保留，正式gate在注意到probe07终止0之后才启动，不重演上一轮提前启动的问题。

## 实际门禁结果

生产源现7252行／481,555字节，SHA256 `5b134f38afad34e6de8027c9d32dc0c1816417ae23e14d5f6301b26def9fb72c`。原7054行逐字保持，新增198行。候选源、probe、脚本及测试的精确身份见candidate-identity.json；开发检查快照不冒充正式门禁，正式证据是gate01/result.json及该目录实际日志。

gate01终止退出0，18项检查符合预期：生产＋10个probe共11次coqc、隔离FrozenPrefix和完整PositiveRoots两次coqc、两次预期负控拒绝、三次coqchk。190个不同路径输入保持；分类归属为166活动源＋10probe＋12受保护输入＋Before／baseline／gate三项＋2helper，共193项，扣除3个重叠受保护源。隔离树已按逐文件manifest清理。2个正控根和7个新probe根实际打印假设并集仅classic与functional_extensionality_dep。

两个负控完整目标Proof均从172行开始，208行最终tauto首次拒绝。由于最终tauto合并所有结论，这只说明该固定Proof不能完成被替换的后置，不单独归功于每个中间机制；downstream_credit=false。对应的物理／抽象错指针排除另由同一次完整返回的CurrentProbeReturnRejectsWaitingPointer提供语义证据。旧入口41/60错配由CurrentProbeOldInputMismatch明确保留。

## 测试、范围与清理

新增8项测试实际通过。完整911项仍305失败1错误；full-tests-comparison.json确认与本轮旧903项基线的306个诊断按重数完全一致。相对上轮的两项新增历史SHA过期已保留trace，旧测试／报告没有改动。增量make退出0，仅COQDEP，没有Coq重编，不授source-only全量干净构建信用。范围／冻结源码／diff检查通过，默认audit仍2，正式覆盖不晋级。

在实际coqc／coqchk、测试和增量make之后，先确认完整删除集合的路径／类别／大小／SHA，再删除67个本轮专用一次性文件，共22,895,640字节：55个工作树新Coq产物和开发临时树12个文件。两份开发.v均有逐字保留快照；903个基线缓存路径保留，不声称字节不变。正式gate与配置源码临时树另按各自manifest清理。源码、依赖、用户数据、全部成功／失败日志和快照保留。见cleanup-plan.json／cleanup-result.json。

文档与清理后已实际复验：新8项再次通过，全量911项仍305失败1错误，306个诊断按重数完全相同；范围／冻结源码／diff通过，默认audit仍2。见post-docs-command-exits.json、post-docs-test-comparison.json及原始日志。最终完整性结果另记final-integrity.json。
