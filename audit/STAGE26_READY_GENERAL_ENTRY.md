# 一般 NULL-ready 原始入口与持有抽象表的局部配对

## 目标与不变量

在固定V2.93.01目标内，保持全部原4849行源前缀，仅追加两个抽象堆运输引理及一个一般入口接口。固定C、配置、端口、框架、正式函数证据、覆盖不变。

入口：同一原始物理M，原完整NULL成功路径的全部load、写权限和分离条件；同一 `tasks` 的入口table／bitmap关系、实际目标指针ready成员、`shared_fields ** R` 与外部抽象帧。没有执行、store、free或spec_step完成前提；新优先级fresh从物理空槽导出。

出口：同一Mf的完整return0/free/caller轨迹、TCB、ready、任务表、NULL事件、明确具体frame；实际更新任务表上的抽象步骤／外部帧和 `shared_fields ** Atrue`；同一更新表的bitmap／table关系；最高ready任务及从Mf读取其指针。

不保留任意物理R；没有完整ready不变量、TCB／事件合法性、初始化可达、正常无锁切换、前向模拟、整函数Hoare或GOOD_OS信用。

## 身份

`V293CriticalReturn.v`：原4849行／316,712字节逐字保留，追加214行（含两个分隔空行）至5063行／330,382字节；SHA256 `abe6ad33db96bbfea234f9930c2cb5f76cbd76ddd0129de4bba4a0b65b256122`。新增引理／主根实际内容212行。

HEAD仍 `1f57743c638c7e1ccdcc594e51dc90c0c7406789`，166活动源；其他165源及12项受保护输入保持，未提交。历史测试、driver和三个上轮门禁结果的60项文件身份另由 `historical-inputs-before.json` 固定。

## 检查协议

前瞻协议见 `prospective-protocol.json`。固定probe沿用历史字面AST并固定一般接口，同时独立构造物理与抽象入口后实际调用新一般根；不是第二份独立实现证明，也不导入旧内核证明树。

隔离正控只导入冻结4849行前缀，不导入候选生产模块；实际编译完整追加后缀。两项单因素负控仅改主根声明，完整Proof保持：

- `NoOwnedEntry`：所有权前提改为保留R类型的True，只授首次owned primitive应用拒绝信用。
- `StaleTaskRelation`：仅将出口bitmap对应的updated tasks换成入口tasks，只授最终bitmap关系拒绝信用。

所有负控 `downstream_credit=false`。不把关联的早拒绝当作后续机制有效证据。

## 开发失败保留

- development01：误把抽象字段的空堆等式方向写反，`Not convertible`。
- development02：使用当前未导出的 `join_emp_eq` 名称。
- development03：最后空堆等式方向不匹配。
- development04／05：主动中止。04内存超过4GiB；05的逐步计时定位到 `View new ltac:(lia)`，不计成功信用。
- development06：只收窄lia的无关上下文后快速推进，最后rewrite因let展开不匹配拒绝。
- development07：用可转换的 `f_equal Some SelectedPointer` 完成；正式追加移除诊断输出。
- probe开发01：通用assumption已消掉三个关系前提，后续重复bullet不匹配；开发02移除重复bullet后通过。未修改接口前提／出口或门禁标准。

源码、失败／成功日志和文本快照保留。

## 验证与清理

`gate01/result.json` 的11项实际检查全部通过：生产／两个历史字面AST探针／新一般探针共4次coqc；生产、新探针和隔离完整正控共3次coqchk；冻结4849行前缀与完整追加后缀正控共2次coqc；两个负控实际退出1。175项输入身份保持，门禁临时树已由自身清单确认清理。两probe根、三正控根的实际Assumptions并集均仅classic和functional_extensionality_dep。

NoOwnedEntry的目标Proof在184行开始，200行实际owned_step应用因Owned只为True拒绝；StaleTaskRelation同样184行开始，233行exact FinalBitmap因旧表／更新表不匹配拒绝。完整目标Proof均保持，只授首次依赖信用，详见negative-first-rejection-review.json。

新增12项测试全部通过。完整853项实际268失败1错误；上轮841项为263失败1错误。逐重数比较，原264个FAIL／ERROR诊断全部保留，新增5个均为原4849行SHA与当前5063行SHA不匹配。分别为ready_owned的current_inputs／old_assertions、complete_return的gate_inputs、entry_witness的current_gate／historical_assertions。逐条trace与两个实际SHA见added-diagnostic-review.json，不宣称全套通过或旧门禁在当前身份重放。

project-audit、固定源码只读复核、增量make与git diff --check实际通过；增量只更新依赖扫描，无证明重建信用。默认make audit实际退出2，原因仍为正式旧函数证据input identity过期；六门94／1／1／1／1／0不变。

已逐路径／类别／大小／SHA确认并清理39个本轮一次性文件，共13,346,457字节（隔离开发树19个，工作树新Coq缓存20个）。门禁临时树由自身清单清理，另计、不重复计入39个；903个基线缓存路径全部保留，不声称字节不变。源码、probe、测试、中文文档、成功／失败日志、文本快照、历史证据、依赖与用户数据保留。见本轮cleanup-result.json。

历史门禁不递归重绑：保留旧报告原检查身份，当前追加后若旧测试拒绝旧SHA，应逐条报告，不能放宽门槛、覆盖历史证据或删除不利结果来造通过。

## 对抗性复核与边界收紧

- **所有权是否只是口头声明？** 新一般根实际消费原始M上的fields所有权；统一probe构造它，NoOwnedEntry只测该依赖。抽象当前任务字段尚未与物理 `OSTCBCur` 指针绑定；不把四字段所有权称为完整共享不变量。
- **抽象fresh是否循环引用出口？** 只用原始M的新槽NULL、入口表load和task→slot关系推导，未用出口或spec_step作为前提。
- **成功执行是否来自另一条固定轨迹？** 一般根实际应用原一般完整返回根；统一probe再实际调用新一般接口，不拿旧固定见证顶替。
- **位图对应是否等于全部TCB合法？** 不等于。priority-table只是task→slot关系，不是全部槽位与TCB双射；没有推出每个指针的TCB／事件字段一致性。
- **外部frame是否都保持？** 抽象Of有join保持，物理任意R没有；只承诺显式物理非写入、非局部frame等式及fields ** Atrue。
- **最高任务指针可读是否等于切换完成？** 不等于；统一见证仍在ISR受阻路径，正常无锁执行和准确缓存／源码switch对应仍开放。
- **两个执行是否构成前向模拟？** 这里只建立局部完整具体轨迹与一个抽象原语步骤的入口／出口配对；未证明所有中间交错、完整API规格或通用模拟关系。
- **门禁过了是否代表正式覆盖晋级？** 不代表。正式旧证据仍因SHA过期被拒绝，六门不变；本轮也不重写历史快照获得通过。
