# 阶段26：同一次完整返回的当前指针权限与共享核心

本报告仅授局部空间资源保持信用，不授完整内核不变量、初始化、API/ISR 保持、正常无锁调度、C 前端、源码级 GOOD_OS 或同程序 K1–K4 闭合信用。阶段一未完成，uC/OS-III 未启动。

## 固定对象与修改

- 固定 uC/OS-II V2.93.01，上游提交 `0c4a48e6fbc6e915714e816196619a5481accf0c`，只保留两类既有授权修复。
- 重新执行实际配置后 Clang 定位，`OSTaskChangePrio` 函数 SHA256 为 `c29b633e71cf54c2d244eb87c7a5910a1f2973e6cd23d7a23769070b24bc2dbf`；冻结修复程序身份不变。这不是验证过的 C 前端或标识符翻译。
- `V293CriticalReturn.v` 保留原7252行逐字前缀，追加278行至7530行／500,625字节，SHA256 `accba980a6b7edcb6532f698dd43e6e9c8b27ecd89577fa0608f962714a0d2f2`。
- 仍166个活动源。其余165源、12个受保护输入和7936个既有 audit/scripts/tests 文件按本轮基线检查，不修改旧证据、测试和门禁，也不重绑正式覆盖身份。

## 最小证明链

1. `V293_ptomvallist_other_block`：空间编码片段不占其他块。
2. `V293_owned_block_frame`：从真实子资源、支持集和整块逐地址的权限／值相等，推导同一子资源仍可分离出来。不是从 typed load 推回权限。
3. `V293_current_owned_frame`：提取入口 `CurTid` 的实际读取片段；该块未被修改时，允许 caller、控制状态、抽象状态改变，运输该片段到出口。任意物理 `R` 不承诺保持。
4. `V293_current_fields_reconstruct`：`CurTid` 的抽象资源为空，共享字段的物理资源为空；用正交的真实资源片段重建 `CurTid ** shared_fields`。不能泛化为任意两断言的合并规则。
5. `V293_critical_event_current_owned_execution`：只调用一次旧完整执行根，沿其实际同一 `Mf/Os'/OO'` 的块 frame 和最终字段组合上述链，保留全部旧输出。

入口有明确加强：共享字段前提改为 `(CurTid current ** shared_fields ...) ** R`，另要求当前指针块不属于写集合或待释放 locals。原数值、布局、可写、任务／事件及 continuation 前提没有删除。旧接口逐字保留，不宣称两接口的入口相同。

共享核心仍是既有的较弱组件：不内置 current 必须 ready，也不提供物理 TCB／链表、ready 位图、优先级数组和 ECB 的完整全局合法性。旧根关于 ready 成员的条件结论保留。

## 同一输入与同一完整返回

新 probe 保留上一轮普通选择器8、等待目标 `(41,8)`、抽象 ready current `(60,0)`、标准 `OSTCBCur` 指向存储块80的原始内存。先由实际安装的完整编码字节构造读取半份额，再构造完整入口空间前提；没有把旧 `CurrentProbeExecution` 的完成结果充当这次加强后接口的入口证明。

字面接口实际调用新一般根。出口保持目标8→6仍等待、ready16/0不变、事件0/1→64/0、SEM类型3／计数0／NULL、返回0、caller恢复和locals释放；同一出口具有已更新字段与 `CurTid` 的空间组合。另一个消费定理把它封装为现有 `V293_shared_core ** Atrue`，同时排除当前指针所有权指向等待目标41。

`OwnershipProbeEmptyCannotOwnCurrent` 独立证明空物理内存无法持有任何 `CurTid ** Atrue`。它与同次返回上的错误当前任务排除定理是语义证明，不以门禁中固定 Proof 拒绝替代。

例子的 run/ISR/lock 为1/1/0，实际调度调用仍受阻。ready 的 current 成员是抽象成员见证，未建立其完整物理 TCB 链表合法性。

## 检查记录

开发隔离前缀和正控成功，生产实际 coqc 成功。7次正控开发尝试的全部快照和日志保留，含语法、隐式参数、`addr` 展开和空资源包装诊断。旧10个 probe 在新生产身份下均实际编译成功；新 probe 的第1次在编码 merge 的 option 化简失败，第2次在等价地址表达式的 rewrite 匹配失败，第3次成功。没有把失败重命名为成功，也未在新 probe 成功前启动正式 gate01。

正式门禁、全量测试和清理结果在本报告下节记录；原始证据目录为 `audit/logs/stage26-current-ownership/`。

## 正式门禁与回归结果

- gate01退出0，19项实际检查符合预期：生产coqc1、隔离FrozenPrefix/PositiveRoots coqc2、11probe coqc、2次预期负控拒绝、3次coqchk。
- 191个不同路径输入保持；隔离正控仅导入不含本轮后缀的FrozenPrefix及依赖，不导入候选生产模块。5个正控根和7个新probe根打印假设并集均仅 `Classical_Prop.classic` 与 `FunctionalExtensionality.functional_extensionality_dep`。
- DroppedBlockFrame只移除局部块相等前提，整个目标Proof后缀逐字保持；45行开始，50行首次拒绝。ChangedCurrent只将最终CurTid指向等待目标，入口保持，整个目标Proof保持；277行开始，301行最终tauto拒绝。均 `downstream_credit=false`。不是C突变验证、一般不可证明性或所有下游机制有效性证据；独立语义空内存／同次错误指针定理另行提供证据。
- 新7项测试实际全通过。全量 `Ran 918 tests in 51.786s; FAILED (failures=307, errors=1)`。308个诊断与本轮追加后旧911项按重数完全相同，未新增或移除诊断；相对于前轮911项的306个旧诊断，新增的2项已逐条trace核对为历史当前任务一致性报告生产SHA过期。原门槛、旧证据与所有失败不改。
- 增量make退出0，仅COQDEP且无Coq重编；不授source-only全量干净构建信用。范围审计、冻结源码只读检查、diff通过；默认audit仍2（stale function evidence input identity），正式六阶段仍94/1/1/1/1/0。

## 清理、反向审查与后续

已先逐路径／类别／大小／SHA确认完整删除集，再清理84个一次性文件，共24,612,534字节：新工作树Coq产物60、隔离开发树24。开发树4个临时源均有逐字保留快照和provenance；903个既有缓存路径全部保留，不声称缓存字节不变。源码、依赖、用户数据、凭据以及全部成功／失败证据保留。正式门禁与配置源码临时树按各自manifest清理、另计。清单为 `cleanup-plan.json`／`cleanup-result.json`。

逐项反向审查记录见 `adversarial-review.json`：入口加强、同次执行、资源不可复制、共享核心与完整不变量的区别、受阻调度、负控信用边界及陈旧身份均有明确限制或独立检查。

下一步把物理ready/TCB/event关系与本轮共享核心组合为可供API保持使用的接口，再接正常无锁调度、ISR及初始化。源码级GOOD_OS和同程序K1–K4仍开放；阶段一未完成，uC/OS-III未启动。中文教程：`docs/开发中/从指针读数到共享核心的权限保持.md`。

## 文档与清理后复验

新增7项再次全部通过；全量实际 `Ran 918 tests in 50.212s; FAILED (failures=307, errors=1)`，308个诊断与清理前按重数完全相同。最终范围审计、冻结源码只读检查及diff均退出0，默认audit仍2；903个既有缓存路径全部保留，无本轮新缓存残留。最终165／12／7936项、191项门禁输入和HEAD保持；正式六阶段及目标未晋级。机器可读核对见 `final-integrity.json` 与 `final-tests-comparison.json`。
