# 阶段26：同次成功返回的位图联合资源与完整权限

## 固定对象与范围

仍验证固定配置的 uC/OS-II V2.93.01，上游提交 `0c4a48e6fbc6e915714e816196619a5481accf0c`，仅保留原两类已授权修复。repaired C 身份 `74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da`。不修改 C/config/port/framework、正式覆盖、旧测试／门禁／证据、假设白名单，不重绑历史报告，不提交 Git。

实现前的 `audit/logs/stage26-bitmap-permissions/baseline.json` 冻结167活动源、12项保护输入、8914个历史文件、835个既有缓存路径和HEAD。本轮只在 `V293TaskRecordOwnership.v` 原1528行之后追加；其他166源逐项保持。手工AST与配置后源码、端口归一化仍沿用既有边界，不授已验证C前端、编译器或硬件信用。

本轮只处理选定成功路径、受阻调度、实际尾部返回与local释放，以及ready/event六字节的联合空间资源。不是完整TCB、完整event、完整priority table、链表或分配器所有权；未与上一轮CurTid／全部任务字段／shared_fields归还组成一个联合执行根。两个定理分别存在的Mf不能直接视为同一终态。不是完整Inv、初始化可达性、所有API／ISR、正常无锁调度、源码级GOOD_OS与同程序K1–K4；uC/OS-III未启动。

## 为什么需要这一步

`load`成功不能推出完整写权限；半份额也能读。新证明保留独立的完整权限前提，从同一次实际更新得到权限保持，再与实际返回的非local精确frame连接。被free的local不在权限保持范围内。

- `V293_full_byte_load_encoding`：已有完整权限时，用真实typed read确认byte编码。它不制造权限。
- `V293_full_byte_cell_owned`：从完整字节分离真实singleton，再构造一个空间单元。
- `V293_full_byte_cells_owned`：对地址NoDup的字节列表逐个分离singleton并保留其余字节，得到一份联合资源。不是把若干独立的 `cell ** Atrue` 直接拼起来。
- `V293_bitmap_layout`：只枚举ready两行／group和同一个event对象内的两行／group，复用原record cell表示。
- `V293_critical_event_return_bitmap_owned`：原入口前提不变，只调用一次已有实际update execution和一次tail return；同一个Mf同时满足实际执行、原loads／frames／free结论、非local完整权限保持、ready/event六字节联合所有权。

五store模型用于整块精确frame，不是第二次API执行。新根未引用旧完成执行定理作为oracle，也未假设最终内存满足待证资源。

## 字面入口与终态消费

`V293BitmapOwnershipProbe.v`重新构造真实入口，不调用旧完成执行trace。任务 `(41,8)` 从优先级8改成6，但仍等待SEM `(72,5)`，delay1、非空消息 `(120,7)`不使其ready；另一个任务 `(60,0)`仍ready／优先级4。run／ISR／lock为1/1/0，仅受阻调度，不是正常无锁切换。

同一次返回后ready16/0／group1不变，event0/1／group2变为64/0／group1，priority table新槽指向目标、旧槽NULL，返回0、caller恢复、locals释放。

六个probe根分别验证：实际返回与六字节联合所有权／两个四字节priority槽完整权限；任意成员字节的实际store及联合空间资源更新；两个priority槽分别存在pointer store；同一内存排除旧event位图；半份额可读但不能构造完整所有权或写入；已释放local不能写入。两个槽的store存在量词是分别的，不代表顺序执行；任意后续写不保证保持内核Inv。priority槽权限不等于完整priority table空间所有权。

## 前瞻消融与可反驳边界

实现前 `protocol.json` 固定以下单因素控制；整个目标Proof及其后缀保持，不改其他前提或门禁：

| 控制 | 唯一改动 | 信用边界 |
| --- | --- | --- |
| FreedLocalsRetained | 删除新执行根最终permission结论中的非local guard | 预期拒绝；downstream_credit=false，不推断所有后续机制都有效。 |
| ReadOnlyCreatesOwnership | 单字节空间构造器的完整权限前提改成半份额 | 预期拒绝；downstream_credit=false；另用实际半份额反例验证不可写。 |

隔离Positive包含整份候选源，不能导入候选自身替代重证。生产模块、新probe、隔离Positive分别coqc和独立coqchk；沿用旧假设白名单。开发加速文件导入旧生产模块，只作开发证据，不代替最终整源重证。所有失败候选、诊断和成功快照保留。

开发失败包括：缺少精确imports、byte编码算术归一化、implicit参数、frame等式匹配、asrt scope下list语法、分支tactic展开及Ltac局部名匹配。均在新追加证明／新probe中修正，原1528行、旧门禁和冻结协议不改。具体候选见同目录development快照及日志。

## 验收与清理

生产源1861行／119,434字节，原1528行逐字保持，追加333行；SHA256 `fafb787168450426e1f6039ac1649edd362d1bb1179ffeb780da82ee459a7060`。新probe349行，SHA256 `087b7786ac253cfb4c02205d427c15f71d6ba119ade4ad24e2bca08db21a8e1e`。新旧执行根的完整入口契约经空白归一化后相同，未新增最终权限或执行oracle。生产整源编译通过，16个旧fixture逐项重编均退出0。

新probe01在旧event排除定理处因无法从Mf反推完整状态参数而失败；probe02只在两处load lifting调用显式指定s后通过，定理头不改。失败及成功快照／日志均保留，不把它解释成运行时内核缺陷。

`gate01`实际退出0，8项符合预期，199个冻结输入保持：

| 实际检查 | 退出码 | 秒数 |
| --- | --- | --- |
| Production coqc | 0 | 197.54 |
| 隔离完整源Positive coqc | 0 | 210.95 |
| 新Probe coqc | 0 | 16.25 |
| FreedLocalsRetained | 1（预期拒绝） | 152.36 |
| ReadOnlyCreatesOwnership | 1（预期拒绝） | 149.56 |
| Production独立coqchk | 0 | 213.52 |
| 新Probe独立coqchk | 0 | 226.69 |
| Positive独立coqchk | 0 | 214.17 |

FreedLocalsRetained的Proof从1748行开始，1783行拒绝：实际Surviving带非local guard，不能提供删除guard后的无条件permission结论。ReadOnlyCreatesOwnership的Proof从1562行开始，1564行拒绝：半份额前提不满足真实完整字节编码桥。两者整个目标Proof后缀保持，downstream_credit=false。不能从这种早拒绝推断每个下游机制都有独立检测能力。

4个正控根和6个probe根的假设并集仅classic、functional_extensionality_dep，旧白名单不改。三个独立coqchk目标分别为生产模块、新Bitmap probe和隔离Positive，不以旧probe替代。

新增6项测试实际通过。旧958项和全量964项均334失败1错误，335个诊断按kind/id重数完全相同。与上一轮全量958项的332个诊断相比增加3项旧current-all测试：生产源SHA、生产快照、负控快照身份过期；逐条trace见diagnostic-comparison.json。原332个诊断全部保留，不能将全体335项统称为快照问题。未修改旧测试或重绑历史证据；本轮新测试通过不等于全仓通过。

范围审计、冻结C只读重验、diff检查实际通过；默认make audit仍退出2：stale function evidence input identity。正式六阶段94／1／1／1／1／0保持，不因本局部结果晋级。增量make build退出0，仅COQDEP／nothing-to-be-done，没有当前SHA的source-only全仓干净构建；旧构建身份不可套用。

### 一次性材料清理

全部验收和回归结束后，先完整列出116项path／category／size／SHA，逐项确认，再对整个集合重核，才首次删除，共11,771,546字节：85个fixture／probe一次性Coq产物和31个任务专用开发源／产物。开发源先保存精确快照，所有成功／失败日志保留。初始cleanup-plan保留；门禁重编新probe后只刷新其aux／vo身份，另存cleanup-plan-final和refresh记录，不覆盖旧计划。

835个既有缓存路径、生产模块5个可复用产物、全部源／依赖／成功失败证据保留，用户数据和凭据不动。gate隔离树12项／4,546,112字节另按完整manifest整体核对后清理。清理结果见cleanup-result.json和gate01/temporary-cleanup-plan.json。最终文档与清理后的复核见下节记录。

## 下一步

将同一次执行中的位图与priority table空间资源，和CurTid／全部任务字段／更新后的shared_fields真正联合归还；不能直接拼两个独立exists Mf。随后推进正常调度、其他API／ISR、初始化与顶层GOOD_OS／K1–K4。中文入门与已填表见[位图可读为何还不等于返回后可写](../docs/开发中/位图可读为何还不等于返回后可写.md)。

## 文档与清理后的最终复核

清理并追加中文检查点后，再次实际运行全量964项，51.57秒，仍334失败1错误；335个诊断与清理前按kind/id重数完全相同，无新增／删除，新增6项仍无诊断。范围、冻结C只读、默认audit、diff最终退出码为0／0／2／0。final-integrity.json确认其他166源、12项保护输入、8914个历史文件、199个门禁冻结输入、HEAD和旧文档正文保持；835个既有缓存路径仍在，116个清理目标仍不存在。未增加证明逃逸、未晋级正式覆盖、未完成总目标。
