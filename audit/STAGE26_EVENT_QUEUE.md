# Stage26：把事件位图连接到同一实际ECB等待队列

## 本轮结果

仅加强`OSTaskChangePrio`单事件等待路径。生产原5797行／379,633字节原样保持，追加221行至6018行／394,826字节，SHA256 `6efff6628f97496864f7874e32a53d58b4b56615d6465738463827c9c1873eae`；166活动源、其他165与12项受保护输入保持。固定C／配置／端口／框架／正式覆盖和历史证据未改，没有Git提交。

新增实际ECB查询、edata种类／地址与wait列表的双向任务成员关系，证明改优先级保留同一列表；把此关系与同一真实返回内存的事件位图配对。一般执行根保留全部原始入口、真实执行及完整旧结论，没有完成执行或出口load oracle。精确优先级域p<13。见[中文教程及补全表格](../docs/开发中/事件位图怎样对应真正的等待队列.md)。

## 实际检查

- gate02：14项通过，178输入保持，门禁临时树已按manifest移除。7次生产／probe coqc，3次coqchk，冻结前缀及隔离完整正控2次coqc，两负控。四probe根、三正控根的实际假设并集仅classic与functional_extensionality_dep。正控不导入候选生产模块。
- 两个单因素后置负控保留完整Proof，223行开始、242行exact FinalQueue首次拒绝。只授固定Proof后置敏感性，不授修改C或命题不可证、下游信用，见`logs/stage26-event-queue/negative-first-rejection-review.json`。
- 主probe空列表语义否定先拒绝查询，不能证明成员方向检查有效。独立Membership补充在查询及sem类型／地址显式正确时，分别漏登记真实wait任务、加入ready幽灵任务；两方向语义否定和两项查询／类型见证实际coqc／coqchk通过，四根假设仅classic，精确源码snapshot及结果保留。
- 新9项测试通过；完整Ran 879 tests in 50.944s；FAILED (failures=273, errors=1)。原273个诊断按重数保留，新增1个逐trace复核为旧wait-payload报告生产SHA过期；旧测试和报告未修改。
- 范围审计、冻结核对、diff及增量make通过，make无重编，不授当前身份source-only全量干净构建或旧完整函数门禁重放信用。默认audit仍2，正式六门94／1／1／1／1／0不晋级。
- 核对清理56个一次性文件／17,144,941字节，门禁树另计；903个基线缓存路径保留，不声称字节不变。交付文件、全部成功失败日志及snapshot、可复用依赖和用户数据保留。

## 开发失败与证据边界

源码临时materialize第一次错误地传入布尔参数，记录TypeError后改用两授权修复名列表；临时树自动清理。一般证明01在冻结前缀尚未编译完时导入失败；02／03的Task rewrite及04的congruence失败，05用详细类型打印定位priority类型别名，06修复该处后在fold自引用处失败，07只对goal做cbn zeta／fold后完整通过，均保留日志。

gate01实际在固定probe入口查询lemma处失败，生产及五旧probe已编译，但无后续coqchk／正负控成功信用。probe02显式展开事件表后仍因generic map lemma与EcbMod.sig不匹配，03改具体EcbMod lemma后进入出口空列表否定处发生同类rewrite失败，04同样改具体lemma后通过。新测试仅纠正对应字面lemma断言并将报告路径指向实际gate02，未削弱断言或改旧测试。额外Membership检查01／02分别因缺少直接导入的旧probe定义而失败，03显式导入后通过两个否定根，04增加查询／类型见证后通过四根。失败不算成功。

前瞻协议、反驳清单及最终审查位于`logs/stage26-event-queue/`。入口示例physical SELF(41,8)与abstract current(60,0)仍不同；不是全局合法性或初始化可达性。真实调度在run1／ISR1／lock0下受阻；出口只保shared_fields ** Atrue。抽象edata类型不是物理OSEventType，不能混淆事件码与TCB状态位；未建立任意入口NoDup或全部任务优先级范围。

## 后续

先从真实写操作保留事件头字节并接物理类型，再补物理／抽象current一致性、正常调度、完整API／ISR不变量保持与初始化。同程序K1–K4和GOOD_OS仍未闭合，阶段一未完成，uC/OS-III未启动。
