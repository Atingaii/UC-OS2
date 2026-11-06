# Stage26：同一事件返回内存的真实等待字段绑定

## 范围

本轮只加强 `OSTaskChangePrio` 单事件等待路径。未改变固定C、配置、分析端口、框架、正式覆盖或历史证据；没有Git提交。最终目标仍是同一源码程序／规格／初始化的GOOD_OS及K1–K4闭合，然后才开始uC/OS-III。

## 实际连接

详见[中文逐步教程](../docs/开发中/把等待状态绑定到真实TCB字段.md)。新增一般返回根暴露目标TCB细粒度字节frame，跨真实tail/free保持；字段布局与源状态常量核对；实际owned抽象wait步骤与同一Mf的物理payload配对。固定探针包含非空消息的同一入口见证，实际调用新一般接口；不是第二份独立实现证明。

## 检查

- 生产身份：5797行／379,633字节，SHA256 `c7e749a65e8274e4b83ebc60bf254cc04b9dfbade7e47649b33d1383bdf86cba`；旧5422行逐字保持。
- 新门禁13项通过／177输入保持，三次coqchk通过，实际假设并集仅classic与functional_extensionality_dep。
- 两单因素后置负控完整Proof保持；首次拒绝位置、目标和信用见 `logs/stage26-wait-payload/negative-first-rejection-review.json`。独立语义反例只否定非空输入绑定成NULL，不能混成修改C信用。
- 新9项局部测试通过；全量Ran 870 tests in 44.947s；FAILED (failures=272, errors=1)。旧271项诊断保留，新增2项为历史身份错配；完整trace见added-diagnostic-review.json，旧测试和报告不改。
- 范围审计、冻结核对、diff、增量make通过。增量无重建，不是当前身份全量干净构建；默认audit仍2，六门94／1／1／1／1／0不晋级。
- 已核对清理56个一次性文件／16,713,167字节；门禁树另计。903个基线缓存路径保留；交付和全部成功失败证据保留。

## 对抗性复核与限制

`adversarial-review-plan.json` 在正式门禁前记录具体质疑；`adversarial-review.json` 界定字段范围与未完成项。关系只覆盖未挂起的四种单事件wait，pend参数只是原始字节。尚未绑定OSEventType／ECB等待队列、物理与抽象current的一致性；见证尚未证明初始化可达，实际调度仍受ISR阻塞。不是完整API、前向模拟、共享不变量或GOOD_OS。

生产开发01因冻结前缀尚未编译完成而导入失败；02中不受限制的cbn展开load，后续frame rewrite不能匹配；03修正为保留load/loadm/loadbytes后通过。probe01因旧probe的Local Ltac不导出而失败，02在新probe显式保留这些局部tactic后通过。全部精确输入snapshot与日志保留，失败不算成功。正式gate和probe固定后才运行，不在运行中改输入。

下一步先把事件类型／队列、当前任务和完整共享关系连接起来，再完成正常调度与API／ISR／初始化。阶段一、阶段二均未完成。
