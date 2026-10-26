# 第八阶段：真实 OSVersion 的 API 组件连接

## 目标与边界

冻结 C 身份不变：`74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da`。

新增 `V293OSVersionAPI.v`，在原受限检查翻译、独立精确规格和局部证明之上，建立一个非空的单函数 API 单元。它不是完整内核程序，不提供 `TopRule` 或 `GOOD_OS`。

- `V293_OSVersion_api_contract`：对任何在指定位置保存准确函数的 API 表，连接实际框架生成的前后置。
- `V293_OSVersion_api_rule`：实际框架 `APIRule`，同时证明 `EqDomAPI`。
- `V293_OSVersion_api_builders`：空参数列表的前后置构建器确实返回断言；不声称整核初始化可满足性。
- 标识符由未来链接器选择，定理不依赖某个碰巧不冲突的硬编码值。

## 预先确定的验收

1. 干净构建全部 113 个活动 Coq 文件，不读取工作区旧对象或参考资料。
2. 原三个函数根和新增三个组件根，六条实际假设输出及闭包 `coqchk`。
3. 独立探针直接写出非空函数表、准确函数、无参数返回类型、常量 29300；不只检查导出定理名字。
4. 保留常量变异与空洞前置的两个局部控制。空洞控制隔离下游组件，必须先编译局部空洞定理，再由预定局部接口拒绝。
5. 新增两个逐因素控制：只改 API 结果在 `api_contract` 拒绝；只删除函数入口在 `api_domains` 拒绝。两者都要求原局部证明先编译成功。
6. 静态覆盖增加过期组件、其他函数冒领、组件构建失败和指定负控制缺失的反向测试。

第七阶段 `function-evidence.json` 与当时的框架报告保留为历史快照；本次报告另写 `function-evidence-stage08.json`，不回写旧记录。仅有新报告实际通过后才能提升覆盖。

## 当前验收状态

113 文件隔离干净构建、六个根、独立接口与 `coqchk` 全部通过。实际假设并集为 `Classical_Prop.classic` 和 `FunctionalExtensionality.functional_extensionality_dep`。四项控制均到达预定拒绝位置；新覆盖 `94 / 1 / 1 / 1 / 1 / 0` 经 `make audit` 通过。

机器报告见 [function-evidence-stage08.json](function-evidence-stage08.json)。全部输入哈希与当前活动源码匹配，原 C 身份及第七阶段历史报告不变。

任务专用探针／变异源、派生对象和可重生 AST 已逐项确认清理，故障日志、可重放工具和验收报告保留；干净构建的临时目录已自动移除。

## 全套回归与后续对象

- `PYTHONDONTWRITEBYTECODE=1 make test`：95 项全部通过，包括四个新增组件证据反向测试。
- 历史函数／框架／失败报告、修复后源码清单、固定配置和 C 回归报告与前一 Git 检查点逐字相同。
- 调度器有限实验可重放，实际源表 256 项匹配，65,528 个状态的高位掩码消融决策变化为 0，另四个单因素语义反例均观察到指定差异；不记入函数证明覆盖。见 [ready-bitmap-investigation.json](ready-bitmap-investigation.json)。
- 当前下一个实质证明对象是 `OS_SchedNew` 的共享内存与最小就绪优先级，具体初始化及整核连接仍开放。
