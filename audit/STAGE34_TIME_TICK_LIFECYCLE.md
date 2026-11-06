# 第34步：OSTimeTick 两局部变量的调用与 void 返回

## 固定对象

沿用固定配置 V2.93.01、上游提交 `0c4a48e6fbc6e915714e816196619a5481accf0c`。
实际源码 `csrc/upstream/v2.93.01/checkout/Source/os_core.c:937–1008`，文件 SHA256
`96eef5dc1a519887499cffd8f9a6c8873b96978ed9646c42e52eb6992422fea5`，
配置后函数体 SHA256 `6103dfdd986ce129a03e1b8919997bea850989041632905f3d0ee0962ae1d251`。
精确身份与前瞻协议见 `audit/logs/stage34-time-tick-lifecycle/protocol.json`。

不修改 C、配置、端口、旧174个活动 Coq 源、框架／tactics、旧测试／门禁／覆盖／历史证据。
`_CoqProject` 只追加一个新模块，中文入口采用前插检查点／教程追加，不重写历史。

## 新的纵向连接

- `V293_tick_function` 手工登记真实的 ptcb 与 CPU_SR 两个局部声明，并以 `sret` 表示隐式 void 返回。不是已验证的 C 前端；临界宏仍沿 ADR-0005 的显式归一化边界。
- `V293_tick_call_to_hook` 从真实 `scall` 开始，执行 `sfexec`、两个 `salloclv_step`、初始化 `cpu_sr=0`，停在未删除的 CPU hook 调用及真实 continuation。同一 Mp 中 ptcb 原始内容为 Vundef，保存单元为0，分离 frame 保持。没有执行／store 成功 oracle。
- `V293_tick_suffix_void_lifecycle` 从 hook 返回边界的真实 continuation 开始，调用一次既有未初始化 ptcb 的完整后缀，在同一 Ms 归还任务／位图／时间／指针与保存单元／R，再实际执行 `sret`、全部 `sfree` 与 caller 环境恢复。两局部对象各4个字节全部缺失，非局部块字节与 Ms 相同。
- 局部环境的真实排序枚举用 permutation 连接两个对象；由返回的原始所有权推出全部写权限，再构造 free，不把 free 成功作为尾段入口前提。
- R明确在最终callee环境求值；不把任意R自动搬到caller环境。返回导出物理frame，而非跨环境的无条件空间断言。

## 独立入口与反向检查

`LifecycleSameMemoryCheckpoints` 从独立编码的六任务内存建立入口，实际分配新鲜块70／71，并使用前缀真实产生的同一 Mp 验证后半段。对任意32位时间、所有byte运行标志及两种IE成立。最终 Mf 中逐字段检查既有字面预期清单（包括任务、位图和额外字段），不是只检查释放前的 Ms；同时检查两局部对象全部字节确实缺失。

**这仍是两条检查点轨迹，不是一条完整函数调用轨迹。** hook仍无可执行体，独立fixture明确证明其程序查找为None；不存在被暗中假定的“hook成功执行且保留所有资源”。在恢复入口给定的资源并不等于该入口由真实hook可达。

两项单因素负控预先登记：只把前缀保存值结论0改为1；只把释放后扫描字节结论None改为仍存在。保持全部AST、入口前提和所有Proof正文，要求分别在保存值读回／释放结论处拒绝；两者都不授下游机制信用。

## 可重核证据

`audit/logs/stage34-time-tick-lifecycle/` 保留每次成功／失败的源码快照、Coq原始日志、状态码、正式gate命令、假设检查、独立coqchk、前后全量测试及诊断差异。

实际结果以 `gate01/result.json`、`final-report.json` 和最终manifest为准，不用此文件替代命令证据。新增测试为 `tests/test_time_tick_lifecycle.py`。全量历史失败照实保留，新增登记导致旧冻结项目身份断言变化也单独记录，不修改旧测试或重新绑定历史证据。

默认 `make audit` 仍以 `stale function evidence input identity` 失败；六门保持 `94/1/1/1/1/0`，不提升正式覆盖。复用已有依赖，不是全仓 source-only 干净构建。未提交／推送。

## 未闭合义务与清理

CPU hook的真实实现／契约与连续调用、原端口内存token仿真、所有ISR交错的safety、完整共享Inv、初始化可达、源码级GOOD_OS与同程序K1–K4仍开放，uCOS3未启动。下一步优先取得／验证hook真实实现，不能改配置、擦hook或用条件执行假设冒充完成。

清理只针对本轮一次性负控树与五个probe的编译产物。计划逐项登记类型、大小、SHA／链接目标和目录成员，全部重核后才首次删除；保留旧870个依赖产物、新模块5个可复用产物、全部源／证据及既有缓存。实际清理数量与重核结果见最终报告。

## 本轮实际验证结果

- 正式gate九条命令退出码依次为 `0/0/0/0/0/0/1/1/0`，两项负控按预期拒绝，独立 `coqchk` 通过。
- 生产三个接口根、独立样例四个根仅依赖既有 `classic`／`functional_extensionality_dep`；另一个样例根闭合，无新增公理。
- 新增10项测试在清理前后均全部通过。全量1064项测试在清理前后均为368失败、1错误，诊断集合一致；旧367条诊断全部保留，新增两条仅为stage33对冻结项目身份／精确追加的断言。全量测试并未通过。
- 清理前完整复核全部目标后，删除348个一次性软链接、31个实文件（3435671字节）和38个目录；没有删除基线文件，保留全部源码、证据、既有缓存与可复用生产依赖。
- 默认audit仍exit2，正式六门与Git HEAD不变；完整函数、hook执行、GOOD_OS及后续阶段仍未完成。
