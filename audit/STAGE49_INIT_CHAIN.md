# 第49步：同一程序、同一内存轨迹上的三个初始化调用

## 本步结果

稳定接口：`certiucos/v293/proofs/V293InitChain.v` 中的 `V293_OSInit_three_calls`。

从一个拥有原始可写全局资源的入口执行：

```text
M --OS_InitMisc--> Mmisc --OS_InitRdyList--> Mrdy --OS_InitTCBList--> Mf
```

接口返回完整连续语句的真实 `cstepstar`，同时返回带实际continuation的三段子轨迹。所有调用使用同一个P；后一步使用前一步真正返回的内存，不把中间状态、输出fresh或load作为前提。同一Mf返回TCB、优先级表、ready、十项Misc及frame的可写所有权。

## 准确源码边界

- 固定目标、配置及两项授权修复不变；94个配置后函数身份与冻结清单一致。
- 本次 `OSInit` 在锁定 `os_core.c:582–635`；配置后实际顺序为：
  1. OSInitHookBegin
  2. OS_InitMisc
  3. OS_InitRdyList
  4. OS_InitTCBList
  5. OS_InitEventList
  6. OS_FlagInit
  7. OS_MemInit
  8. OS_QInit
  9. OS_InitTaskIdle
  10. OS_InitTaskStat
  11. OSInitHookEnd
- 两个port hook在分析翻译单元中有声明、无函数体。不能将其删除或冒充空函数。
- 本步只覆盖第2–4项的连续片段，从第1项之后的状态开始。**不是从OSInit入口执行到该片段的可达性，也不是完整OSInit。**
- 三个子函数的精确源码身份与第41／42／48步已检查对象逐字段匹配；旧证据未改写。
- `V293OSInitChain.v` 是人工归一化的三调用AST；没有新增已验证C前端或编译器／ABI结论。

证据：`logs/stage49-init-chain/source/result.json`、`source-connection.json`。

## 分配不再依赖未来内存oracle

`V293_init_fresh_four` 从实际内存的 `HalfPermMap.bounded` 上界和有限资源地址列表的最大块号构造互异新鲜块，证明它们不与返回资源重叠。

- 执行Misc后，从Mmisc选择ready局部块。
- 执行ready后，从Mrdy选择四个TCB局部块。
- 复用原来的实际调用／分配／释放定理，不改旧源码或旧定理。
- 接口仍有准确函数绑定、全局／局部名称条件、TCB标识符排序及原始资源所有权等前提；并非任意坏环境都能执行。
- Misc helper对scalar slots参数化；独立实例以固定十项slot将其与真实Misc函数按定义相等连接，而非拿任意写零函数替代C。

## 独立有限入口与49项读回

`audit/probes/V293InitChainProbe.v` 不导入其他probe。真实有限可写入口包含：728个TCB未定义字节、52个值255的优先级字节、非空旧链头、非零／Vundef的ready与Misc存储，以及17／29／123／caller7的frame。

`ChainLiteralFullEntry` 证明该入口满足所有权前提，排除不可满足前提造成的空证明。`ChainConcreteExecution` 在同一Mf读回：

| 类别 | 实例数 |
| --- | ---: |
| TCB指向下一项的链接 | 12 |
| 最后TCB的Next为NULL | 1 |
| 活动／空闲链头 | 2 |
| 优先级表typed NULL | 13 |
| ready结果 | 7 |
| 固定十项Misc为0 | 10 |
| 表尾保护字节、123和caller7 | 4 |
| 合计 | 49 |

Extras共21项，其类型和值匹配由 `ChainExtrasValid` 逐项证明，不靠未满足的额外条件。返回资源还包括676个TCB其余零字节；它们保持所有权，但不额外计入49次读回。

## 释放的时间点

- ready局部1字节：在其返回的Mrdy中为None。
- TCB四局部1+1+4+4=10字节：在最终Mf中全部为None。
- **不声称最终Mf中前述11字节全部缺失**。后续分配可以合法复用ready已释放的块；未加无必要的禁止复用约束。

## 验证与原始失败

- 新稳定证明：`proof19.json`；独立实例最终结果：`probe04.json`。早期失败与源快照全部保留。
- 正式197源构建通过：94个目标源＋103个framework/tactics源，复用975个既有产物，保留985个可复用生产产物；不是source-only冷构建。
- 64个信任根及framework顶层／新代码／新证明／独立实例四模块coqchk通过；仅接受既有框架公理集合，无新增承认或内存容量公理。
- 四项前瞻单因素控制：错误调用顺序、最终时钟错误为1、ready组错误为1、frame123错误为124。正控通过，负控均按计划指定行拒绝；目标proof bodies及独立有限fixture不改。
- 控制只检查最终接口连接；直接导入已检查的独立fixture，不重新复制执行它，不授内部机制消融或下游／所有交错安全信用。
- probe02在211.32秒仍未完成、内存持续增长时作诊断中断。单因素调整为先使用已证的块排除引理、再展开merge；入口、环境和全部定理陈述保持不变，probe03约10.07秒完成。原中断与差异保留，不声称未完成基线的精确总加速比。
- 新8项测试全部通过；全仓实际1185项，395失败＋1错误。基线1177项为394失败＋1错误，原395个诊断ID全部保留；新增的唯一旧测试失败是第48步的exact195源断言，当前已197源。不修改旧测试、不删除失败；完整ID差异见 `final-report.json`。
- 默认 `make audit` 仍以退出2报告既有stale证据身份；正式六门仍是 `[94,1,1,1,1,0]`，不晋级。
- 正式构建生成的当前依赖缓存另存快照，再精确恢复既有缓存字节；lia自动追加的307字节也另存，按baseline SHA256定位并恢复原始前缀，原缓存哈希完全相等。不改旧测试的保护要求。

完整证据：`logs/stage49-init-chain/final-evidence-manifest.json`。原输入／产物保护、回归差异、清理及实际结果见同目录 `final-report.json`；未提交／推送。

## 尚未完成

本结果是无交错存在性执行，不是Hoare／所有执行safety。完整OSInit余下六个内核调用及两个端口hook边界、OSStart、任务／ISR、运行不变式、源码级GOOD_OS及同程序K1–K4仍开放；uCOS3未启动。最终目标保持active，继续沿锁定源码启动路径推进。
