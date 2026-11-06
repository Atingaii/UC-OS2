# 第82步：从真实初始化入口接通保留全部任务记录的返回

## 给初学者的说明

前几步分别证明了“写好任务字段”和“发布任务后返回”。本步把它们连成同一条执行，不允许前半段使用一块内存、后半段偷偷换成另一块：

```text
已有9个局部对象、cpu_sr已初始化的真实prefix入口
  → 从空闲链表取出TCB
  → 18次字段写入，建立新任务记录并保留旧记录
  → 实际首Hook调用入口
  → 首Hook真实执行并保持联合资源【未证明的契约】
  → 实际优先级表写入
  → 实际第二Hook调用入口
  → 第二Hook真实执行并保持联合资源【未证明的契约】
  → 链表／就绪位图／任务计数实际发布
  → 返回0、释放9个局部对象29字节、恢复caller
```

“任务记录”是分离逻辑中对7个字段共10字节的所有权，不是完整56字节TCB。18个初始化字段共44字节，其中7个进入记录，另外11个字段共34字节继续单独保留。抽象任务map只是规格参数；本步没有执行抽象O中的任务表更新。

## 生产接口与资源

源文件：`certiucos/v293/proofs/V293InitPublishRecords.v`。

- 稳定上层接口：`V293_OS_TCBInit_prefix_return_records_under_hooks`。
- 内部连接：`V293_TCBInit_prefix_to_record_hook`，不需要任何Hook契约即可到达首Hook入口并建立全部记录。
- `V293_records_hook_return` 明确要求从真实`sfexec`到真实`sskip None`的执行及同一个联合空间断言的保持，不把完整函数结果、发布结果或释放结果放进Hook前提，不假定Hook是noop。
- 优先级表写入以全记录和其余字段为frame；发布复用第80步从新记录借还读取字段；返回复用第81步联合资源运输。
- 最后一个Mf同时持有全部记录、发布后的链接/位图/计数、初始化剩余11字段、空闲链表指针、优先级表槽和有限用户frame；9个局部对象的全部29字节为None。
- 幸存记录及raw cell的block必须避开局部block，属于显式、偏强的块级前提。旧、新任务可以在同一block的不同offset。不运输任意依赖旧局部环境的断言。

这是已经分配局部对象后的函数体prefix，不是最外层函数调用/分配入口；continuation中的kcall仍是入口给定条件。临界区按既有ADR0005的归一化宏边界处理，不是缺失端口函数的证明。

## 独立实例与反例

`audit/probes/V293InitPublishRecordsProbe.v` 使用独立字面入口：44个typed cell、114字节；新TCB18个目标全为Vundef，旧任务为ready。旧tid=(301,8)、新tid=(301,128)，优先级12和11；存在非空旧head；caller与callee的局部环境不同。初始ptcb局部值为Vundef，实际prefix读取空闲表后才得到新指针。

1. `ChainPrefix` 无Hook前提，真实到达首Hook并保持旧、新记录。
2. `ChainPrefixExcludesWrong` 在同一个实际prefix末态读出11并排除新记录优先级10。它只验证prefix，不授予下游执行信用。
3. `ChainActualMissingHook` 到达真实缺失Hook并证明不能返回，不将缺失实现隐藏成零步执行。
4. `ChainGoodSameMf` 在两个尚未兑现的Hook契约下，连续到达真实返回；同一个Mf给出空间记录、语义记录、11项真实load和全部29字节释放事实。11项load包括优先级表、空闲表、初始化栈指针、链表、位图、计数和哨兵。
5. 正负控制只把最终新记录优先级11改为10，保持两个Hook前提、程序、入口、raw后置、free事实和证明体完全不变。正例编译通过，负例被拒绝。只证明同一证明体的敏感性，不声称任意证明都不存在。

**完整条件链的两个Hook契约尚无具体实现实例，不能据此声称无条件完整执行的非空性。** 独立字面入口与无条件prefix避免的是入口/初始化部分的空前提，并不自动消除下游契约的开放义务。

## 检验、证据与边界

本步协议在第一次生产编译前固定；控制计划在控制编译前固定，时间戳与哈希见`prospective-order.json`。所有12次编译尝试及9次失败的原始源快照、日志均保留；成功版本为`proof07`和`probe05`，原因见`attempt-diagnoses.json`。

配置后`OS_TCBInit`沿用既有模型，未新建C翻译。实际`os_core.c`第2022–2151行与固定inventory的文件及行段哈希均核对；具体身份见`source-identity.json`。

固定inventory中的`csrc/repaired/...`是历史生成路径，目前不存在；本步实际核对的是`csrc/upstream/v2.93.01/checkout/Source/os_core.c`，该函数不涉及两项授权修复，文件和函数行段都与inventory哈希一致。本步没有重新生成完整repaired checkout／预处理产物，不能把历史配置身份记录解释为已重新复现整个修复后程序。

248个活动源（145目标、103框架/tactics）增量构建通过，非cold；新增6项结构测试通过。全仓1388项测试仍423失败、1错误；424项旧诊断ID与第81步逐项一致，不宣称全绿。`make audit`仍退出2，原因是覆盖输入身份过期；project audit通过。`git diff --check`仍被旧`framework/logic/inferules.v`的行尾空白拒绝，该文件本步没有修改。

内核检查、根假设闭包、清理数量及清理后复测的最终实测值，以`audit/logs/stage82-init-publish-records/final-report.json`为准；不能用这里的预期替代工具结果。

尚未完成：最外层调用分配与record资源的连接、两个Hook实现、完整OSInit/启动、全局Inv、统一程序规格、全交错安全、localHoare/WFIFun、源码级GOOD_OS及同程序K1–K4。六门仍94/1/1/1/1/0，uCOS3未开始。目标保持active；本步不提交/推送。
