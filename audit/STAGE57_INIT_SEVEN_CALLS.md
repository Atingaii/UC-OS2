# 第57步：七个真实初始化调用连接

## 产出

稳定接口为`certiucos/v293/proofs/V293InitQChain.v`中的`V293_OSInit_seven_calls`；模型为`certiucos/v293/code/V293OSInitQChain.v`；独立验证为`audit/probes/V293InitSevenCallsProbe.v`，完整证据在`audit/logs/stage57-init-seven-calls/`。

准确重新物化冻结C／配置／两项修复，94函数身份全部一致，OSInit的零基位置1到7正是Misc、Ready、TCB、Event、Flag、Mem、Q。七个子函数身份分别与已有证据哈希相同；Begin和End hook只有声明，没有定义。只是保持顺序的手工语句分组，不是已验证前端，也不是完整OSInit。

## 从真实返回内存接上第七call

把96个旧队列字节及非空旧链头作为frame穿过六调用，得到实际Msix。在Msix上调用`V293_init_fresh_four`，根据内存界和全部返回资源足迹构造四个互异新鲜块；入口没有Msix／freshness／预分配callee局部前提。重排分离资源，再使用`V293_OS_QInit_call_return`执行真实清零、三次原生循环和return／free，最后组合成同一个P、同一条cstepstar轨迹。

独立fixture有八函数，明确给出GE／caller／有限入口，不导入其他audit probe。队列96字节均为255，旧链头216:0；前缀含非零和Vundef。最终同一Mf保有全部可写所有权并闭合293项读取（208已有前缀＋4队列链接＋80其余零字节＋1链头）。Q四局部对象的12字节在Mf缺失，caller同名变量41仍指向110并存7。更早的局部块可能被后续分配复用，不声称它们在最终Mf仍不存在。

## 前瞻消融与负控

只将第七个`scall208`替换为`sskipNone`，其余六call、P／GE／caller／入口／continuation不变。计划在probe和端点执行前冻结，明确只授整call信用。

| 同一返回内存上的端点 | 七call | 仅删第七call |
| --- | --- | --- |
| 队列非链接字节4／8 | 0／0 | 255／255 |
| 队列空闲链头 | 198:0 | 216:0 |
| 前缀Mem首链接 | 196:20 | 196:20 |
| Ready组 | 0 | 0 |
| frame99 | 123 | 123 |

端点第一候选缺少传递关系helper所在生产模块的显式import；保留失败源快照与日志，第二候选仅新增该import，但在展开整个结果的成员搜索上CPU持续满载，被明确SIGINT中断；第三候选改为精确的13层append-tail资源定位，结论、fixture和所有调用不变。三个候选的快照、日志、差异和诊断均保留。四项负控单独改变首链接、链头、尾NULL、frame的最终接口结论；正控通过，各负控必须在各自预定且不同的load证明行拒绝，不把早期拒绝算作下游机制证据。

## 验证与边界

213源构建复用1055旧产物，不是source-only冷构建；100根Print Assumptions和四模块coqchk结果见trust.json，仅允许既有框架三项公理。新增8项回归及全仓结果以final-report.json为准；必须与第56步冻结的396条诊断ID相同，不许改旧测试或gate制造通过。默认audit仍因旧function evidence身份过期失败。

211旧源、1055旧生产产物、C／配置、旧测试和冻结证据保持原字节。仅_CoqProject追加两模块、README／VERIFICATION前插本步、学习文档追加；两缓存恢复任务前精确字节，生成字节另留证据。清理全部先列出、全部复核后才删除；所有生产产物、独立probe源、失败和通过日志保留。数字见cleanup.json。

这是BeginHook之后存在性、无交错、八函数fixture的执行连接；不是完整94函数P、local Hoare、所有执行safety、完整OSInit／OSStart、源码GOOD_OS或同程序K1–K4。六门保持94／1／1／1／1／0；uCOS3未开始，未Git提交／推送。下一步定位Idle／Stat源码，推进任务初始化、hooks及全局runtime invariant连接，不以增加独立小模型替代整核目标。
