# 第56步：OS_QInit 完整调用

## 本步做成什么

固定uC/OS-II V2.93.01、既有配置和两项授权修复均不变。生产接口：

- 模型：`certiucos/v293/code/V293OSQInit.v`
- 证明：`certiucos/v293/proofs/V293QInit.v`
- 稳定定理：`V293_OS_QInit_call_return`
- 独立验证：`audit/probes/V293QInitProbe.v`
- 本步完整日志：`audit/logs/stage56-init-queue/`

从准确的配置后 `os_q.c:936–962` 开始：源码body SHA256为 `1c7141f5cfdd50134cb33e3f4b1d4d3ddcd75d8c0effe2cfdbab933d513196e6`；全部94个函数身份与冻结清单相同。Clang断言与Coq布局定理同时核对4×24=96字节及七字段偏移0／4／8／12／16／20／22。递归OSQPtr用复合指针标签414表达，不改成void*。

## 真实执行路径

分配 `ix, ix_next, pq1, pq2` → 真正调用 `OS_MemClr` 清零96字节 → ix=0 → 原生while三次真实迭代 → ix=3退出 → 尾NULL → 空闲链头 → return并释放12局部字节，恢复caller。

每次循环仍按源码顺序执行 `ix_next=ix+1; pq1=&Tbl[ix]; pq2=&Tbl[ix_next]; pq1->OSQPtr=pq2; ix++`。最终链接偏移为24、48、72、NULL，不是把预设结果表替代循环。清零调用自身的两个参数从实际调用内存构造fresh；外围四个callee局部的freshness／NoDup／Away仍为泛型接口显式入口条件。

独立入口把96字节全部设为255、旧链头设为非空121:0，caller变量41映射到110并存7；局部90／91／92／93初始不存在。同一Mf保有88项可写所有权并读回：4链接＋80其余零字节＋链头＋3frame。所有12个callee局部字节释放；返回前ix=3，caller同名变量保持7。字面AST核对不在右侧复用生产语句helper。

## 消融和失败记录

只将外部 `scall100` 替换为 `sskip None`，P／GE／caller／入口／frame／continuation均保持不变。原计划把第一指针字节预测为数值24，这是错误的：框架用符号Pointer片段编码指针，`QueuePointerByteIsNotAddressLowByte` 直接反驳该预测。原计划保留且不授实验信用；`ablation-plan02.json` 在新端点执行前冻结，改为测量非链接偏移4和8，并保留链头、frame对照。

| 观测 | 实际调用 | 删除调用 |
| --- | --- | --- |
| 非链接字节4 | 0 | 255 |
| 非链接字节8 | 0 | 255 |
| 空闲链头 | 82:0 | 121:0 |
| frame99 | 123 | 123 |

两个端点harness候选失败（缺少生产模块import；tactic分支作用域），日志和快照均保留；第三候选在不改结论或fixture下通过。只授“整次调用”消融信用，不授内部clear／link／allocation各自信用。

四个最终接口负控分别改首链接、尾NULL、链头、frame。正控通过，四负控在四个预先指定的不同readback行拒绝；它们不是机制消融。

## 检查与未完成部分

代码、完整调用证明、独立probe首次编译通过。211源构建复用1045旧产物，非source-only冷构建。信任检查含100个根和四模块coqchk；仅允许既有三项框架公理。机器读数以 `final-report.json`、`trust.json`、`final-tests.json` 和最终manifest为准。

本轮早期回归在Coq运行已更新.lia.cache时观测到402失败／1错误，其中额外7项明确是旧缓存hash保护。保留该日志；精确恢复任务前缓存后，最终必须与第55步冻结final的396条诊断ID逐项相同，不通过改测试或降低gate消除失败。默认audit的旧function-evidence身份过期问题继续如实保留。

209旧源、1045旧产物、C／配置、旧测试和冻结证据不得更改；仅_CoqProject追加两模块、README／VERIFICATION前插本步、学习文档末尾追加。原缓存精确恢复，所有生产产物和失败证据保留。清理先列出全部目标、全部复核，再第一次删除；最终数字见cleanup.json。

这是独立函数的存在性、无交错执行证明，手工前端。fixture只有QInit和MemClr，不是完整94函数P；尚未连接前六调用实际返回内存，不是local Hoare、所有执行safety、完整OSInit／OSStart或GOOD_OS。同程序K1–K4、任务／ISR、全局runtime invariant仍开放；uCOS3尚未开始，未Git提交或推送。下一步从实际Msix构造四fresh块，接入第七个初始化调用。
