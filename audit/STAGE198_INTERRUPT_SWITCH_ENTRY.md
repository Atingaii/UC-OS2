# 第198步：不同任务中断退出至真实切换调用入口

## 本步补齐的纵向路径

第197步完成了“当前已经最高”的完整调用；本步推进另一条路径：当前任务在优先级6等待，最高就绪任务在优先级4。主接口 `V293_OSIntExit_switch_entry_execution` 不假定比较结果或整段执行，而由同一任务表的当前成员与非最高关系推导不同优先级：

```
scall OSIntExit → sfexec → fresh四字节saved分配、初始化
→ running=1 → encrit → nesting 1→0 → guards
→ 真实OS_SchedNew调用、计算、返回释放 → high/target更新
→ 实际优先级比较true → counter模32位递增 → 空trace
→ scall OSIntCtxSw → sfexec OSIntCtxSw（本步止于这里）
```

生产文件：`certiucos/v293/proofs/V293OSIntExitSwitchEntry.v`。

主接口只有实际函数lookup、全局绑定、同一task map关系、decoder读取和owned资源等前置；没有整段trace、callee执行、分配、store/free或比较eval的先验答案。内部从所有权构造写入，复用真实调度前缀。

## 端点不是完整切换

端点是**真实调用规则生成的 `sfexec int_switch nil nil`**，而不是人为跳过调用。

- 旧current任务、`OSPrioCur`和running保持；high/target已指向新的最高就绪任务。
- counter为 `Int.add c Int.one`，按原32位整数语义递增。
- fresh saved四字节仍存活并拥有，尚未释放；callee局部环境仍在。
- continuation仍为 `excrit → sret → kcall`，没有提前恢复caller或IE。
- 入口空间资源用IE=false逻辑视图；端点**实际**IE=false，原IE压入临界栈。未证明入口IE=true实际状态满足生产SWINV。
- 字节frame排除fresh整块、target整块、high/nesting各一字节、counter的4字节；不声称全堆精确更新方程。

框架 `pswitch_step` 只更新当前TCB指针和运行任务，不同步物理 `OSPrioCur`。不能直接把它当作完整 `OSIntCtxSw`，也不能私自新增缓存同步C补丁。端口实现/接受抽象的正确连接仍须另证。

## 独立资源与事前单因素对照

冻结协议：`audit/logs/stage198-interrupt-switch-entry/protocol.json`。

probe由已有非空ready/task/table资源和owned cells独立构造，不从成功trace倒推入口。物理当前TCB指针、抽象curtid及优先级6缓存一致；该任务确为等待任务，priority4确为最高就绪任务。不是仅改一个缓存字节制造的不一致输入。

| 检查 | 保持不变 | 单独设置/变化 | 观察 |
| --- | --- | --- | --- |
| 完整前缀正控 | 非空任务图、真实scheduler、caller | 当前waiting6，ready4，nesting1/lock0 | 到真实sfexec112；target变ready，counter19→20，saved4字节存活 |
| IE对照 | 同一program/heap/caller/栈尾 | 入口IE=false/true | 均到同一调用边界，端点IE=false，分别压入false/true |
| caller遮蔽 | 完整前缀两侧 | caller同名saved为Tint8/23，局部running0，全局running1 | caller字节保持，callee使用新鲜Tint32 saved、全局running |
| counter消融 | 同一独立尾段输入堆、program、continuation和比较 | 只删除counter递增语句 | 两侧均到同一sfexec112，counter分别20/19；current6和caller23保持 |
| 缺少端口实现 | 实际sfexec112 | 该probe的program112=None | 实际loststep无下一步；只证明边界缺口，不当作实现 |

counter消融是**精确不同优先级尾段**的对照，不是两个完整OSIntExit函数的入口至返回比较。尾段独立输入由原入口拥有的high88单独更新为4构造；它不冒充完整前缀的端点。两侧确实执行到相同下游边界，不用早拒绝替代递增的效果检验。完整正常前缀另证。

## 可复核证据

目录 `audit/logs/stage198-interrupt-switch-entry/`：

- 稳定编译 `body04`、`probe11`；失败快照/日志/退出码全部保留，含一次中断的慢速计算尝试。
- 两次重建精确配置后的OSIntExit/OS_SchedNew，核对锁定源哈希及函数体。
- 20个生产/probe根的Print Assumptions，递归coqchk两入口；只接受既有信任集合。
- 新增5项结构回归，仅用于结构/身份检查，不替代Coq语义证明。
- 两轮2154项全量回归；应保持旧423失败、1错误及有序ID，实测结果以verification.json为准。
- build/project-audit和已有audit/whitespace失败分别留存，不修改旧门槛。
- 旧文件逐哈希核验，文档仅前插，工程清单仅追加；清理前逐项登记，恢复旧缓存，保留证据和可复用编译产物。

只读复核：

```
PYTHONDONTWRITEBYTECODE=1 python3 audit/logs/stage198-interrupt-switch-entry/recheck-checkpoint.py
```

## 下一步与最终目标

下一步需要连接真实/获接受的OSIntCtxSw抽象效果及其返回continuation，处理切换后指针、优先级缓存和不变量的一致性。此处没有新端口函数体、没有真正switch步骤、没有完整不同任务返回。

生产ISR/LocalInv、WFFunEnv、初始化、全局模拟、GOOD_OS及同程序K1–K4仍开放。六门仍为94/1/1/1/1/0；本步不提高函数覆盖。目标active，未提交/推送。第一阶段GOOD_OS完成后，才按老师附件进入uCOS3。
