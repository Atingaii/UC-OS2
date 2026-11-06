# 第300步：真实控制字节与精确中断调度决策

## 为什么接着做这一步

最终目标不变：先完成固定 V2.93.01 源码级 `GOOD_OS` 与同程序 K1–K4 回归，再按老师附件推进 uCOS3。第299步已把 quiet 中断包装接入 `sched ;; END None`，但依赖当前任务已经最高就绪；对当前非最高且锁非零的 quiet 输入，不能强行执行 `sched`。本步隔离这个差异究竟来自任务表还是被旧抽象状态遗漏的控制字节。

## 本步闭合的连接

生产文件：`certiucos/v293/proofs/V293InterruptControlRetention.v`。

1. 从原始、未附加 quiet/最高就绪过滤的真实 `BuildintPre`，取得有界 running/nesting/lock 三个字节的同堆所有权，进而唯一捕获 `(旧 osabst, 控制三元组)`。不是调用者额外提供一份独立快照。
2. 明确定义确定性选择：`running=1 ∧ nesting≤1 ∧ lock=0` 时选择 `sched ;; END None`，否则 END。这里 nesting 是 Exit 递减前的值，0保持0；Enter 后的选择精确等价于原 running=1、原 nesting=0、lock=0。
3. 将选择结果连接到已有 `OSIntExit` 真实递减及两层 guard 的 Hoare 规则。dispatch body、环境与局部资源前提原样保留，因此这条规则只闭合局部控制块，不是完整 ISR。
4. 证明 bounded 状态的 Enter/Exit 保持有界。饱和255在 Enter 不增，Exit 后254，绝不无条件声称原深度恢复。

这是一份**迁移接口组件**。原框架 `osabst`、`spec_step`、固定 `osintspec`、`WFInt`、健全性定理都未修改；新直积没有自动成为这些旧规则的状态。

## 单因素对照，不让外层提前拒绝掩盖锁分支

探针：`audit/probes/V293InterruptControlRetentionProbe.v`。

- 复用原 `ACmemory n`，分别取 n=0、n=1；running始终1，Exit递减后 nesting 始终0。
- 只 store 地址 `(151,0)` 的锁字节0→1，证明所有其他地址不变；实际 load 得到前后相应三元组。
- 原低层程序、抽象任务状态 `RIabstract OwnershipWaiting`、Inv、LI 不变。实际锁 guard 从真变假，并分别构造完整客户端调用。
- **高层规格不同**：原分支使用 `CCspec`，锁定分支使用 `QCspec`。这不是单个固定高层程序的两条轨迹，不能据此宣称统一生产规格已完成。

在这两个当前 Inv 接纳的输入上，旧 O 完全一样而调度决定相反，因此不存在只看 O 的精确布尔分类器。这只排除了该条件下的确定性 O-only 决策；不排除所有非确定性规格，也不证明这些输入从初始化可达。当前任务在见证里是 Waiting，更强 current-is-running 不变式可能改变允许输入集合，但必须先证明建立和保持，不能直接删除反例。

边界消融固定其他因素，覆盖 running=0/1/2/255、所有 nesting/lock 字节，另有 Coq 中的0/1/2/255与锁255边界。Python 262144组算术检查只是独立的源码 guard 影子，不能替代物理内存、调度器执行或 Coq 证明。

## 路线与尚欠义务

见 [ADR-0011](../docs/adr/0011-精确中断决策保留真实控制信息.md)：接受“精确决策需保留足够控制信息或证明更强入口不变式”这一边界；不预先决定最终框架必须采用直积表示。没有使用任选调度、放宽最高就绪条件、虚假任务键或把时间字段改作控制位。

下一条纵向连接应把真实控制信息的读取及 Enter/Exit 更新耦合到**单个固定生产中断规格**，并证明其框架解释；不能停留在纯选择函数，也不能把按堆选择 CCspec/QCspec 当成 WFInt。一般中断上下文、强 current 关联与初始化、全内核环境、同程序 K1–K4、GOOD_OS 及 uCOS3 仍开放。既有三函数内部 WFIFun 成果继续保留，不能说所有函数环境证明都不存在。

## 验证与交付

本步采取前瞻协议 `audit/logs/stage300-control-retention/protocol.json`。稳定编译、全部新根信任复核、回归与失败记录以该目录的 `verification.json`、原始日志和封存清单为准。首次编译的11次失败快照保留，后续稳定成功不改写失败历史。README/status 仅前插，project 仅追加新生产文件；C/config/AST/framework/旧证明、测试与冻结证据不重写。没有提交、推送或标记最终目标完成。

### 实测结果

| 检查 | 结果 |
| --- | --- |
| 新生产/探针双稳定编译 | 各2次通过，源哈希相同 |
| 全部新根 | 生产14、探针6，共20；Print Assumptions及递归coqchk通过（约565秒） |
| 新回归 | 7/7通过 |
| 完整回归首次 | 2670项，445失败、1错误；原始日志保留 |
| 精确恢复原缓存后完整回归 | 2670项，436失败、1错误；与第299步旧失败ID及顺序完全相同 |
| 增量make build | 通过；不是clean build |
| project-audit | 374个活动证明文件、103个框架/战术文件，通过 |
| make audit | exit 2，原有stale function evidence input identity未修复 |
| git diff --check | exit 2，原有inferules.v第581–586行六处尾空白未改 |

新增9项首次回归失败全部明确报告 `.lia.cache` 哈希错配。保持测试和证明不变，只恢复编译前原缓存后，第二次完整回归恰好消去这9项；其余旧失败及错误保留。两次完整日志与 `cache-diagnosis.json` 同时封存，不用最终结果覆盖首次结果。辅助的九项单独诊断脚本首次启动因日志标题解析错误失败，协议文件未生成；因此没有宣称它成功做了独立的九项 before/after 实验，诊断依据是两次实际完整回归。

按逐项身份和用途清理6个临时Trust文件、2份已恢复的缓存备份、1个不再使用的临时诊断脚本；保留Trust/失败源快照、两次回归日志与可复用编译依赖。旧306个pyc和两份根缓存的内容精确不变。最终封存后由只读 `checkpoint.py` 检查旧2589项输入、上一轮最终120项证据及本步清单，哈希/字节数损坏的单因素负对照必须被拒绝。
