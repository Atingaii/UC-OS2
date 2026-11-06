# 第135步：同一任务表的记录、就绪位图、优先级表与调度赋值

## 目标与范围

第134步的有限运行期 Inv 拥有同一抽象任务映射的真实 TCB 已选字段，但尚无就绪存储。仅从独立位图计算最高位，不足以说明真实内存里选出的指针属于该任务表。本步把三者连接，并执行原 `OS_SchedNew` 两条赋值；不是完整函数、完整调度调用或整核验证。

源码定位为锁定 `Source/os_core.c` 第1751～1776行的 `OS_SchedNew`，固定配置选择 `OS_LOWEST_PRIO <= 63u` 分支；实际两条赋值位于1757～1758行，对应既有 `V293_OSSchedNew_updates`。本步复用手工 AST 与既有局部连接，不声称已验证自动 C 前端或新完整函数覆盖。

输入版本、C、配置、手工 AST、框架、tactics 和全部既有冻结证据保持不变。实现前的六项检查在 `audit/logs/stage135-ready-task-invariant/protocol.json`；实现前全部旧文件的哈希在同目录 `baseline.json`。全部编译失败、源码快照与日志保留，不将早期失败改写成通过。

## 新的有限运行期不变量

生产文件 `certiucos/v293/proofs/V293ReadyTaskInvariant.v`：

- `V293_ready_owned` 精确拥有两行 bitmap、group 三个实际字节，以及13个真实 typed 优先级表指针。纯关系要求字节范围、非空 ready、位图与同一 tasks 的 ready 成员等价、每个任务在其优先级槽有自身指针。
- `V293_ready_payload` 把同一 tasks 的 TCB 已选字段与上述存储分离拥有；不再为记录、位图、表项各用一个互不相关的任务映射。
- 精确性从固定地址／类型 footprint 与表长13推导，不假定两个存在量化的位图数值或表值相等。
- `V293_ready_inv` 继续拥有 current、tasks、events、time 四个抽象槽；`V293_ready_invariant_good` 闭合该有限实例的 `GoodI`，包括真实 `OSTCBCur` store 保持记录与就绪存储。未新增公理。
- `V293_ready_switch_sound` 从带任意 caller frame 的同一完整内存读出抽象 tasks、其真实记录、bitmap/table 关系及实际 loads。
- `V293_ready_switch_selected` 从这些事实推出最高优先级 ready 任务和实际表指针，而非输入“某任务已经最高”的前提。

`V293_ready_sched_updates` 是本步供上层使用的执行接口：从上述 Inv、实际 ge/le 绑定、调用者拥有的两个输出字节和256项 lookup loads，执行原两条赋值；返回同一 Inv 与 frame、实际 high 字节、原目标表达式的指针值／类型、同一抽象状态的 scheduler 判断，以及两个输出地址之外其他全部地址的字节不变。

这里的 `br/bg/bp` 是固定块参数；Inv 本身不含这些全局变量的 ge 绑定。绑定在真实表达式执行接口中明确要求，未凭同名变量直接假定真实存储已关联。只读 lookup 表在 caller frame 中，不是凭 Inv 凭空拥有。

## 独立联合实例与消融

探针 `audit/probes/V293ReadyTaskInvariantProbe.v` 重用已检查的非空任务字段字节：ready 任务 `(60,0)` 优先级4，waiting 任务 `(41,8)` 优先级6，后者等待信号量且有消息。增加独立 literal bitmap low=16、high=0、group=1，优先级槽4／6分别为两个真实指针。

1. `RTliteral_spatial` 建立新 Inv。`RTswitch_cases` 分别覆盖 current 为 waiting 成员以及非成员的情况，真实 current store 保持同一记录、位图和表。不是因为 current 已经 ready 才能成立。
2. `RTjoint_execution` 在同一份实际内存中联合拥有上述资源、两个独立输出字节以及实际256项只读 lookup 表，证明任意 P／continuation 下原两条赋值的存在性执行、实际 high=4、目标表达式读取 ready 指针、记录保留及其他地址保持；覆盖上述两种 current。所有局部前提联合可满足，不只列出条件接口。
3. `RTbitmap_ablation` 仅对实际 low 字节 store 16→0；同一 tasks、TCB、表、high、group 和其他全部地址不变。旧记录 Inv 仍可满足，而新 ready Inv 对任意 current／frame 均拒绝。拒绝由真实 load 锁定 low=0 与同一 tasks 中优先级4确实 ready 的矛盾推出。
4. `RTslot_ablation` 仅把槽4的一次真实 typed 指针 store 从 ready 指针换为 waiting 指针；这修改其四字节 footprint，不称作单字节变异。位图、任务表、TCB 与该 footprint 外其他全部地址不变；旧记录 Inv 仍可满足，新 Inv 拒绝。拒绝由同一 tasks 的槽约束与实际 pointer load 冲突推出，独立于上一消融。

两项是各自从未破坏的基线出发的单因素实验，不把第一项的提前拒绝当成第二项已被检验。没有删改冻结证据、绕过错误或降低验收门槛。

## 验证记录与复现

最终实测以本目录 `checkpoint-report.json`、`verification.json` 及冻结 manifest 为准；`stable-compiles.json` 记录精确的成功源码快照。新增8项 Python 检查仅验证结构、证据身份和边界文字，不替代 Coq 语义定理。

```sh
make build COQBIN=/data/home/lucentzhou/.opam/default/bin/
PYTHONDONTWRITEBYTECODE=1 python3 -B -m unittest discover -s tests -p test_ready_task_invariant.py -v
PYTHONDONTWRITEBYTECODE=1 python3 -B audit/logs/stage135-ready-task-invariant/verify-checkpoint.py
```

实测48个证明根（生产24＋探针24）、301个活动模块与21个附加探针的信任检查通过；实际使用的框架假设仅 `Classical_Prop.classic` 与 `FunctionalExtensionality.functional_extensionality_dep`。全量1773项测试仍有旧423失败／1错误，失败 ID 集合与第134步完全相同。

信任检查枚举本步两个文件的全部证明根，检查 `Print Assumptions`，并对全部活动模块和累积附加探针运行 `coqchk`。允许的框架假设没有扩大。全量回归必须和第134步比较完整失败 ID 集合：既有423失败／1错误保留，六门仍为94/1/1/1/1/0。`make audit` 的旧 `stale function evidence input identity` 及旧框架行尾空白不在本步修复，不重写证据制造通过。

## 不可扩大解释的边界

- 这不是生产全局语义 Inv：只拥有有限任务已选字段与就绪存储，不包含完整池、链、事件资源、删除／创建保持或所有 API／活动 ISR。
- 空 LocalInv 只适合本实例，没有完整任务私有资源回收信用；GoodI 不等于初始化建立或 `WFIFun`。
- 优先级关系仅约束任务到对应槽，不约束未使用槽，也不排除这些槽的额外别名。位图高行的13..15位未要求清零；已验证的是存在有效 ready 时选择属于0..12范围的最高任务，不是完整官方运行态特征。
- 探针是联合存在性轨迹，不证明从真实初始化可达，也不是完整函数的通用 Hoare 契约、完整调用／返回或交错上下文切换。
- lookup 读回是显式入口义务；joint 实例用实际只读字节满足它，未把缺失表凭空加到生产 Inv。
- 最终源码级 `GOOD_OS`、同程序 K1–K4 尚未完成；uCOS3 未开始；总目标保持 active。本步不提交／推送。

下一步应把这个同映射就绪 Inv 与真实创建／唤醒／阻塞等更新路径连接，或先闭合完整调度调用边界；初始化、Hook／栈、活动 ISR 与最终 `WFIFun` 仍须在同一固定程序上完成，不能以更多孤立 fixture 代替。
