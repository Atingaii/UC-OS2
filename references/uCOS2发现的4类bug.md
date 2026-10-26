可以。为了避免计数混乱，我把目前项目里已经形成明确反例的 **4 个主问题**按下面方式编号：

| 编号    | 主问题                                          | V2.93 状态                                  |
| ----- | -------------------------------------------- | ----------------------------------------- |
| Bug 1 | timeout 后 Suspend/Resume 导致任务丢失就绪资格          | **V2.93 已修复**                             |
| Bug 2 | 删除发生优先级继承的 mutex 后，就绪位与优先级表失配，调度器选到 `NULL`   | **V2.93 修复了原 `NULL` 路径**，但同一边界仍有其他状态一致性疑点 |
| Bug 3 | 嵌套 mutex 的优先级保存/恢复失效，造成优先级复用冲突               | **V2.93 仍存在**                             |
| Bug 4 | scheduler 锁定时 self-delete，TCB 被回收复用，但旧任务继续执行 | **V2.93 仍存在**                             |

这里我把 Bug 3 中的“真正 owner 被 `OSMutexPost` 误判为非 owner”看成**同一个嵌套 mutex 问题的一个分支表现**，不单独算第五个 bug。V2.93 已经用 TCB 指针比较修掉这个分支，但没有修掉 Bug 3 的核心“stale priority restoration/reuse”。项目记录也明确把这两种表现放在同一次嵌套 mutex 反例调查中。

* * *

Bug 1：timeout 后 Suspend/Resume 使任务永久失去正常就绪路径
============================================

### 场景

设：

* 任务 A 等待信号量 `S`；

* `S` 当前计数为 0；

* A 调用 `OSSemPend(S, 1, &err)`，timeout 为 1 tick；

* B 优先级高于 A；

* timeout 到达后，B 恰好先于 A 得到 CPU。

关键在于 V2.52 把“还在等待事件”和“已经 timeout”混在 `OSTCBStat`、`OSTCBDly`、ready bitmap 三套状态中，没有独立的 Pend 结果字段。

初始状态：

| 时点     | `OSTCBStat`          | `OSTCBDly` | A ready | A 仍在 S wait list |
| ------ | -------------------- | ---------- | ------- | ---------------- |
| A 开始等待 | `OS_STAT_SEM = 0x01` | 1          | 否       | 是                |

### 第一步：A 阻塞在 `OSSemPend`

A 设置：
    OSTCBStat = OS_STAT_SEM
    OSTCBDly  = 1

然后 `OS_EventTaskWait`：
    从 ready bitmap 删除 A
    把 A 放入 S 的 wait list
    调用 OS_Sched()

所以 A 的 `OSSemPend()` 还没有返回。

### 第二步：Tick 到达，A timeout

`OSTimeTick()`：
    OSTCBDly : 1 → 0

因为 A 此时**没有显式 `SUSPEND` 位**，Tick 把 A 加回 ready bitmap。

但是 V2.52 此时没有同时：
    清 OS_STAT_SEM
    移除 S wait-list linkage

于是产生一个中间状态：
    OSTCBStat = SEM
    OSTCBDly  = 0
    ready(A)  = true
    still_waiting_on_S = true

即：

> “逻辑上仍标记为信号量等待，但已经因为 timeout 被放回 ready bitmap。”

这正是危险窗口。

### 第三步：B 在 A 重新运行之前 Suspend A

B：
    OSTaskSuspend(A);

Suspend 清除 A 的 ready bit，然后加入 `SUSPEND`：
    OSTCBStat = SEM | SUSPEND = 0x09
    OSTCBDly  = 0
    ready(A)  = false

### 第四步：B 又 Resume A

随后：
    OSTaskResume(A);

Resume 清掉 `SUSPEND` 位：
    OSTCBStat = SEM
    OSTCBDly  = 0

但是 V2.52 Resume 只有在：
    OSTCBStat == OS_STAT_RDY
    &&
    OSTCBDly == 0

时才重新设置 ready bit。

现在：
    OSTCBStat = SEM ≠ RDY

因此：
    Suspend 位已经清除
    ready bit 却没有恢复
    OSTaskResume 返回 OS_NO_ERR

也就是说：

> API 告诉调用者 Resume 成功，但 A 实际上没有恢复成可调度任务。

### 第五步：形成循环依赖

正常 timeout 收尾代码其实在 A 的 `OSSemPend()` 继续执行以后：
    A 再次运行
    → 看见自己仍有 SEM wait 状态
    → OS_EventTO()
    → 从 S wait list 删除
    → 清等待状态
    → 返回 OS_TIMEOUT

问题是现在：
    要清 OS_STAT_SEM
        ↓
    A 必须重新运行

    但要让 A 重新运行
        ↓
    Resume 又要求 OS_STAT_SEM 已经清掉

形成循环：
    清等待状态
        ↑
    需要 A 运行
        ↑
    需要 ready
        ↑
    Resume 要求已经不是 waiting
        └─────────────────────┘

后续 Tick 也救不了它，因为：
    OSTCBDly == 0

Tick 会直接跳过。

最终状态：
    未 suspend
    not ready
    delay = 0
    仍有 SEM wait 标记
    仍连接事件
    Pend 调用没有返回

Coq 局部模型已经证明这条有序轨迹能进入该状态，并且下一 Tick 保持该状态；不过项目记录也谨慎说明，完整内核层面“B 必定能在这一窗口先于 A 运行”的可达性证明当时尚未闭合。

### V2.93 如何解决

V2.93 加入独立：
    OSTCBStatPend

timeout 时：
    清除 event wait 状态
    OSTCBStatPend = OS_STAT_PEND_TO

所以 timeout 结果不再依赖保留 `OS_STAT_SEM`。

于是：
    timeout
    → 清 waiting bit
    → 记录 PEND_TO
    → A ready

    Suspend
    → A not ready + SUSPEND

    Resume
    → 清 SUSPEND
    → 因已没有 event wait bit，A 重新 ready

    A 运行
    → OSSemPend 根据 PEND_TO 返回 timeout

原反例被消除。

* * *

Bug 2：删除发生优先级继承的 mutex 后，ready bitmap 指向不存在的优先级表项
=================================================

这是最早发现的第二个问题。

### 任务配置

优先级数字越小越高：

| 对象  | 优先级     | 作用                            |
| --- | ------- | ----------------------------- |
| D   | 0       | 初始化执行顺序                       |
| B   | 4       | 等待 mutex                      |
| A   | 6       | mutex owner                   |
| C   | 8       | 删除 mutex、Resume A             |
| M   | PIP = 2 | priority inheritance priority |

初始过程是通过真实：
    OSInit
    OSTaskCreateExt
    OSStart

建立的，而不是手工伪造 TCB。

### 第一步：A 创建并获得 M

A：
    M = OSMutexCreate(2, &err);
    OSMutexPend(M, 0, &err);

状态：
    M.owner                 = A
    M.saved_owner_priority  = 6

    A->OSTCBPrio            = 6
    OSTCBPrioTbl[6]         = A
    OSTCBPrioTbl[2]         = reserved marker

### 第二步：B 挂起 A

A Resume B。

更高优先级的 B 运行：
    OSTaskSuspend(6);

因此 A：
    持有 M
    但处于 SUSPEND

### 第三步：B 等待 M，触发 priority inheritance

B：
    OSMutexPend(M, 0, &err);

因为：
    B priority = 4
    A priority = 6
    M PIP      = 2

A 被提升：
    A->OSTCBPrio = 2

    OSTCBPrioTbl[2] = A
    OSTCBPrioTbl[6] = A

同时 A 仍然被挂起，所以不会立即 ready。

### 第四步：C 在 scheduler lock 中强制删除 M

C：
    OSSchedLock();
    OSMutexDel(M, OS_DEL_ALWAYS, &err);

V2.52 删除 M 时：
    唤醒 B
    清 PIP 对应优先级表项 2
    回收 M

但是**没有同步恢复 A 当前的有效优先级字段和 bitmap 定位字段**。

得到：
    A still suspended

    A->OSTCBPrio    = 2

    OSTCBPrioTbl[2] = NULL
    OSTCBPrioTbl[6] = A

    B priority 4 ready

这时已经出现：

> TCB 自己说“我的当前 priority 是 2”，但 `OSTCBPrioTbl[2]` 却说 priority 2 没有任务。

### 第五步：C 使用旧表项 Resume A

C：
    OSTaskResume(6);

它能通过：
    OSTCBPrioTbl[6] = A

找到 A。

Resume 清除 Suspend。

问题在于，重新设置 ready bit 使用的是 **A 当前 TCB 中的 bitmap index**，也就是 priority 2 对应位置。

于是：
    ready_bit[2] = 1
    OSTCBPrioTbl[2] = NULL

这就是关键 invariant 破坏：

被直接违反。

### 第六步：Unlock 后调度器选择 priority 2

C：
    OSSchedUnlock();

`OS_Sched()` 查看 ready bitmap：
    priority 2 ready
    priority 4 ready
    priority 8 current

于是最高优先级是 2。

接下来：
    OSPrioHighRdy = 2;
    OSTCBHighRdy  = OSTCBPrioTbl[2];

而：
    OSTCBPrioTbl[2] = NULL

所以：
    OSTCBHighRdy = NULL

实验确实观察到了这个 `NULL` 调度目标。项目没有把它进一步描述成“CPU 一定会发生哪一种崩溃”，因为实验在真正汇编 context switch 之前停止；这是合理的证据边界。

### V2.93 状态

V2.93 在强制删除 mutex 时先把 owner 恢复到原 priority 6，然后才清 priority 2 的表项，因此：
    ready_bit[2] = 1
    OSTCBPrioTbl[2] = NULL

这条**原始 NULL 路径已经消失**。

不过 V2.93 在该边界还有额外状态一致性问题，而且其源码注释假设 mutex owner 是 runnable；所以我建议迁移 V2.93 时，把这段作为历史反例保留，但不要直接把“NULL 路径修掉”扩大表述成“所有相关边界均已完全证明正确”。

* * *

Bug 3：嵌套 mutex 使用失效的中间继承优先级，导致两个活动任务占用同一 priority
=================================================

这是后来发现、而且 **V2.93 仍存在** 的问题。

### 配置

| 对象      | priority / PIP   |
| ------- | ---------------- |
| A，owner | base priority 10 |
| B       | 8                |
| C       | 4                |
| D，控制任务  | 0                |
| U，后来创建  | 5                |
| M1      | PIP 5            |
| M2      | PIP 3            |

反例由真实初始化流程建立；Pend timeout 均为 0，所以它与 Bug 1 的 timeout 无关。

### 第一步：A 获得 M1

    OSMutexPend(M1, ...);

M1 保存：
    owner = A
    saved_priority = 10

A：
    current priority = 10

### 第二步：B 等待 M1

B priority 8 等待 M1。

A 继承 M1 的 PIP：
    A: 10 → 5

于是：
    OSTCBPrioTbl[5]  = A
    OSTCBPrioTbl[10] = A

### 第三步：A 又获得 M2

这时 A 的**当前有效 priority 已经是 5**。

A：
    OSMutexPend(M2, ...);

M2 保存的是：
    saved_priority = 5

而不是 A 的真正 base priority 10。

这是后续问题的种子。

### 第四步：C 等待 M2

C priority 4 等待 M2。

A 又继承 M2 的 PIP：
    A: 5 → 3

所以优先级演化链是：
    10  --M1-->  5  --M2-->  3

而两个 mutex 分别记着：
    M1 saved = 10
    M2 saved = 5

### 第五步：D 先删除 M1

D：
    OSMutexDel(M1, OS_DEL_ALWAYS, ...);

此时：
    A current = 3
    M1 PIP    = 5

因为：
    3 != 5

旧恢复逻辑认为此时不应该恢复 A，因此跳过恢复。

但是它仍然释放了 priority 5 的占用：
    OSTCBPrioTbl[5] = NULL

问题是：

> M2 里面仍然保存着“以后应把 A 恢复到 5”。

所以现在 priority 5 已经对系统公开为“空闲”，但 M2 仍持有一个指向 5 的延迟恢复承诺。

### 第六步：创建 U，复用 priority 5

D 创建新任务：
    U priority = 5

因为：
    OSTCBPrioTbl[5] == NULL

所以创建合法：
    OSTCBPrioTbl[5] = U

### 第七步：删除 M2

D 再：
    OSMutexDel(M2, OS_DEL_ALWAYS, ...);

现在：
    A current = 3
    M2 PIP    = 3

所以恢复路径执行。

M2 保存的“旧 priority”是 5，于是：
    A: 3 → 5
    OSTCBPrioTbl[5] = A

但那里已经是 U。

最终：
    A priority = 5
    U priority = 5

    OSTCBPrioTbl[5] = A

于是两个不同活动任务拥有相同 priority，而且 U 的唯一 priority-table 入口被 A 覆盖。

这已经足以证明状态错误，不需要假设最终 CPU 是否崩溃。

即使不创建 U：
    delete M1
    → delete M2

A 最终也只恢复到：
    5

而不是 base：
    10

所以 priority restoration 本身已经错误。

### 为什么 `OSMutexAccept` 也很重要

源码注释对 `OSMutexPend` 有“持锁任务不能再去 Pend 其他事件”等使用约束。

但项目随后把第二次获取 M2 改成非阻塞：
    OSMutexAccept(M2);

相同的四组删除/复用结果仍出现。

因此不能简单说：

> “这是因为测试违反了 OSMutexPend 的注释前置条件，所以不算问题。”

项目对 V2.93 的实际测试同样观察到了这个冲突。

### 同一 Bug 的 owner-misidentification 子分支

在：
    A current priority = 3
    A 实际仍持有 M1
    M1 PIP = 5
    M1 saved owner priority = 10

时，旧 V2.52 `OSMutexPost(M1)` 用 priority 数值判断 owner。

因为：
    3 != 5
    3 != 10

它会错误返回：
    OS_ERR_NOT_MUTEX_OWNER = 120

尽管真正 owner 就是 A。

V2.93 把 ownership 改成：
    OSTCBCur == M1.OSEventPtr

因此这个**owner 误判子问题已经修复**。

但是 V2.93 **没有修掉前面的 stale saved priority / priority reuse 问题**：
    M2 仍保存 5
    M1 删除后仍释放 5
    后续 M2 仍恢复到 5

所以 Bug 3 主体仍然存在。

* * *

Bug 4：scheduler lock 下 self-delete，当前 TCB 被重新分配给 B，但 CPU 继续执行 A
===============================================================

这是目前最后发现的一处，而且证据非常直接。

### 初始状态

任务 A：
    priority = 6
    TCB address = T

CPU 此时真正执行 A。

所以：
    OSTCBCur = T
    T describes A
    CPU stack/PC = A

### 第一步：A 锁 scheduler

A：
    OSSchedLock();

得到：
    OSLockNesting = 1

### 第二步：A 删除自己

A：
    OSTaskDel(OS_PRIO_SELF);

删除代码：
    清 A ready bit
    清 OSTCBPrioTbl[6]
    摘除 A
    把 T 放回 OSTCBFreeList

但是：
    OSTCBCur 仍然指向 T

更关键的是 scheduler 现在仍被锁定：
    OSLockNesting = 1

所以内部：
    OS_Sched();

不能进行 task switch。

结果 `OSTaskDel()`：
    return OS_NO_ERR

于是**已经逻辑删除的 A 又回到自己的调用点继续执行**。

这时出现了第一个严重 invariant 破坏：

同时：

一个仍对应 live CPU execution context 的 TCB 已经变成可重新分配资源。

### 第三步：A 创建 B

A 的“删除后代码”继续：
    OSTaskCreateExt(B, ..., priority = 6, ...);

B：

* 也使用 priority 6；

* 有不同 task entry；

* 有不同 stack；

* 有不同 ID。

因为刚刚释放的 T 位于 free list 前部，新建 B 复用 T：
    T now describes B

于是内核视角：
    OSTCBCur = T

    T:
      priority = 6
      stack    = B stack
      ID       = B

但 CPU 真实执行上下文仍然是：
    A stack
    A PC
    A continuation after OSTaskDel()

因此已经形成：
    内核任务身份 = B
    CPU 执行身份 = A

### 第四步：A 调用配对 Unlock

旧 A 的代码继续：
    OSSchedUnlock();

现在调度器发现最高 ready task 是 B：
    OSPrioHighRdy = 6

但是：
    OSPrioCur = 6

仍是 A 原先的数值。

调度器使用：
    if (OSPrioHighRdy != OSPrioCur)

判断是否切换。

于是：
    6 != 6

为假。

所以：
    不发生 context switch

### 第五步：错误被实际观察到

Unlock 返回以后：
    CPU 继续执行 A 的后续代码

而实验观察：
    B entry count = 0
    context switch count = 0

同时 TCB T 已经记录：
    B 的 ID
    B 的 stack
    B 的 task metadata

再调用 scheduler 仍保持这种错位。

这不是“理论上也许不漂亮”，而是明确的：

> **task execution identity violation**

即内核认为当前任务已经是 B，但 CPU 实际仍在执行 A。

TCB 来自静态池，因此它未必立即产生非法地址访问，所以“没有马上 crash”并不表示正确。

### 证据范围

项目实际测试了：
    scheduler lock count = 1 / 255
    ×
    OSTaskDel(SELF) / 显式删除当前 priority

具体 TCB reuse 的四条流程都复现了旧任务继续执行。此前“1020”这个数字指的是大量非零 lock 组合下：
    OSTaskDel 成功返回
    但当前 TCB 已被回收

而不是“1020 次都发生 CPU crash”。

这也是当前证据表述应该保持的准确边界。

* * *

四个问题之间的关系
=========

从形式化角度看，这四个 bug 其实有一个共同主题：
    某一子系统宣布了一次状态转换已经完成
                 ↓
    但其他表示同一事实的状态字段/数据结构
    没有同步完成转换

可以概括为：

| Bug | 发生失配的两侧                                                                  |
| --- | ------------------------------------------------------------------------ |
| 1   | timeout 状态 ↔ event-wait 状态 ↔ ready bitmap                                |
| 2   | TCB 当前 priority ↔ priority table ↔ ready bitmap                          |
| 3   | mutex 保存的恢复 priority ↔ 当前有效 inheritance chain ↔ priority table ownership |
| 4   | CPU 当前执行上下文 ↔ `OSTCBCur`/TCB ownership ↔ TCB allocator/free list         |

因此它们对最终 Coq 证明非常有价值，因为可以导出四组核心 invariant：
    Bug 1:
    timeout/wait/result consistency

    Bug 2:
    ready(p) → priority-table(p) contains a valid corresponding TCB

    Bug 3:
    active task priorities are unique
    and inherited-priority restoration never targets a priority
    owned by another live task

    Bug 4:
    the TCB backing the currently executing context
    cannot be free/reallocated
    before execution has left that context

这四组性质以后不应该只是“回归测试”；如果验证目标改为 V2.93，我认为它们应该直接成为 **V2.93/修正版全局 invariant 或由全局 invariant 推导出的 safety theorem**。这样最终的 `GOOD_OS` 之外，还能机器可检查地说明：**这四类已经发现过的反例不会在最终验证版本中重新出现。**
