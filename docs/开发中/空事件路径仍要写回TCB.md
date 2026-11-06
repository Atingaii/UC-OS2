# 下一步：EventPtr 为 NULL，为什么 TCB 仍要更新？

上一节已将非空事件路径接到TCB五字段。本节补另一条路径，不改变程序：

```c
pevent = ptcb->OSTCBEventPtr;
if (pevent != (OS_EVENT *)0) {
    /* 迁移事件等待位 */
}
/* 无论上面的条件真假，都继续更新TCB五字段 */
ptcb->OSTCBPrio = newprio;
ptcb->OSTCBY    = y_new;
ptcb->OSTCBX    = x_new;
ptcb->OSTCBBitY = bity_new;
ptcb->OSTCBBitX = bitx_new;
```

这是固定配置相关语句的教学摘录，不是完整函数。关闭的Multi-Pend块不在当前配置后程序中。

## 1. 先把两条路径放在一起

同一个任务从优先级8改成6，固定入口ready两行16／0，只改变TCB的EventPtr字段：

| 检查对象 | EventPtr非空路径 | EventPtr为NULL路径 |
| --- | --- | --- |
| 执行的程序 | 同一个连续程序 | 同一个连续程序 |
| 旧优先级表第8槽 | 清为空指针 | 清为空指针 |
| 新优先级表第6槽 | 指向原任务TCB | 指向原任务TCB |
| ready两行 | 仍为16／0 | 仍为16／0 |
| 事件等待两行 | 0／1迁移为64／0 | 该事件块逐字节不变 |
| TCB五字段 | 6／0／6／1／64 | 6／0／6／1／64 |
| 局部pevent | 真实非空指针 | NULL |

这里没有收到消息、没有解除等待，**都不能因“改了优先级”就说任务已ready**。NULL路径没有对应事件指针可供解引用，所以不执行事件位图写入；但TCB仍必须与新的优先级表一致。

## 2. 这次还补了什么保持性？

只看局部`pevent == NULL`，不能直接推出TCB内部的`OSTCBEventPtr`没被后来写坏。新接口分别证明这两件事，并进一步证明TCB中五个写入字节以外全部保持。

固定分析布局中，EventPtr占偏移28..31，五个写入字段占50..54。具体夹具TCB基址为8，因此改变入口EventPtr的是36..39，五写目标是58..62；地址不重叠。偏移55是实际`OSTCBDelReq`字段，也属于保持区域，不把它当作填充字节。这里只用当前源码级分析布局，不声称硬件ABI已被证明。

这一内部保持后置目前由**新NULL接口**明确提供；不能反向给旧非空接口补上没有导出的后置条件。

## 3. Coq怎样把这些步骤接起来？

新稳定接口为`V293_task_prio_prefix_null_update_execution`，仍在既有`V293TaskPrioRekey.v`中：

1. 从入口资源执行已有的表写、三旧字段读取、ready判断与真实空事件前缀。
2. 旧前缀只在事件赋值前的Mf给出操作数；通过真实pevent存储的frame把它们运输到Me，而不是要求调用者提供“Me已经正确”。
3. 从同一Me读取指针、newprio、X索引及其他操作数，实际完成五次写入。
4. 在最终Mh中同时检查表、ready、五字段、局部pevent、TCB内部EventPtr和未写字节。

`V293_null_update_continuous_witness`构造可满足入口，`V293_null_update_entry_delta`说明NULL对照只覆盖一个入口字段、其余地址不变。控制还包含ready真支；那条路径会迁移ready位，而不是跳过整个函数。

## 4. 怎样复核？

在仓库根目录执行：

```sh
COQBIN=/data/home/lucentzhou/.opam/default/bin/ \
PYTHONDONTWRITEBYTECODE=1 \
python3 scripts/check-v293-task-prio-rekey.py --null-update
```

门禁检查四根独立手写字面接口、实际假设、`coqchk`、同环境正向重编和四项单头负控。负控只说明错误契约被当前证明拒绝；早期拒绝不能证明每个下游机制都已被独立测试。源码与原始成功／失败日志见`audit/logs/stage26-task-prio-null-update/`，实际结果以最终机器汇总为准。

本次实际复核：四根接口、三次`coqchk`和四项负控符合预期，174项局部Python通过；另行165源隔离干净构建通过。全套674项仍有253失败、1错误，默认正式审计仍拒绝旧证据身份，不能写成“全套通过”。专属临时树和60个新探针产品已核对清理，源与全部失败日志保留。

## 5. 后续真正缺的是什么？

现在处理的仍是函数中间的连续片段，**不是完整API或最终GOOD_OS**。下一步要处理更早的参数／任务检查、新坐标的实际计算，然后接退出临界区、调度判断和返回；还需非空路径的内部TCB保持接口、合法等待／ready共享关系、全API／环境／初始化及同程序K1–K4。uC/OS-II整阶段完成后，再按老师要求开始uC/OS-III。
