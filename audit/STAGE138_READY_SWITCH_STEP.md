# 第138步：同一就绪不变量接到真实任务切换

## 本步解决什么

第137步已执行原 OS_SchedNew 的调用、分配、两赋值、返回、释放及原目标赋值，但尚未执行 switch。本步复用这些结果，从 **同一 Mtarget 内存** 调用框架原 `pswitch_step`，构造实际 current 指针写入，保留同一 tasks／ready Inv。不修改 C、配置、既有手工 AST、framework、tactics 或旧冻结证据。

固定目标仍是 V2.93.01、提交 `0c4a48e6fbc6e915714e816196619a5481accf0c` 与原配置和两类授权修复；六项事前检查见 `audit/logs/stage138-ready-switch-step/protocol.json`。

## 稳定生产接口

`certiucos/v293/proofs/V293ReadySwitchStep.v`：

- `V293_ready_store_frame`：同一 ready Inv 的两半 current 权限重新合成 full ownership；实际 current store 后更新 ghost curtid，恢复同一 Inv，保留即时 frame。
- `V293_ready_current_write`：利用 full ownership 与原 `store_exist_join'` **构造**成功 store 和最终内存，不把成功 store 当调用者前提。给出 readback，以及 current 四字节外逐地址不变。
- `V293_ready_switch_step`：直接使用原 `pswitch_step`，输入真实 current／target 绑定、target load、当前代码和局部投影；输出实际 `lpstep`、旧任务的 `SKIP` continuation、其他任务代码不变、current store 与同一 Inv。target 与 current 使用同一个 pointee type，不能仅凭 SWPRE 跳过类型义务。
- `V293_ready_call_then_switch`：供上层复用的稳定入口。先调用第137步的实际函数执行接口，得到原 unlocked prefix 的 `cstepstar` 和 Mtarget；再在这份 Mtarget 上执行真实切换。局部块 fresh 分配、释放、caller 恢复、target 写入与 SWPRE 仍由旧接口构造。

这里是 **源片段的 cstepstar 加单个框架 lpstep 的共同内存连接**，不是完整 OS_Sched 的 lpstepstar。两个执行关系分别证明，未在旧 AST 中插入 switch，也没有证明该片段的结束控制状态自动成为原完整函数的 switch 控制状态。原完整 OS_Sched 的优先级比较（以及既有指针比较归一化义务）、切换计数器、端口切换后的 current priority 一致性、临界区／返回和所有交错仍待组合；不能把相同内存误写成完整连续控制轨迹。

## 类型单因素对照：旧 SWPRE 不能自动推出切换

探针 `audit/probes/V293ReadySwitchStepProbe.v` 使用原 `RHmemory ct` 的全部原始字节；只把环境中 OSTCBCur 的类型从 `Tptr Tvoid` 改为 `Tptr V293_tcb_type`，地址仍为块1。target 仍为原块93、同一 TCB pointer type。其余全局绑定不变，有 `RSbinding_type_only` 的逐项证据。**这只是联合实例的类型绑定修正，不是 C 修复。**

旧实例完整调用和 SWPRE 仍通过，`RSold_SWPRE_without_switch_type` 明确把它们与 `RSold_no_common_type` 放在同一个结论中：原 current／target 不存在 `pswitch_step` 所要求的共同 pointee type。拒绝并非位图或任务选择提前失败；负例仅证明该共同类型前提不可满足，不泛化为所有 lpstep 都不可能。

正例保持同一字节内存、ready＋waiting 非空任务表、lookup、函数绑定及 caller canary；不以弱化 SWPRE 或改框架掩盖旧实例问题。

## 联合正例与省略实际写入的反例

`RSjoint_call_switch` 以同一参数化定理覆盖两种 current：等待任务成员与不在任务表中的旧 current，二者都不同于 selected ready。共同前缀实际执行原调用返回和 target 写入：

1. 实际释放 callee 局部块，caller 局部字节90仍为99。
2. 在同一 Mtarget 执行原 `pswitch_step`；真实 current 四字节改指向 ready，实际 active task id 改为 ready，离开任务代码改为 SKIP。
3. selected task 有实际代码、局部环境和 auxiliary 状态，不是切换到缺失任务；原 selected 代码不变，`projS` 给出其自己的空局部环境。通过 Inv 的局部环境无关性，在该投影中恢复同一 SWINVt。
4. 同一 tasks 的实际已选 TCB 记录及 caller canary 保留；current 四字节外，Mtarget 与 Mf 逐地址相同。
5. 单因素省略：保留共同前缀、同一 Mtarget、同一 tasks／ready 关系，甚至允许单独更新 ghost curtid，唯独不执行物理 current 写入。实际 load 仍为旧 current，所以不能满足 selected ready 的 SWINVt。不是仅用 ghost 字段反驳自身的循环 oracle。

store 保留 target、caller 等即时 frame，不等于它们在别的任务任意执行后还能作为旧任务私有资源恢复。**不把目标指针当作私有 frame 跨上下文切换保存**；本步没有跨恢复 continuation／私有资源稳定性定理。call／return 沿用 `GoodInvAsrt` frame 限制；单个 store 的 frame 结论不需要该限制，但只针对这个即时步骤。

这是无交错存在性执行和联合可满足实例，不是初始化可达性、初始全程序良构、所有交错或任意分配选择的证明。selected task 的存在不替代整程序 WFIFun。

## 验证与复现

语义依据为 Coq 8.18 的实际编译与 coqchk，不是 Python 字符串检查；新增8项 Python 回归仅检查结构／身份／边界。实测见本步 `stable-compiles.json`、`trust.json`、`checkpoint-report.json`、`verification.json` 与冻结 manifest。全部13个证明根（生产4＋探针9）、304个活动模块和24个附加探针均需检查；假设白名单不扩张。

```sh
make build COQBIN=/data/home/lucentzhou/.opam/default/bin/
PYTHONDONTWRITEBYTECODE=1 python3 -B -m unittest discover -s tests -p test_ready_switch_step.py -v
PYTHONDONTWRITEBYTECODE=1 python3 -B audit/logs/stage138-ready-switch-step/verify-checkpoint.py
```

全量1797项回归与第137步对比完整失败 ID 集合，不删除旧423失败／1错误。`make audit` 的 `stale function evidence input identity` 和旧 framework 行尾空格也仍保留；六门94/1/1/1/1/0，不新增整函数可调用覆盖信用。清理先逐项核对目标，再只删除本步一次性 Trust 编译材料和缓存备份，恢复原 lia／nia 缓存；保留可复用产品和所有失败编译证据。

## 与最终目标的距离

不是生产全局语义 Inv；有限就绪关系、已选 TCB 字段和空 LocalInv 尚未连接完整池／链／事件、真实初始化、API／ISR 保持、Hook／栈和 WFIFun。既有手工 AST 不是已验证 C 前端。尤其既有 `V293SwitchPriorityBoundary.v` 已证明：只写 OSTCBCur 不足以保持独立 OSPrioCur 字节的一致性；本步的有限 Inv 不包含该一致性，不能把它无依据扩张为包含该字节关系的生产 GoodI。本步没有消除这个已知切换边界障碍。完整 OS_Sched 以及源码级 GOOD_OS／同程序 K1–K4 未完成；uCOS3 未开始，总目标 active；本步不提交／推送。

下一步先把原 OS_Sched 的优先级比较、计数写入及 switch continuation 接成连续控制轨迹，保留端口切换后 current priority 一致性义务，同时明确共享资源与恢复边界；不能只凭此次单步切换就声称整个调度器或内核正确。
