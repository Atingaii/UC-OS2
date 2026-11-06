# 第169步：原 tick 后 hook 接受真正未初始化的扫描槽

## 为什么前一步还不能接完整函数

固定上游 `Source/os_core.c` 第937–1008行的 `OSTimeTick` 声明 `OS_TCB *ptcb`，没有初始赋值。实际局部分配后的槽值是 `Vundef`，不是 idle 指针。第168步的共享入口仍要求 scan 是已类型化的指针；不能用那个契约直接接真实分配结果。

本步仅补上这一接口缺口，不修改 C、配置、AST、框架、战术或此前证明。生产文件为 `certiucos/v293/proofs/V293TimeTickScanSlot.v`，上层接口为 `V293_tick_scan_switch_hoare`；`V293_tick_scan_switch_semantics` 只经既有 `RuleSound` 导出。

## 从内存事实推导最小接口

- scan 使用拥有写权限的原始 `Amapsto`，允许任意初值；不声称 `Vundef` 满足 pointer 的类型匹配。
- 时钟更新不读取 scan。读取真实 `OSRunning` 后，仅 run=1 执行 `ptcb = OSTCBList`：赋值读取 head，安全覆盖 scan，不读取旧 scan。
- 覆盖后指针已经类型化，可直接连接原完整 while 及既有 task／ready 更新证明。
- run=0/255 不进入该赋值和 while；返回时原始 scan 仍为 `Vundef`，不能凭空变成 idle 指针。
- 共享取还沿用第168步的同一 `V293_time_ready_inv`、additive view 及实际抽象槽对齐。没有另造 Inv，也没有将控制标志非法藏入 GoodFrm。

一般 raw-core 接口保留原有两种初始 IE 的条件形式；本步实际 SWINV 连接和独立执行探针仍为 IE=false、ISRclear。前者不能当作生产 enabled=true 首次借出已经完成。

## 同一入口的独立执行与对照

探针为 `audit/probes/V293TimeTickScanSlotProbe.v`。事先固定的四项对照、三项限制及其身份保存在本步 `protocol.json`、`protocol-identity.json`，未用结果反写协议。

| 检查 | 保持不变的内容 | 可观察结果 |
| --- | --- | --- |
| `SSentry` | 原四任务字节堆、13项优先级表、readonly current、canary99、合法栈顶1 | 只对 scan 作保持权限的 `store Vundef`，由字节资源独立打包同一 SWINV；真实 load 为 `Vundef` |
| `SSwrong_pointer` | 同一 M、抽象表、程序、Inv 和补片 | 只把入口 scan 见证换成 `Vptr idle`，由同址真实 load 矛盾拒绝 |
| `SSundef_not_typed` | scan 值和类型不变 | 原始 `Vundef` 不能包装成 typed pointer |
| `SSrunning`、`SSstopped` | 同一新入口构造及原程序 | 正式实例化 run=1 与 run=0/255；运行返回 idle 指针，停机保留未初始化槽 |
| `SSexecution` | **恰好是 `SSentry` 的同一个 M** | 直接应用既有原操作语义的未初始化后缀执行；核对时钟、scan、全部链／bitmap／idle字段、canary及精确残余 |
| `SSwrap` | run=0、1、255 的同类入口和原程序 | 最大无符号时钟回绕为0，scan按真实分支变化，canary保持 |
| `SSclock_neutralized` | 同一次新执行的 Mf、控制状态、taskmap及全部物理字节 | 停机时更新抽象 clock 可恢复完整新 SWINV 入口；仅中和抽象 clock 后连 time-ready core ** Atrue 也拒绝，覆盖37及最大时钟 |

入口路径为 `PCjoint → PCpack → SSreplace → SSpack → SSclose`，不调用新 opening 或新主定理制造入口。执行直接使用 `V293_tick_uninitialized_suffix_execution`，不是重用旧 scan=idle 的 `PCmemory` 执行结果，也不冒充新 `RuleSem` 的运行实验。

**store 构造的 fixture 不是实际 callee allocation。** 它只证明新 raw 接口非空、能承接真实 `Vundef` 编码及原执行；尚未把函数的两个 local 分配、CPU hook 与本步共享入口连接起来。任务更新中和负控仍是第165/167步明确标识的旧端点，不声称它发生在新 Mf 上。

## 验证记录

稳定生产编译 `slot05`、探针编译 `probe15` 均退出0，开始／结束源码哈希一致。20次编译快照与17次非零结果全部保留；其中 `probe10` 是主动性能中断，`probe11`–`probe14` 是局部证明搜索超时，均不是程序语义反例。隔离布局诊断 `.input.txt` 与日志只作诊断，不作为最终证明通过的证据。

隔离诊断发现布局两侧仍含不同形式的闭数地址和记录字段投影。将这两类表达式一并局部归一化后，相同资源及相同结论的证明编译通过；没有删除字段、弱化契约或改写失败快照。这是组合修正的实测结果，没有分别消融两类展开，不能宣称各自独立的性能贡献。

源码核对使用实际存在的 `current_upstream_file`，检查整文件及第937–1008行的哈希；继承身份记录中的旧 `csrc/repaired/...` 定位当前不存在。没有为通过检查伪造该 checkout，也没有改写旧身份或旧审计结果。AST 仍是既有人工源码模型，不是已验证的 C 前端。

30个新增证明根通过假设检查，339个活动模块和59个探针模块通过独立 `coqchk`；检查期间553份 Coq 输入不变，允许假设集合与第168步完全相同。新增5项结构回归全部通过；完整回归每轮2008项，旧423失败／1错误及完整 ID 集合保持。各轮机器结果及最终旧文件核对以本步 `verification.json` 为准，不能仅凭本文或 wrapper 的进程退出码宣告验收。

构建与清理后构建退出0；旧审计仍为 stale function evidence input identity，`git diff --check` 仍只报框架旧六行 whitespace，没有改写这些失败。逐项确认后清理10项一次性材料696645字节，恢复既有 `.lia.cache`／`.nia.cache`；保留正式源、全部失败快照、明确标识的隔离诊断及可复用 Coq 产物。清单、哈希和清理记录保存在本步证据目录，冻结 manifest 不包含自身。

## 未完成的上下文与下一步

1. 本步仍限合法未挂起有限任务链，canonical 域匹配 bindings 加 idle；不是任意生产任务状态。
2. 同一 SWINV 的 IE=false／ISRclear 边界不等于统一生产 ISR／Inv／LocalInv 安装；旧空 LocalInv 也不是初始化可达性证明。
3. 下一条真实连接应复用 `V293TimeTickLifecycle.v` 的 `V293_tick_call_to_hook` 实际两槽分配结果，保留 callee 环境、saved槽、分离权限及原始 `Vundef`，连接 CPU hook 返回与本步后缀；不再复制分配证明或制造另一个 fixture。该旧接口只是实际操作执行片段，不能反推正式 Hoare；hook 也必须保留真实调用及待证的保存契约，不能删去或假定无效果来过门。
4. 完整 tick／API／ISR、初始化、WFIFun、最终源码级 GOOD_OS 及同程序 K1–K4 仍开放。六门仍为94/1/1/1/1/0，本步不增加整函数信用。

第一阶段尚未完成，uCOS3 未开始；总目标 active，不提交或推送，不改旧失败以制造全绿。
