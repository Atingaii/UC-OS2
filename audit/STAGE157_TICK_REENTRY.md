# 第157步：从真实 tick 返回资源构造下一轮入口

## 1. 解决什么问题

第156步证明了原始字段与精确规范布局的无损分解。但一般的存在量化任务记录隐藏了实际 `pend` 等取值，不能倒推任意记录来恢复下一轮可写链。

本步不做这个不成立的逆推。沿真实原尾段执行保留精确 raw 字段，确定性构造下一轮 binding，并在同一个实际返回堆中保有下一轮所需资源。raw 出口和规范记录出口是两种打包方式，不是同一权限的两份副本。

## 2. 固定对象与未改范围

- 对象仍为 uC/OS-II V2.93.01，提交 `0c4a48e6fbc6e915714e816196619a5481accf0c` 与既定两类授权修复。
- `OSTimeTick` 身份见本步 [source-identity.json](logs/stage157-tick-reentry/source-identity.json)；原函数、配置、AST、framework、tactics、旧证明、旧测试和旧证据不改。
- 复用原 `V293_tick_uninitialized_suffix_execution`、抽象时钟／链转换及两局部真实释放证明，不引入第二套执行语义。
- CPU hook 仍启用且开放。不安装空 hook，也不把分配前缀和 post-hook 尾段拼成完整调用。

## 3. 证明接口

| 文件／根 | 作用 |
| --- | --- |
| `V293TimeTickReentry.v` | 用实际 `task_after` 字段和更新后的状态确定下一 binding；证明合法性、地址／键不变、任务表与原输出一致 |
| `V293_tick_reentry_extras_permutation` | 精确排列旧 extras 为新 extras 与到期后遗留的 event 指针；不借 `Atrue` 丢弃资源 |
| `V293_tick_reentry_shared` | 只更新现有 clock／tasks 两抽象槽，保留其他共享槽与 frame，不任意重解释抽象状态 |
| `V293_tick_reentry_entry` | 实际已分配的 `Vundef` ptcb、初始化为0的 saved 与 raw payload 重组为旧原尾段入口 |
| `V293_tick_raw_reentry_return` | 执行原 post-hook 尾段、返回、两次实际 free，恢复 caller；同一 Mf 持有下一轮 raw payload 与所有遗留字段 |
| `RPtwice` | 从非空构造入口执行第一轮；由第一轮 Mf 推导全偏移 fresh，实际再次分配／初始化局部变量，再执行第二轮 |
| `RPobservations` | 读取两轮真实返回堆，不只比较抽象记录或预设布局 |
| `RPnext_control` | 从正确第一轮 Mf 只移出首个 next 的所有权，保留其余资源与完整抽象状态；证明剩余片段不能满足完整再入口 payload |

生产 payload 精确持有时钟、运行标志、链头、raw 链、bitmap、idle、extras、优先级表、caller／遗留字段、一个实际 current 指针及四个共享抽象槽。没有额外 `Atrue`，也没有规范记录权限的重复副本。

## 4. 非空两轮实例

复用第156步已经实际构造的第一轮分配入口，不复用旧的执行结果作为新执行假设。三个非 idle 任务与 idle 共用同一 block 的不重叠区间；caller9999 指向确实拥有的 canary90。

| 观察 | 初始 | 第一次真实返回 Mf1 | 第二次真实返回 Mf2 |
| --- | --- | --- | --- |
| clock，block101 | 37 | 38 | 39 |
| sem 等待首任务，优先级10 | delay1、pend7 | ready、delay0、pend1 | ready、delay0、pend1 |
| time 等待第二任务，优先级2 | delay3 | delay2 | delay1 |
| 原 ready 任务，优先级4 | ready、pend7 | ready、pend7 | ready、pend7 |
| 高 bitmap 行 | 16 | 20 | 20 |
| 首任务旧 event 指针，81:36 | 84:4 | 显式遗留字段，实际可读取 | 继续保有，实际可读取 |
| caller canary，90:0 | 99 | 所有权保留 | 实际读数99 |

两次尾段之间确实重新执行 `call_to_hook` 的两次分配与 saved=0；ptcb 的实际读数仍为 `Vundef`。fresh 不是由“free 后前四字节空”推断，而是由第一轮完整精确 payload 证明70／71两个 block 的**全部偏移**均不存在，再证明第二次分配不影响另一 block。

这两次尾段之间仍隔着未证明的 hook 边界。因此“可复用 raw 入口”不等于“连续两次完整 API 调用”。

## 5. 预先指定的消融与边界

[protocol.json](logs/stage157-tick-reentry/protocol.json) 先于实现写入，指定三组检查：

1. 两轮非空原尾段，由第一次真实输出构造第二次入口；不能把第二次执行或 fresh 作为前提。
2. 只移出首个 next-link 权限；原实际 Mf、C／AST／执行不变，补片保有其余所有字段、caller、遗留指针和同一个抽象状态。移出后81:28首字节为None，完整 raw payload 要求的读取因此不成立。
3. 五类已表示的等待原因各检查 delay0／1／3，包括 time 到期与 event 到期 pend 的差异；两轮实例另含已经 ready 的任务。数量检查不是一般排列与空间所有权证明的替代。

对抗审查见 [adversarial-review.json](logs/stage157-tick-reentry/adversarial-review.json)。未扩展到挂起、flags、ECB／等待结果的完整生产关系，也不把选定字段说成完整TCB。

## 6. 验收与可重现入口

本步最终结果以 [verification.json](logs/stage157-tick-reentry/verification.json) 和其引用的不可覆盖清单为准。独立验证覆盖27个新增根，327个活动模块及46个额外探针模块。新增7项回归文本／身份检查不能代替Coq根与 `coqchk`。

| 实际验收 | 结果 |
| --- | --- |
| 构建／清理后重建 | 均退出0 |
| 27个根的假设检查 | 通过；实际仅依赖既有 classic／functional_extensionality_dep |
| 独立 `coqchk` | 327活动＋46探针＝373模块，退出0，802.82秒 |
| 信任检查期间529个Coq输入 | 哈希保持不变 |
| 新增回归 | 7项通过 |
| 两轮全套回归 | 各1930项，423失败／1错误；与第156步的完整失败及错误ID集合相同 |
| 项目审计 | PROJECT AUDIT通过；总体退出2，旧函数证据输入身份问题仍在 |
| `git diff --check` | 退出2，仅旧 `framework/logic/inferules.v:581–586` 空白 |
| 旧文件核对 | 28000份；仅README、状态、项目入口及生成依赖4项预期差异 |
| 一次性清理 | 先确认8个目标再删除，共673931字节；两份既有缓存恢复原字节 |

原始结果、44次编译的稳定源快照与失败／中断记录均保留。清理只删除信任检查包装文件及已恢复的缓存备份；新生产／探针Coq产品作为可复用验收材料保留。

```bash
make build COQBIN=/data/home/lucentzhou/.opam/default/bin/
PYTHONDONTWRITEBYTECODE=1 python3 -B -m unittest discover -s tests -p test_tick_reentry.py -v
PYTHONDONTWRITEBYTECODE=1 python3 -B audit/logs/stage157-tick-reentry/verify-checkpoint.py
```

开发过程失败与受控中断的源快照、日志、退出码均保留；未改写成成功记录。符号到期分支不再展开全部整数／bitmap定义做巨大 `lia`，而复用现有节点合法性引理。探针中未实例化列表的构造搜索中断后，先用真实 Held 固定列表，再证明其支持集合。

## 7. 尚未完成与下一步

- 当前只闭合原运行分支 raw 字段的可复用端点；未证明完整调用入口或完整函数 Hoare。
- 下一步应将可复用 raw 资源与已有 ready 组件接口作不重复所有权的连接，并明确补齐 CPU hook／临界区与生产不变量的桥接义务，不能继续把端点执行当作 ISR 或完整 API。
- 生产 caller LocalInv／Inv、初始化、ISR安装、WFIFun、源码级 GOOD_OS 和同程序 K1–K4仍开放。
- 六门维持 `94/1/1/1/1/0`，无新函数覆盖计分。旧423失败／1错误及旧证据输入身份问题保留。
- 第一阶段未完成；uCOS3未开始。总目标 active，不提交／推送。
