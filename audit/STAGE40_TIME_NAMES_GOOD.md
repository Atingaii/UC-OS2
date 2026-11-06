# 第40步：共享时间 GoodI 与 API 使用同一个局部不变式

## 之前缺了什么

第37步的共享时间 `GoodI` 使用 `V293_shared_li`（空局部资源），第39步的 API 字面实例使用携带全局名称的局部不变式。两者不是同一个 Coq 项，不能把分别成立直接算成系统连接。

本步新增 `certiucos/v293/proofs/V293TimeNamesGood.v`，定义统一的 `V293_time_names_li now bn`，内容只是全局时钟的 `Agvarenv` 名称。稳定接口 `V293_time_names_compatible` 同时给出：

1. `GoodI (V293_time_shared_inv bn) V293_scheduler (V293_time_names_li now bn)`；
2. 使用完全相同 Inv／LocalInv 的真实 setter `APIRule`。

它对普通函数规格 `Spec` 和逻辑参数列表 `lg` 量化，不把将来的程序环境固定成某个演示环境。仅保留原来的三个名称不重合条件；不把 `GoodI`、NoAbs、全局名称蕴含或成功 store 当作调用者额外公理。

## 为什么新的 GoodI 不是换个名字

框架 `GoodI` 包含四项义务。第一项抽象帧完整性、第二项当前任务指针与抽象当前槽位一致性、第四项调度器性质不依赖 LocalInv，逐项复用原证明。

第三项包含旧任务已经离开任务表后的局部资源归还，**真正依赖 LocalInv**。本步重新处理它：

- 从新名称局部不变式推导其物理内存和抽象状态都为空；
- 显式代入 `Mx=emp`、`Ox=emp`；
- 构造旧空局部条件需要的实际 `satp` 证据；
- 保留原来同一个 `JM`／`JO` join，调用已经证明的归还分支。

这没有丢弃任务数据字节：本步的 LocalInv 本来就只有零字节名称事实。也因此，此结论不能推广为“任意含任务存储的 LocalInv 都可以直接运输”。

## 同一个规范局部不变式所需的其他义务

`V293_time_names_local_good`、`V293_time_names_noabs`、`V293_time_names_global` 分别证明 GoodLInv／精确性、NoAbs、调用前所需的全局名称事实。它们针对生产定义本身，而不是另造一个看起来相似的 probe 定义。

随后直接调用第39步的真实 `V293_TimeSet_api_rule`，不修改 C、归一化 body、API spec、共享 Inv、框架或旧证明。

## 独立字面非空连接

`audit/probes/V293TimeNamesGoodProbe.v` 不导入其他 probe；使用字面块80／81／82／90和任务91，参数42。局部不变式直接实例化生产定义。

| 检查 | 实际内容 |
| --- | --- |
| GoodI | `NamesSameGood`，名称 LocalInv，不是空 fixture |
| API | `NamesSameAPI`，与 GoodI 使用相同块和 LocalInv |
| 真实 builder | 字面前置／返回条件与 `BuildPreA'`／`BuildRetA'` 定义相等 |
| 非空调用者 | 具体内存满足实际 API 入口；同一调用者内存没有块80的任何字节 |
| 资源兼容 | 同一完整内存同时满足共享核心和真实 API 入口；指针两半来自真实写权限分裂 |
| 联合接口 | `NamesCombinedNonempty` 同时包含上述 GoodI、API、共享核心与入口，任意旧时间成立 |

这排除了“GoodI 使用 A、API 使用 B”以及“入口根本不存在”的当前缺口，但没有证明这些字面状态由 `OSInit` 可达。

## 前瞻单因素检查及信用边界

实现前冻结 `audit/logs/stage40-time-names-good/protocol.json`：

1. 仅在字面 GoodI 使用处移除新适配接口，直接使用旧空 LocalInv 的 GoodI；
2. 仅在联合接口的 API 使用处，把时钟块80换成81。

保持生产模块、字面内存、目标声明及其余 Proof 不变。预期分别在真实 GoodI 的 LocalInv 类型连接、API 的共享块索引连接被 Coq 拒绝。

这两项是**接口身份消融**，不是新执行语义攻击，不给运行时、下游函数行为或所有交错任何额外通过信用。原函数行为的前瞻参数／局部类型负控仍原样保留在第39步证据中。

## 开放项与下一步

- 已解决名称局部不变式对应的 GoodI／API 一致性；尚未引入完整任务、TCB、就绪位图、事件等资源不变式。
- 尚未从真实全局环境构造与 `OSInit` 执行建立初始化可达性；字面入口可满足不是初始化证明。
- setter API 入口仍限 IE=true／ISR 标志清零，使用框架既有 call／return soundness，未新增独立具体调用／free 轨迹。
- 默认 audit 的 stale 身份失败、历史测试诊断及六阶段94／1／1／1／1／0保留，不晋级覆盖。
- 完整源码级 GOOD_OS、同程序 K1–K4 未闭合，uCOS3 尚未开始，总目标继续 active。

下一步要从锁定配置后源码核对 OSInit／全局资源的实际构造，再把这里的同一套 Inv／LocalInv 接入程序和初始化，而不是把任意字面状态改名为初始化状态。

## 初始化预研：发现必须区分启动前与运行期

本步还对同一新鲜物化树执行 clang AST 检查，所有94个配置后函数身份与既有冻结清单逐项一致。`initialization-survey.json` 保存 OSInit、OS_InitMisc、OS_InitRdyList、OS_InitTaskIdle、OSStart 的准确身份、配置后函数体和赋值表达式；不授新证明覆盖。

实际观察：OS_InitMisc 清零 OSTime；OS_InitRdyList 把 OSTCBCur 写成 null；OSStart 调用 OS_SchedNew，再从优先级表取得任务并写入 OSTCBCur，随后调用 OSStartHighRdy。因此不能直接声称 OSInit 后已经满足要求有效 CurTid 的运行期共享 Inv。下一步须先建立启动前资源，再证明 OSStart 的当前任务指针安装及运行期不变式建立；idle 任务／非空就绪表与明确的 hook／上下文边界都不能略过。

## 实际收尾结果

正式 gate01 六命令退出码 `0／0／0／1／1／0`，独立 coqchk 两模块通过；生产3根／独立8根假设仅既有 classic／functional_extensionality_dep。旧空GoodI直连控制在第293行拒绝，错API时钟块控制在第298行拒绝；只授接口身份信用，下游／执行语义信用均为false。新增8测试清理前后全过。

全量1114测试实际376失败、1错误；此前377项诊断全部保留，新增／删除诊断均为0，清理前后multiset相同；不是全测试通过。scope／固定C／diff检查0；默认audit仍exit2（stale function evidence input identity），六门94／1／1／1／1／0未晋级。

旧180活动源／900生产依赖逐一不变；新增后181＝78目标＋103框架／tactics。基线只有已声明4路径前插／追加，缺失0；HEAD不变，未提交／推送。第36／37／38／39步冻结manifest分别117／142／98／111项无漂移，旧lia／nia缓存未变。

逐项列出类型、大小、hash／链接目标和目录成员，全部重新核实后首次unlink：删除392项（362软链接、30实文件／1129152字节）及49目录；仅两个接口负控树、一次新鲜C临时物化树、probe5产物。基线删除0；全部源／成功和失败证据／既有缓存／生产依赖保留，新增5个可复用生产产物保留。并非全仓source-only构建；总目标继续active。
