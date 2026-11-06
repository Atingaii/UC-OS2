# 第208步：同优先级退出的真实 builders 与三函数环境

## 接续什么，实际新增了什么

第207步证明完整同优先级归一化本体，但前置里已经有 saved 局部单元。本步连接框架真实 `BuildPreI/BuildRetI`，并用同一个增强 scheduler Spec 闭合 OSIntExit、OSIntEnter、OS_SchedNew 的 `WFFunEnv/WFIFun`。不再把整个退出本体作为环境定理的假设。

- 生产文件：`certiucos/v293/proofs/V293OSIntExitSameInternal.v`。
- 稳定接口：`V293_OSIntExit_same_builder_contract`。
- 环境接口：`V293_same_exit_env_WFFunEnv`、`V293_same_exit_env_WFIFun`。
- 独立探针：`audit/probes/V293OSIntExitSameInternalProbe.v`。

**这里的 P 是既定、已接受的归一化本体；不是原始 CPU 临界调用的执行精化。退出契约只覆盖 running=1、nesting≤1、lock=0、最高就绪优先级等于当前缓存的路径。三函数环境闭合不意味着全部退出行为或整核完成。**

## 从调用边界看证明

1. 函数外部断言只提供普通内存、全局地址、抽象操作、原 IE/ISR/两栈，不提供 saved、局部地址或不遮蔽事实。普通内存与外部断言分别证明 `GoodFunAsrt`。
2. 逻辑参数复用既有 exit snapshot，加上 IE、ISR、ISR 栈、临界栈。有效性还要求字节范围、就绪位图/任务表关系和同优先级选择条件；不能把解析成功等同语义有效。
3. `BuildPreI` 根据真实零形参函数和 saved 单局部声明生成局部资源及精确 domain。由 domain 和各全局名不同于 saved，推导不遮蔽事实；不是预先放进函数外部规格。
4. unpack 将实际 builder 资源重排为第207步本体前置；直接复用其单个 `InfRules`，没有假设整个本体或 callee 正确。调度契约所持 Inv 与本步 ambient Inv 一致。
5. pack 保留调用者资源、saved 单元和局部 domain，给出真实 `BuildRetI` 的结果。最高任务指针/最高优先级已更新，nesting=0，counter 与原 IE/ISR/两栈保持。
6. 三函数程序使用实际进入、调度及归一化退出函数；分别证明其真实 builder→InfRules，统一使用增强 scheduler 契约。没有把第204步 plain Spec 的条件等价式改名当作本步证明。

当前字节资源权限按真实断言匹配：running/current 读权限，nesting/high/输出/counter 按既有单元接口提供；没有通过省略写入资源来取得通过。

## 独立非空与单因素控制

`BIbuilders` 按定义算出实际零实参 builders。`BIowned` 从此前独立字节内存构造 `QPpre_nonempty` 出发，推导新的资源排列；不假设本步目标前置或本体结论。`BIpre_nonempty` 证明同一个具体状态满足本步真实 builder 前置：位图=(0,16)、最高/当前优先级12、nesting=1、lock=0、counter=1、saved 原值1、ISR 栈=[0]、临界栈=[false]。原 IE 参数化，故两值均非空。

`BIdecode/BIvalid` 排除前置解析失败或非法 snapshot 的空洞。`BIie_control` 固定全部内存、实际 IE=true、ISR/两栈与其他逻辑参数，只把逻辑 IE 从 true 改为 false；正控满足，反控由真实 Aie 矛盾排除。**这只检验规格与现场身份，不是两个完整变体执行，也不证明每个下游步骤都会失败。**

`BIarity_control` 检查零形参 `BuildPreI` 拒绝非空实参。第一次也预测 `BuildRetI` 拒绝，probe06 实测失败：框架返回 builder 不检查形参数量。保留失败快照；`BIreturn_arity_observation` 正式记录其仍可生成返回断言。事前协议要求的准入控制由前置 builder 完成；返回 builder 不被误报成第二道拒绝门。没有改动框架或事前协议。

## 核验和审查

证据目录：`audit/logs/stage208-interrupt-exit-same-builders/`。

- 事前协议与基线先于实现冻结；每次编译保留快照、日志和退出码。编译期间不编辑 Coq 输入。
- 固定源码、配置、AST 不变；重新构造 OSIntEnter/OSIntExit/OS_SchedNew 配置后源码，校对各自函数身份。
- 18 根逐项 `Print Assumptions`、两入口递归 `coqchk`，允许假设不扩大。稳定编译版本见 `stable-compiles.json`；失败记录不删除。
- 新增5项结构回归，不冒充语义 TDD；完整旧失败/错误及顺序保持。项目审计、构建、旧 coverage 审计与旧空白检查分开报告，不把旧失败伪装成通过。
- 逐项确认一次性信任驱动、产物与缓存备份后清理，恢复原缓存字节；证据、源码和可复用 Coq 产物保留。最终数字及清单见 `verification.json`。

审稿式边界：具体 LocalInv/ISR 见证不是生产状态可达性；窄规格 WFFunEnv 不证明其他退出路径；真实 builder 不等于局部单元分配/释放的完整执行 trace；归一化源码身份不等于端口 refinement；参数化 Inv 不等于生产 Inv 已构造。

## 还要怎样继续

本步只关闭第207步留下的同优先级 builder 和增强三函数环境缺口。不调度路径还需并入同一动态退出规格，不同优先级 handoff Hoare 仍开放。随后必须解决生产 Inv 数据所有权、生产 ISR/LocalInv/WFInt、初始化与整核链接。

六门仍为 `94/1/1/1/1/0`；源码级 `GOOD_OS`、同程序 K1–K4 尚未完成，uCOS3 未启动。目标保持 active；未提交或推送。
