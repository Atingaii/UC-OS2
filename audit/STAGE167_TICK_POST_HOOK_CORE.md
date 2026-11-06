# 第167步：将同一 canonical 共享 core 连接到完整原 post-hook

## 这一小步解决什么

第166步解决的是如何从同一份 canonical task／ready／clock 资源打开完整任务链，并连接原 while。本步把它接到原后 hook 路径：

1. 执行真实 `OSTime++`，同一资源中的物理时钟与抽象 `ostmid` 同步更新。
2. 从实际拥有的 `OSRunning` 字节推出条件值，而不是要求调用者提供“求值成功”。
3. 只有 `OSRunning == 1` 时才执行真实 `ptcb = OSTCBList`，然后进入原完整 while。
4. 运行路径归还 task／ready／table／clock core、scan、全部链残余、globals 和 frame；停机路径只更新时间，其他资源完整保持。

生产文件：`certiucos/v293/proofs/V293TimeTickPostHookCore.v`。
稳定接口：`V293_tick_post_hook_core_hoare`；`V293_tick_post_hook_core_semantics` 由框架 `RuleSound` 得到。入口只要求 canonical core 与真正缺失的链字段补片，没有全链 raw、batch primitive 或执行成功 oracle。

## 独立验证与单因素对照

探针：`audit/probes/V293TimeTickPostHookCoreProbe.v`。

- 从四任务同块 encoded bytes 直接构造入口，使用布局打包引理，不调用旧入口或新主定理制造入口。当前 ready4 确实在任务表内，优先级表有实际13项，保留 readonly current、clock、canary99、合法栈顶1。
- scan 初始为 idle，而非非空 head。实际初始 while guard 为 false；因此运行路径不能省去 head 赋值。
- `run=1` 走原完整 while；`run=0/255` 保持链与 bitmap，仅更新 clock；初始 IE 为任意布尔值。
- 在本步新堆上独立执行原操作语义，检查全部预期链字段、bitmap、clock 和 canary。该执行证明不是新 `RuleSem` 的运行实验。
- 对普通时钟37和最大无符号时钟，停机执行给出同一个真实 `Mf`。正确抽象时钟沿合法抽象步骤推进后可重新打包完整 canonical core；仅把抽象 `ostmid` 留在旧值，其他物理堆、环境、控制、taskmap、events、程序及 frame 不变，clock agreement 拒绝错误 core。
- 最大无符号时钟的物理结果为0，同时覆盖 `run=0/1/255`。
- 混合链任务更新中和负控明确复用第165步：新后缀输出 `Mf` 与旧 while 输出 `oldMf` 分别命名，不把两个执行端点混为同一输出，也不把旧操作执行包装成新 `RuleSem` 的运行。

协议在实现前写入 `audit/logs/stage167-tick-post-hook-core/protocol.json`，保留原文件。

## 证明脚本调试的范围

性能中断和编译错误的逐次源码快照／日志保留，不算语义反例或消融通过。
独立探针的字节分离检查器有 Coq 健全性证明，仅检查固定资源地址分离，不预测执行结果。
资源重排使用精确 `Permutation`，没有删除字段或放宽空间断言。定向归约和相同尾项的自反规则避免展开开放 `run` 的大整数计算；程序、fixture、命题和验收门槛保持不变。

## 验收状态

生产 `core12` 与最终探针 `probe22` 编译退出0，前后源码哈希及快照一致。构建和清理后构建退出0；39个新增证明根、337个活动模块与57个探针模块通过独立检查，549份 Coq 输入检查期间不变，允许假设与第166步相同。

新增5项回归全部通过；三轮完整回归均为1998项、旧423失败／1错误，失败与错误的完整 ID 集合与1993项旧基线相同。旧审计仍因函数证据身份过期退出2，旧六行 whitespace 仍在，未改动它们以制造全绿。

34次编译快照及日志保留，包含29次非零结果；其中5次主动性能中断单独记录，不当作语义反例。先确认全部清理目标与缓存备份后，删除8项一次性材料共691141字节，并恢复既有 `.lia.cache`／`.nia.cache`；保留源码、失败／中断证据和可复用 Coq 产物。

最终核对29407份旧文件、第166步冻结 manifest、主接口无执行 oracle、独立入口和同 Mf 单因素对照；只有本步前插说明、项目末尾追加项及生成依赖可改变旧文件。正式冻结结果见 `audit/logs/stage167-tick-post-hook-core/verification.json` 和同目录 `checkpoint-evidence-manifest.json`；仅在全部门槛通过后生成，不把局部检查点记作整核完成。

## 仍然没有解决的部分

- 调用者已经持有 canonical core；通用 ISR 不变量借还规则不等于从生产 IRQ 不变量中取出这些资源。
- 仍限制合法、未挂起有限链，完整 canonical 任务域等于 bindings 加 idle；不是任意内核任务状态。
- `LocalInv` 仍为旧空见证，不是由真实初始化建立的可达状态。
- CPU hook、完整 tick 函数／API／ISR、生产 Inv／LocalInv、初始化、WFIFun、最终源码级 GOOD_OS 及同程序 K1–K4 仍开放。

函数六门仍为94/1/1/1/1/0，不新增整函数信用。第一阶段未完成，uCOS3 未开始；总目标仍 active。没有提交或推送，也没有修改 C、配置、AST、框架、tactics、旧证明、旧测试或既有冻结证据。

下一步应把现有 canonical 入口和精确残余接到生产不变量与函数前后文，而不是再增加要求 caller 预拆整链的旁路接口。
