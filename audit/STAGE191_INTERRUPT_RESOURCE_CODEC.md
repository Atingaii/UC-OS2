# 第191步：OSIntExit 资源编码接回完整函数构造器

## 本步真正消除的义务

第190步已经连接原完整函数和真实 `BuildPreI/BuildRetI`，但要求调用方另给 entry、acquired、leaving、restored 四个资源族特化等式。本步将动态元数据装入框架既有的 `list logicvar`，在同一资源族内解码，由 roundtrip 定理自动证明四个等式；没有更换调用规则、原 AST 或临界调用为原语。

新增生产模块：`certiucos/v293/proofs/V293OSIntExitResourceCodec.v`。供上层使用的稳定接口：`V293_OSIntExit_encoded_builder_contract`。

逻辑快照仅为证明参数，不增加运行时状态。静态布局与 `LocalInv` 沿用原接口；不同动态数据不再需要重新定义一套规格。

## 编码与不变量

| 内容 | 表示与证据 |
| --- | --- |
| lo、hi、current、nest、locked | 五个自然数字段，合法快照要求分别小于256；编码为整数值，解码检查 unsigned 值范围 |
| counter | 原 `int32` 原样携带，不截断为字节 |
| old、token、value | 三个任意 `val` 原样携带，不假设它们相同 |
| entries、tasks、aop | 分别用既有 `logic_lv`、`logic_abstcb`、`logic_code` 携带 |
| 任务与 saved 地址 | 从实际调用的 `tid` 和实参地址取出，不藏进固定 owner 常量 |
| 不匹配的逻辑列表 | 解码为 `None`，选择资源为 `Afalse`；`GoodFunAsrt` 对所有逻辑列表仍成立 |

`V293_exit_codec_roundtrip` 对所有合法快照证明解码恢复全部12个字段。`V293_exit_decode_bounded` 证明成功解码的五个自然数字段一定有界。`V293_exit_select_encoded` 把 roundtrip 提升到实际资源族，稳定接口中四次应用它消除原来的四个匹配前提。

这里**不是任意自然数编码器的无溢出保证**：`V293_byteval` 使用 `Int.repr`，无界自然数可能回绕。编码入口契约必须满足上述五个界限；解码检查针对实际整数的 unsigned 值。探针拒绝 current=256 的实例，不能据此声称所有越界原始自然数都被拒绝。

## 最小纵向证明链

1. 从原 `P f` 查询和实际 `BuildPreI/BuildRetI` 得到入口、返回断言。
2. 外部资源是规范的物理 pre，加 caller 绑定／frame；saved 的内部地址仍由 builder 资源中取出，对任意内部 block 处理。
3. 实际 saved 初始化和 running 守卫之后，通过真实索引临界调用使用编码的逻辑参数。
4. 中段直接复用已证明的物理资源桥与原调度逻辑，不把整个中段作为假设。
5. 出口调用和返回使用对应的解码资源族，重新包装真实返回 builder。

稳定接口只有两处 `InfRules`：结论中的完整原 body，以及仍开放的实际 `scall int_switch nil` 义务。后者限于调度启用且优先级不同的路径，对所有 saved block 量化，保留 caller frame／局部绑定，counter 已为 `Int.add c Int.one`。**四个资源等式已消除，切换义务没有消除。**

`Out` 与 `Sw` 是显式的、带 Good／local 条件的断言 continuation，不能作为 `logicvar` 值编码；不能把这两个语义参数误说成生产端口实现。主接口仍要求统一的 ready、table、数值条件，不声称是非运行路径的最弱前置。

## 前瞻协议与独立对照

协议事先固定在 `audit/logs/stage191-interrupt-resource-codec/protocol.json`。新探针 `audit/probes/V293OSIntExitResourceCodecProbe.v` 使用已有独立编码内存、分离 join 和物理状态构造，不用待证资源选择器生成物理堆。

| 对照 | 保持不变 | 得到的结论／边界 |
| --- | --- | --- |
| 完整 builder，嵌套2→1 | 同一个 `RCspec`，任意 counter | `RCdisabled_nested`：运行分支成立，但调度仍被嵌套层数禁止 |
| 完整 builder，嵌套1→0、current=12 | 同一个 `RCspec`，最高就绪优先级12，锁为0 | `RCenabled_same_priority`：调度启用，实际原调度／查表路径在 Hoare 推导中连通；优先级相同，不调用203号 switch |
| 完整 builder 入口独立非空 | 相同实际全局／局部绑定，独立物理堆 | `RCbuilder_pre_nonempty` 支持任意 counter 和任意 saved 旧值，包括 `Vundef`；不是从空前置推出闭合 |
| 同一物理堆，仅请求错误 counter=0 | 实际 counter=1，任务、nest=1、地址、saved、其他载荷均不变；两种编码都可成功解码 | `RCcounter_control` 用真实 `Tint32` load 排除错误解释，不靠 decoder 早拒绝 |
| 同一物理堆，仅请求错误 nest=2 | 实际 nest=1，counter=0，任务、地址、saved、其他载荷均不变；两种编码都可成功解码 | `RCnest_control` 用真实 `Tint8` load 排除错误解释 |
| 物理 counter／nest 单独改变 | 其余构造参数固定 | `RCcounter_frame`／`RCnest_frame` 分别证明14／11号块外每个字节保持不变；这是独立 frame 证明，不把两个实验变量混在一起 |
| 空列表、额外字段、current=256 | 同一资源选择器 | 分别拒绝；仅为解码层控制，不替代后续物理 load 或调用证明 |
| 全12字段载荷 | 各合法字段任意，counter 是任意 int32 | roundtrip 为普遍定理，不限于 fixture 的0和1 |

两个完整 builder 实例使用同一个 `RCspec`：scheduler=200、enter=201、exit=202，switch=203 的条目不存在；后者仅因两个实例均不走不同优先级路径而无需查找。没有给出实际端口函数体，也没有证明这个 Spec 的完整 `WFFunEnv`。

任意调用任务在生产接口中被普遍量化，但本步独立物理 heap fixture 仍只有 idle 任务；不把此前其他任务的探针算成本步生产多任务环境。禁调度实例 current=0，不声称它满足完整生产“当前 TCB 与当前优先级一致”不变式。

## 验证结果与失败保留

- 稳定编译：body05、probe10；全部15次编译尝试的源码快照、日志、JSON 保留，其中11次失败没有删除或改写为成功。失败包括展开／绑定名／实例化及 frame 重写位置问题；最终使用结构性物理 load 和定点 frame 重写，没有弱化对照。
- 两个新模块共31个引理／定理根逐一 `Print Assumptions`，两个入口的依赖递归 `coqchk`；限制在此前已有白名单内。检查时全部599个 Coq 源输入身份保持不变，临时信任驱动随后移除，快照保留。
- 新增5项结构／身份回归；语义证据来自 Coq 根，而非字符串检查。红灯记录保留，测试目标未修改。
- 两轮全量测试各2119项，保留原423失败、1错误以及全部有序 ID。新增测试全部通过，不是全仓测试通过。
- `make build` 和 project audit 通过；`make audit` 仍因旧 function evidence 输入身份陈旧失败；`git diff --check` 仍报告旧 `inferules.v` 581–586行空白。均分别保存日志，不清除旧失败。
- 新鲜重建的配置后原 C 与冻结身份一致。C、配置、原 AST、framework／tactics、旧证明／测试／冻结证据不改。根文档只前置本步说明，`_CoqProject` 只追加新生产文件。

最终机器报告：`audit/logs/stage191-interrupt-resource-codec/verification.json`；冻结清单：同目录 `checkpoint-evidence-manifest.json`。

复核：

```bash
make build COQBIN=/data/home/lucentzhou/.opam/default/bin/
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s tests -p 'test_interrupt_resource_codec.py' -v
PYTHONDONTWRITEBYTECODE=1 python3 audit/logs/stage191-interrupt-resource-codec/recheck-checkpoint.py
```

## 仍未完成与下一步

编码解决的是**局部静态布局下动态资源的传参和等式消解**，不是整核资源关系。canonical pre 继承原有 IE=false 条件；本步没有证明任意入口 IE 的实际禁中断／保存／恢复。资源快照与 Hoare 推导不等于原端口连续执行 trace；实际局部分配／释放 trace、生产 ISR／LocalInv、全任务临界环境也仍开放。ADR-0005 的宏归一化边界保持，不把原始调用偷换成已经验证的硬件端口。

下一步应让同一规格的生产临界边界获得可验证的实现／资源保持关系，再接真实启用且不同优先级的 `OSIntCtxSw`；不能用更多同优先级示例代替切换义务。随后接初始化、完整环境和全交错 simulation，建立源码级 `GOOD_OS` 并在同一程序排除 K1–K4。

六门仍为 `94 / 1 / 1 / 1 / 1 / 0`；**GOOD_OS 未完成，uCOS3 未开始，总目标保持 active**。本步未提交或推送。仅清理逐项登记的一次性驱动／过时生成器／本步备份，恢复既有 Coq 缓存原字节；编译证据、诊断记录与可复用 Coq 产物保留。
