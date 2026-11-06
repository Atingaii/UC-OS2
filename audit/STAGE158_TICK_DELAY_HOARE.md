# 第158步：把原 tick 延时片段连接到正式 Hoare 规则

## 1. 本步解决的缺口

此前已有 tick 的实际逐步执行与返回资源证明，但执行端点不自动构成框架的 `InfRules`。本步直接证明原 `V293_tick_delay` AST 的规则：从字段所有权导出表达式求值，应用已有赋值、条件和顺序规则；再用既有 `RuleSound` 导出 `simulation.RuleSem`。不把所求执行或求值当作主接口的前提。

本步不是完整 tick 函数。原 `next` 前移、循环、临界区、CPU hook、ISR、调用者生产不变量及顶层 `GOOD_OS` 都不在这个片段里。

## 2. 固定对象

- uC/OS-II V2.93.01，提交 `0c4a48e6fbc6e915714e816196619a5481accf0c` 与原定两类授权修复；不增加修复。
- 原 `OSTimeTick` 的函数、配置后身份和 AST 见 [source-identity.json](logs/stage158-tick-delay-hoare/source-identity.json)。复用原 AST，不改 C、配置、framework、tactics、旧证明或旧证据。
- CPU hook 仍启用且开放；不安装空 hook。临界宏的既有手工映射也没有因此取得端口语义保持信用，见 [ADR-0005](../docs/adr/0005-显式临界宏映射不等于端口执行.md)。

## 3. 供后续连接的稳定接口

生产文件：`certiucos/v293/proofs/V293TimeTickDelayHoare.v`。

| 根 | 内容 |
| --- | --- |
| `V293_tick_expiry_fragment_hoare` | 原到期分支：处理 pending mask、pend 结果、挂起位和 ready bitmap |
| `V293_tick_delay_fragment_hoare` | 全部 unsigned delay、全部物理 status 字节的原延时片段 Hoare 规则 |
| `V293_tick_delay_fragment_semantics` | 从上述 `InfRules` 经既有 `RuleSound` 导出相同前后条件的 `RuleSem` |

主接口要求：合法 TCB 基址与字段地址、`0 <= d <= 2^32-1`、status／pend／group／row 为字节、`y<2`、`x<8`，以及 frame `R` 提供真实的局部／全局变量绑定和 `CurLINV li tid`。

前后都精确拥有原十个字段单元以及同一个 `R`：ptcb、delay、next、stat、pend、y、bitY、bitX、group 和当前 bitmap 行。这里不执行 next 前移；ptcb 和 next 的值不变。所有读取由真实字段资源导出；原赋值规则保留其余字段，不用 `Atrue` 丢掉 frame。

环境条件显式区分局部 ptcb 与全局 bitmap 名称，并要求后两个名称不被局部变量遮蔽。它不是只检查一组全局绑定就假定 AST 一定会读到它们。

## 4. 各分支究竟做什么

| 输入条件 | delay | stat／pend | bitmap |
| --- | --- | --- | --- |
| `d=0` | 不变 | 不变 | 不变 |
| `d>=2` | 减1 | 不变 | 不变 |
| `d=1`，有等待位 | 变0 | 清除原 pending mask；pend=1 | 未挂起时设置当前任务对应位 |
| `d=1`，无等待位 | 变0 | stat保留；pend=0 | 未挂起时设置当前任务对应位 |
| `d=1`，带挂起位 | 变0 | 仍按有无等待位处理pend | 不设置ready位 |

生产定理量化所有字节，而不只五个抽象等待构造子，因此也覆盖组合位和高位。这个事实仅证明物理字节行为，**不代表**挂起、flags、ECB 队列或抽象等待结果已接入生产状态关系。

## 5. 排除空真与单因素对照

探针：`audit/probes/V293TimeTickDelayHoareProbe.v`。

- `DHentry` 从具体不重叠字节构造可满足入口。另持有 block94 的真实只读 current 指针；全局／局部绑定放在独立空堆片段，再与字段、canary 和 LocalInv 分离连接。不是把环境断言直接强塞到非空堆上。
- `DHrules` 独立实例化新生产 Hoare 根。测试 LocalInv 是既有空见证，不是生产 Inv。
- `DHbranch_cases` 给出 delay `0/1/3/4294967295` 与 status `0/1/2/4/8/9/16/32/64/128/255` 的44种可满足入口与规则实例；不能用这44种实例代替一般定理。
- `DHwrong_row` 复用旧独立原到期执行：同一实际 Mf 的 bitmap 行为132，拒绝128，pend=1和canary99仍正确。
- `DHwrong_pend` 复用旧独立原到期执行：挂起＋等待时同一实际 Mf 的pend=1，拒绝0，bitmap行128和canary99仍正确。

两个负控只改变一个预期观察，不改变 C／AST、输入、执行或输出堆，没有 `store`／`del`。它们是独立旧操作语义的对照，不冒充新 `RuleSem` 的运行测试，也不作为新 Hoare 证明的前提。

协议先行记录于 [protocol.json](logs/stage158-tick-delay-hoare/protocol.json)，十项对抗审查见 [adversarial-review.json](logs/stage158-tick-delay-hoare/adversarial-review.json)。局部 Ltac 只选择字段并调用已有规则，没有新增语言、执行关系、推理构造子或公理。

## 6. 验收

本节结果以本步冻结的 `verification.json` 及证据清单为准；完整 `GOOD_OS` 不在本步验收范围内。

| 实际验收 | 结果 |
| --- | --- |
| 构建／清理后重建 | 均退出0 |
| 新增21根 | 假设检查通过 |
| 独立 `coqchk` | 328活动＋47探针＝375模块，退出0，806.62秒 |
| 信任检查期间531个Coq输入 | 哈希保持不变 |
| 实际假设 | 既有 `classic`、`functional_extensionality_dep`、`Eqdep.Eq_rect_eq.eq_rect_eq`，未扩展允许集合 |
| 新增回归 | 7项通过 |
| 三轮完整回归 | 各1937项，423失败／1错误；与第157步完整失败及错误ID集合完全相同 |
| 项目审计 | PROJECT通过；总体退出2，旧函数证据输入身份问题保留 |
| `git diff --check` | 退出2，仅旧 `framework/logic/inferules.v:581–586` 空白 |
| 历史文件核对 | 26311份；仅README、状态、项目入口与生成依赖4项预期差异 |
| 一次性清理 | 逐项确认9个目标后删除，共677583字节；两份既有缓存恢复原字节 |

冻结结果见 [verification.json](logs/stage158-tick-delay-hoare/verification.json) 及其引用的证据清单。保留44次编译的全部日志与稳定源快照，其中40次失败不改写成成功；保留生产／探针可复用Coq产品。只清理本步信任包装文件、临时诊断副本和已恢复的缓存备份。

`RuleSem` 根经既有 soundness 路径使用 Eqdep；其余实际假设也完整保留，不宣称无公理证明。不能仅凭文本回归或编译退出0代替本次独立内核检查。

```bash
make build COQBIN=/data/home/lucentzhou/.opam/default/bin/
PYTHONDONTWRITEBYTECODE=1 python3 -B -m unittest discover -s tests -p test_tick_delay_hoare.py -v
PYTHONDONTWRITEBYTECODE=1 python3 -B audit/logs/stage158-tick-delay-hoare/verify-checkpoint.py
```

## 7. 下一步与总目标

下一条纵向连接应在相同 raw 资源上补原 next 赋值，连接到循环接口，再逐项处理完整函数边界；不能把已有操作执行重新命名成 Hoare，也不能把原尾段与开放的 hook 拼成完整 API。

生产调用者 LocalInv／Inv、完整函数／ISR、初始化、WFIFun、源码级 GOOD_OS 及同程序 K1–K4仍开放。六门维持 `94/1/1/1/1/0`，本步没有新增源码函数覆盖信用。uC/OS-II 第一阶段未完成，uCOS3未开始；总目标 active，不提交／推送。
