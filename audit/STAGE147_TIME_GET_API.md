# 第147步：OSTimeGet 在读取瞬间线性化，并接入共同 API 表

## 为什么做这一步

最终目标仍是固定配置 uC/OS-II V2.93.01 的源码级整核 `GOOD_OS`，以及同一程序的 K1–K4 回归。第146步只有 OSVersion、OSTimeSet 两个 API 和 OS_SchedNew 一个内部函数的共同组件。

原来的 getter 局部证明只说明返回某个读到的值，抽象动作本身没有要求该值与共享时钟相同。本步补上这个缺口，而不是再增加调度轨迹示例，也不采用“任意返回值均可”的较弱规格。

## 用普通程序理解

真实函数按以下顺序工作，C 源码与已有归一化函数体均不修改：

```c
cpu_sr = 0u;
OS_ENTER_CRITICAL();
ticks = OSTime;
OS_EXIT_CRITICAL();
return ticks;
```

证明分成三个关键时刻：

1. **进入临界区**：从已有共享中断不变式取得时钟字节及其抽象对应关系。调用者自己的前置条件不占有时钟字节。
2. **读取时**：执行真实 `ticks = OSTime` 的原赋值规则，再用原 `spec_prim_step` 线性化。抽象结果严格等于此刻时钟，整个抽象状态 `O` 不变。
3. **退出与返回**：归还共享时钟资源，保留局部 `ticks` 和已确定的抽象结果。之后其他执行者可以推进时钟；因此不声称返回时全局时钟仍等于 `ticks`。

“线性化”在这里的含义是：把这次 API 调用的抽象效果定位在临界区内的读取瞬间，而非把整个函数期间的时间都冻结。

## 代码与稳定接口

| 文件／定理 | 解决的义务 |
| --- | --- |
| `V293TimeGetAPI.v`／`V293_time_get_transition` | 原抽象步读取时钟，结果准确，所有 `O` 保持不变 |
| `V293_time_get_absinfer`、`V293_time_get_copy` | 将抽象动作接到原物理赋值及共享所有权 |
| `V293_OSTimeGet_refined_body` | 保留原函数体，连接清零、临界区和实际返回 |
| `V293_TimeGet_api_contract` | 连接原 `BuildPreA'`／`BuildRetA'`；无参 API、两块局部资源、返回资源归还 |
| `V293TimeGetLink.v`／`V293_clock_components_checked` | 同一 Spec、scheduler、共享 Inv、name-only LocalInv 下的三个 API＋一个内部函数 |
| `V293TimeGetAPIProbe.v` | 非空资源、真实 builder、正确／错误返回对照及四个合并后函数绑定 |

共同 API 表的三个分支分别使用已有 OSVersion 契约、已有 OSTimeSet 契约与新 OSTimeGet 契约；没有把 singleton 表的 builder 等式直接冒充合并表的等式。内部 WFIFun 复用第146步已经完成的函数证明，不增加一个“假定函数体已正确”的前提。

## 身份与可满足性

`source-identity.json` 记录当前上游 `os_time.c` 的文件与237–250行哈希，核对旧预处理函数体哈希；归一化 AST 继续使用未修改的 `V293TimeAccess.v`。这是源码定位及既有模型的连接，**不是本步重新验证的 C 前端翻译**，不增加六门覆盖信用。

探针复用旧 `V293TimeNamesGoodProbe.v` 的实际字节布局与空间所有权证明，不复制另一套布局。只有抽象动作从 setter 改为 getter：原 `change_aop_rule` 明确要求相应资源与动作无关。

- `checked_get_actual_builders`：在整个三 API 表中计算原 builders。
- `checked_get_caller_entry`：真实 caller 前置条件可满足；调用者没有全局时钟字节。
- `checked_get_joint_entry`：任意32位时钟下，共享 core 和同一 LocalInv 的 getter 前置条件可以同时满足。
- `checked_get_body_same_shared_environment`：原 getter 函数体在同一 LinkSpec／LinkLI 下满足实际 builders。

该有限见证的抽象 TCB／ECB 表仍为空，不能据此宣称完整任务关系不变式、调度器和所有资源同时初始化可达。

## 预先约定的单因素对照

保持原抽象状态 `NamesAbstract(37)`、物理时钟字节、参数和动作完全不变，只把候选返回值从37改为38：

- 正例：物理 `load` 得到37，原 `spec_step` 返回37且不改变抽象状态。
- 反例：原 `spec_step` 不可能返回38。
- 更一般的 `checked_get_read_result_exact` 直接反演原抽象步，并处理其 frame：只要输入 `O` 的时钟为 `clock`，每个该动作的一步结果都必须是 `clock`，输出整个 `O` 必须与输入相同。

反例没有依赖非法参数、名字冲突或入口提前拒绝。因此它检查的是读取结果约束；不把它夸大成某个修改后 C 实现的全局执行反例。

## 验证、证据与复现

本步最终结果以 `audit/logs/stage147-time-get-api/verification.json` 和 `checkpoint-report.json` 为准；保留失败编译、源码快照、初次测试失败及中断的独立检查日志。初次严格词检查命中了英文注释中的自然语言单词，处理方式是改注释、重新编译并重做检查，不放宽测试。

```bash
make build COQBIN=/data/home/lucentzhou/.opam/default/bin/
PYTHONDONTWRITEBYTECODE=1 python3 -B -m unittest discover -s tests -p test_time_get_api.py -v
```

独立检查命令与27个新证明根记录在 `trust.json`；检查315个活动模块及34个额外探针模块。额外模块包含本步复用并重新编译的旧 names 探针，不把它计为新源码成果。构建缓存中已有的 `.lia.cache`／`.nia.cache` 在任务清理时恢复；一次性 Trust 产物清理清单与哈希另行保存，可复用 Coq 产物及全部失败证据保留。

## 本步实际检查结果

| 检查 | 结果 |
| --- | --- |
| 初次及清理后构建 | 通过 |
| 新增测试 | 6项通过 |
| 全套回归 | 1864项；原423失败／1错误，失败与错误ID集合不变 |
| 新证明根 | 27根全部检查；只依赖原有 classic／函数外延性，无新增假设 |
| 独立 `coqchk` | 315个活动模块＋34个额外探针模块通过，约643秒 |
| `make audit` | 仍失败：旧 `stale function evidence input identity` |
| `git diff --check` | 仍失败：旧 `framework/logic/inferules.v:581–586` 空白 |
| 26920个旧文件身份 | 只有中文入口前缀、`_CoqProject` 和生成依赖表发生预期变化；旧 C／配置／AST／框架／证据不变 |
| 任务清理 | 核对后清理8项一次性产物／缓存备份，恢复两个原有缓存；可复用证明产物和失败证据保留 |

## 尚未完成什么

- 这仍是三个 API＋一个内部函数的组件，不是94函数整核。
- 共享时钟 Inv 和 name-only LocalInv 不是完整生产任务生命周期 Inv。
- 全部生产 WFIFun、ISR、初始化 `side_condition`、源码级 GOOD_OS、同程序 K1–K4 仍开放。
- 六门仍为94/1/1/1/1/0；旧423个失败、1个错误、旧审计身份错配不改写、不隐藏。
- 没有新增 C 修复、修改原框架或旧 AST；没有开始 uCOS3；总目标保持 active，未提交／推送。

下一步应继续补真实函数／共享不变式的纵向连接，优先检查 tick 写入及任务延时状态与时钟的关系；不能把读取成功当作时钟更新、唤醒或所有下游机制都已经成立。
