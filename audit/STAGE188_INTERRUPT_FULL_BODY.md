# 第188步：原 OSIntExit 完整函数体的条件 Hoare 证明

## 本步接上了什么

第187步已经实际组合 enter／已证明的调度中段／exit，但还没有接到原函数体开头与结尾。本步稳定接口 `V293_OSIntExit_body_hoare` 位于 `certiucos/v293/proofs/V293OSIntExitBody.v`，覆盖原 `V293_OSIntExit_body`：

1. 对已分配并绑定的 `saved` 单元执行真实 `saved := 0`。
2. 通过全局绑定、局部不遮蔽事实和物理 `load Tint8` 求出 `OSRunning == 1` 的值与类型，不要求调用者提供表达式求值结论。
3. 运行时直接调用第187步资源桥，连接真实 enter、已有中段与 exit；不新增“整个 enabled 分支正确”或“整个中段正确”的 Hoare 前提。
4. 不运行时跳过这些调用，但不跳过前面的 saved 清零；最后两条路径均执行真实 `sret`，返回 `None`。

原 C、配置与 AST 没有改写。源码检查脚本重新物化授权修复集、重放 clang 预处理，对照冻结清单核验 `os_core.c:693–736` 的源码范围、完整定义、函数体与直接调用身份。空 trace 仍来自原有 AST，没有把 CPU 调用换成空语句或 primitive。

## 条件接口的精确边界

前置 `V293_exit_body_pre` 拥有 abstract operation、saved 的局部绑定与可写物理单元、shared 以及 caller frame。saved 的初始值可以不同，初始化后为0。

只有 `run=1` 时才要求 scheduler、enter、exit 的实际 Spec lookup。唯一残余语句级 Hoare 前提是 `scall int_switch nil`，且仅在运行、减后嵌套为0、调度锁为0、最高优先级不同于当前优先级时触发。其前置 counter 为 `Int.add c Int.one`，同时保留 ready/table/TCB、嵌套／锁、已发布目标指针、saved 物理单元及 caller 绑定。

完整接口为了直接复用调度桥，仍统一要求 ready/table 的关系与数值边界，即使不运行也如此。另一个稳定接口 `V293_OSIntExit_not_running_body` 消除了不运行路径的这些不必要要求：它只需运行字节界限、`run<>1`、shared 的 LocalInv 蕴含，完全不要求 callee lookup 或中段 Hoare 证明。探针 `FBno_lookup_body` 将整个 Spec 实例化为 `fun _ => None`，仍证明完整原 body；不是只证明 lookup 输入缺失。

## 先规定对照，再实现

本步协议及其哈希先于新证明冻结在 `audit/logs/stage188-interrupt-full-body/protocol.json`、`protocol-identity.json`。探针独立构造完整物理堆，仅导入生产证明／见证，不导入 audit probe。

| 对照 | 保持不变 | 可检查结果及限度 |
| --- | --- | --- |
| running=0/1/2/255 | 同一全局／局部环境、ready/table/TCB、current、counter、nest、lock、saved 与抽象状态 | 真实表达式只有1为真，其余为假；另证类型为 Tint32，16号块外每个字节保持。不是只比名称或 domain |
| saved=1/0 | 环境与其他资源，running 固定为0 | 两种正确完整入口均非空；在同一个 saved=1 堆上，错误宣称 saved=0 由真实 Tint32 load 冲突排除，15号块外字节保持 |
| 所有 lookup 缺失 | 完整原 AST，非运行条件与资源 | `FBno_lookup_body` 仍给出完整 body 的 InfRules；不声称运行路径可以删除 lookup |
| 完整入口与已清零入口 | 原资源布局 | 非空物理见证；两份独立快照不冒充实际 call/body/return trace |

fixture 为单 idle 任务、空 LocalInv；它不能代替生产 ISR／LocalInv 不变式。saved 的读取对照明确使用 `Vint32`，不把任意 `val` 都当作有效 Tint32 load。

## 复核入口

```bash
python3 -m unittest discover -s tests -p 'test_interrupt_full_body.py' -v
make build COQBIN=/data/home/lucentzhou/.opam/default/bin/
```

证据目录保存逐次编译的输入快照及所有失败日志、稳定编译身份、逐根 Print Assumptions、两入口递归 coqchk、源身份复查、两轮全量测试及旧失败有序 ID 对照。构建、project audit、make audit、whitespace 结果分别保留，不通过删除旧失败来制造全绿。检查点总结果在同目录 `verification.json`，文件身份由 `checkpoint-evidence-manifest.json` 固定。

## 下一步与最终目标

**完整 body 的条件 Hoare 证明，不等于完整函数环境，更不等于源码级 GOOD_OS。** 仍须纵向接入：

1. 原函数声明的 saved 真实分配及 `BuildPreI/BuildRetI`、`WFFunEnv`，将当前已分配局部入口接入函数 builder。
2. 固定 owner／空逻辑参数的临界契约不能泛化为同一生产 Spec 对所有任务有效；生产 enter/exit 契约及实现尚未闭合。
3. 实际 `OSIntCtxSw` 的实现与后置资源、生产 ISR/LocalInv、初始化与完整全局环境。
4. 全交错 simulation、同程序 K1–K4 回归及顶层源码级 `GOOD_OS`。

六阶段覆盖保持 `94/1/1/1/1/0`；不凭新增文件提高覆盖。uCOS3 尚未开始，必须在 uCOS2 整核目标真正完成后再按老师要求推进。总目标 active，没有提交或推送。历史检查点原文与冻结证据均保留。
