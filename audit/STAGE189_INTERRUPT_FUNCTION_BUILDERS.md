# 第189步：把原 OSIntExit 接到真实函数前置与返回构造器

## 先用容易理解的话说明

第188步相当于证明：“如果 `saved` 的存储单元已经准备好，原函数体满足这些条件，就会得到这些结果。”但调用函数时，不能让调用方先猜好函数内部局部变量的地址。

本步连接框架真实的 `BuildPreI/BuildRetI`：入口从函数声明产生一个存在旧值、存在地址的局部单元；证明内部再拆出地址和旧值，直接使用第188步完整函数体定理；返回时把局部单元、完整局部环境与外部资源重新装回真实返回条件。**这证明的是构造器断言与原函数体的连接，不是执行分配／释放的运行轨迹，也不是整个系统已经验证完成。**

## 稳定接口与证明链

生产文件：`certiucos/v293/proofs/V293OSIntExitBuilders.v`。

- `V293_OSIntExit_builder_contract`：原函数声明查询、真实 `BuildPreI/BuildRetI`、完整原 body 的条件连接接口。
- `V293_OSIntExit_not_running_builder_contract`：不运行路径的更弱接口，不要求任何 callee lookup 或 scheduler 的 ready/table 关系。
- `V293_exit_builder_identify`：从实际构造器等式识别前置／返回断言；原函数无参数，非空实参无法通过 `BuildPreI`。
- `V293_exit_builder_unpack/pack`：从局部资源中取出旧值与地址，并在返回时保留局部资源及完整 domain。

外部 `fpre/fpost` 满足 `GoodFunAsrt`，不夹带 `Alvarenv` 或 `A_notin_lenv`。调用者所需的不遮蔽事实由完整单局部 domain 与名称不等推出，不再把不适合外部函数断言的局部事实塞进外部规格。返回的 builder 断言保留 `EX old:val, LV saved @Tint32 |-> old` 和同一个完整局部 domain；没有用 `Atrue` 丢掉局部内存。

证明链为：实际构造器 → 单局部资源／domain → 存在旧值与地址 → 第188步完整原 body → 返回局部资源／domain → 实际返回构造器。`saved := 0`、真实 running 守卫、enter、中段、exit 和 return 沿用完整原 AST；没有引入整个 body 或整个调度中段的 Hoare 前提。

## 仍保留的条件，不隐藏成完成

运行分支仍显式要求同一 `Spec` 的 scheduler、enter、exit 查询，只有 `run=1` 时才需要这些查询。唯一语句级残余仍是启用且不同优先级分支的实际 `scall int_switch nil`，其前置计数已经为 `Int.add c Int.one`，并保留 saved、caller frame 和完整局部 domain。该残余对内部取出的所有 saved block 量化；公共接口不再预选 saved 地址或入口旧值。

主接口仍统一要求调度关系和数值边界；不运行专用接口取消了这些不必要的条件。探针 `BLno_lookup_builder` 将整个 `Spec` 设为 `fun _ => None`，连接实际构造器与完整原 body，不是仅检查“lookup 缺失”的输入。其返回 builder 隐藏了最终 saved 的具体值；初始化为0来自复用的 body 证明，不能把较弱的返回 builder 说成直接断言最终值为0。

这仍是**条件函数契约**，不是 `WFFunEnv`：不能从一个调用所需的固定 owner、空逻辑参数的临界契约，推断同一生产 Spec 对所有任务／参数的函数环境义务已经满足。

## 先规定协议，再构造独立对照

协议和身份在实现前冻结于 `audit/logs/stage189-interrupt-function-builders/protocol.json` 与 `protocol-identity.json`。独立探针 `audit/probes/V293OSIntExitBuildersProbe.v` 构造真实非空 ready/table/TCB、当前优先级、counter、嵌套、锁、running 与局部单元，不依赖其他 audit probe。

| 对照 | 保持不变 | 已证明及限度 |
| --- | --- | --- |
| saved 旧值为 `Vundef`／`Vint32 Int.one` | 同一环境、running=0、其他物理／抽象资源 | 两个实际 builder 入口都非空；15号块外每个字节相同。允许未初始化旧值，不把任意 val 当成有效 Tint32 load |
| saved 地址15／17 | 相同外部全局环境、shared、running=1、旧值 `Vundef`、单局部名称与类型 | 两个实际 builder 入口非空，真实 `&saved` 分别得到15／17；局部绑定及对应局部物理单元一起搬移，不声称整堆相同，也不是实际 allocator trace |
| 完整单局部 domain | 正确局部名称／类型，全部其余资源 | 两个地址的完整 domain 都合法；生产证明由 domain 推出所有相关名称不遮蔽 |
| 返回局部单元保留 | 同一完整物理 fixture，返回值为 `None` | `BLpost_nonempty` 证明返回 builder 非空；这是独立快照，不是该入口的一次执行结果或 final saved 值证明 |
| 非空实参／所有 lookup 缺失 | 原函数声明、完整原 AST | 非空实参被实际 builder 拒绝；非运行分支在全 None Spec 下仍有完整条件 Hoare 证明。两项不可互相替代 |

fixture 为单 idle 任务与空 LocalInv，不代表生产 ISR 不变式。断言非空不证明全部运行分支 callee 条件已经在同一生产 Spec 下实现。

## 复核与保留失败

```bash
python3 -m unittest discover -s tests -p 'test_interrupt_function_builders.py' -v
make build COQBIN=/data/home/lucentzhou/.opam/default/bin/
```

本步保留每次编译的输入快照、成功／失败日志和输入身份；稳定版本记录在 `stable-compiles.json`。逐根 `Print Assumptions` 与两入口递归 `coqchk` 检查本步15个生产引理／定理、31个探针引理／定理，共46根。最终结果以 `trust.json`、`verification.json` 和文件清单为准。调试时因泛化 `repeat split` 展开资源断言导致的单次耗时编译被停止，其输入与 `exit=-15` 原样保留；最终证明改为明确拆分外层合取，未降低证明条件。

新增5项回归；两轮全量运行均检查2108项，保留旧423失败／1错误的全部有序 ID。构建及 project audit、旧 stale-evidence 的 `make audit` 失败、旧 `inferules.v` 的 whitespace 失败分别记录；局部检查点通过不代表仓库全绿。旧源码、配置、AST、framework、tactics、测试与冻结证据保持；只前缀增加中文状态文档、追加生产项目入口及更新构建依赖。

## 下一步与最终目标

1. 接通同一个生产 Spec 下、对全部相关任务／参数有效的临界区接口，不能继续把固定 owner 示例当作生产端口。
2. 消除真实 `OSIntCtxSw` 残余，并保留实际调度与局部资源。
3. 接 `WFFunEnv`、实际分配／释放语义及完整函数环境、生产 ISR/LocalInv、初始化和全交错 simulation。
4. 完成同程序 K1–K4 与源码级 `GOOD_OS` 后，再开始老师要求的 uCOS3。

六门覆盖保持 `94/1/1/1/1/0`。总目标 active，uCOS3 未启动，未提交或推送；历史检查点原文不覆盖。
