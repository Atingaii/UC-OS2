# 第216步：同一不变量持有就绪语义与调度存储

## 本步解决什么

第215步已把退出路径的运行快照移入逻辑实参，但三函数契约所用的 storage Inv 主要保证字段类型和所有权，不能仅靠它推出就绪表与任务表一致。

本步建立数据所有权候选 `V293_ready_storage_inv`：在同一个不变量内连接已有的就绪/TCB 语义资源与调度存储，并证明原任务切换保持它。**尚未把第215步的 builders、函数体、统一 Spec 迁到这个新 Inv。** 不是完成了生产中断不变量或整核验证。

## 资源结构与稳定接口

生产文件：`certiucos/v293/proofs/V293ReadyStorageInvariant.v`。

- 第0层：`V293_ready_core ** (V293_dispatch_cell ** V293_storage cells)`。
- 其他层沿用共享不变量的空资源部分。
- 就绪表、优先级指针表、TCB 记录由 ready core 持有；附加 cells 不重复持有这些字节。
- `V293_ready_storage_good`：实际框架 `GoodI`，包括精确性、ISR/aux 现场稳定以及原切换所要求的资源性质。
- `V293_ready_storage_switch_resources`：新 `SWINVt` 与旧 ready `SWINVt` 加存储 frame 的双向断言等价。**不是 InfRules 的不变量替换定理**，不能据此直接宣告旧 Hoare 证明已迁移。
- `V293_ready_storage_switch_step`：构造真实原 `lpstep`、实际 pointer store，保持同一新不变量和任意外部 frame；当前指针以外的字节不变。并非把 store 后内存作为假设输入。
- `V293_ready_storage_selected`：从实际不变量提取就绪/任务对应关系、物理位图读取、最高就绪任务及优先级表指针读取。不依赖调用者提供选中结果。

## 非空入口与单因素消融

探针：`audit/probes/V293ReadyStorageInvariantProbe.v`。

| 证据 | 具体内容 | 不证明什么 |
| --- | --- | --- |
| `PPnonempty` | 复用冻结的实际调度 call/guard/counter 源码前缀，把同一个结果堆的资源关闭进新 Inv | 不是从启动初始化可达 |
| `PPactual_switch` | 在该实际结果堆执行原 switch，保持新 Inv 和私有 frame | 不声称缓存自动同步 |
| `PPbitmap_control` | 从同一个满足新 Inv 的堆，实际执行一次 ready 低字节写0；其他地址逐字节相等，控制字段 storage 与同一 TCB 所有权保留；新 ready 语义被排除 | 不是两个完整退出函数的对比执行，也不是 codec 早拒绝 |

固定夹具：就绪任务优先级4、当前等待任务优先级6；高优先级字节、当前缓存、counter、nest、lock 五个字段纳入附加 storage，dispatch 指针单独纳入同一 Inv。私有 saved/local 和 lookup 读取资源留在外部 frame。

消融保持地址布局、任务抽象表、TCB 内容、其他物理字节及控制字段类型资源不变，只把 ready 低字节改成类型合法的0。反例检查的是位图与实际任务表的语义对应，而不是错误编码。

## 必须保留的边界

1. **缓存关系仍开放。** 原 switch 只更新当前任务指针/抽象 curtid，不写 `OSPrioCur`。具体执行后缓存仍为6，目标任务优先级为4，新 Inv 仍成立。这明确证明 `GoodI` 和 typed storage 不足以推出 cache/current 一致。不得把它写成上游 C 的新漏洞；实际 C 前缀是否先做缓存 copy 是另一义务。
2. 新 Inv 对附加控制字段保证类型与完整权限，不保证运行值关系；dispatch 指针仅有类型/命名所有权，未证明它等于 `selected` 提取的最高就绪任务。switch 定理保证资源保持，不单独保证选择目标正确。本夹具未纳入 running 字段，lookup 表语义也未归入新 Inv。
3. ISR/aux 稳定只表示该数据断言不读取这些现场分量，不等于中断处理程序已保持 Inv，更不等于 `WFInt`。
4. 第215步统一 builders/Spec 仍用原 storage Inv；本步未完成所有函数、任意 ISR、初始化或生产 LocalInv 的连接。
5. 不改变 C/config/AST、framework、tactics、旧证明和旧失败证据；不增加新公理或跳过证明。

## 验证与复现

事前协议、全部失败和成功编译快照、源定位/哈希、逐根假设、递归 `coqchk`、构建、全量测试及清理结果保存在 `audit/logs/stage216-ready-storage-invariant/`。以该目录 `verification.json` 和只读 `recheck-checkpoint.py` 的实测结果为准。

本步共20个 Lemma/Theorem 根。五项 Python 回归只检查结构和证据身份，语义来自 Coq 内核，不声称语义 TDD。源核对重建两类授权修复，比较配置后的 `OSIntEnter`、`OSIntExit`、`OS_SchedNew`、`OS_Sched` 的准确源码哈希。

```bash
make build COQBIN=/data/home/lucentzhou/.opam/default/bin/ JOBS=2
python3 -B -m unittest discover -s tests -p test_ready_storage_invariant.py -v
python3 -B audit/logs/stage216-ready-storage-invariant/recheck-checkpoint.py
```

全量既有测试/审计并非全绿。保留第215步的423个 failure、1个 error 和顺序，`make audit` 的既有 stale evidence 问题及旧文件空白错误，不以删除旧失败制造通过。

## 目标与下一步

六门仍为 `94 / 1 / 1 / 1 / 1 / 0`，总目标 active；没有提交或推送。

下一步先把这个数据所有权候选与第215步实际 builders/完整退出契约衔接，单独处理调用、调度写入及缓存复制对新 Inv 的保持；再接 ISR/`WFInt` 与非空初始化。最终仍需同一固定配置程序的 `GOOD_OS` 和 K1–K4，完成后才进入 uCOS3。
