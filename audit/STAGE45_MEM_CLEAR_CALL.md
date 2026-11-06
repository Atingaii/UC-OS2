# 第45步：OS_MemClr 的双参数真实调用与释放

## 本步解决什么

第43步只有参数已分配的原生循环，第44步把四个零字节连接到规范空指针。本步新增稳定接口 `V293_OS_MemClr_call_return`：实际实参求值 → 两个新鲜参数对象 → 两次实际 store → 原生 while → void return → 两次实际 free → 恢复 caller。

参数声明顺序是 `pdest, size`；框架先按源码顺序求值，再用反转列表分配 `size, pdest`。不是把调用者变量直接当作被调函数的参数对象；不假设 store／free 已成功。

## 独立入口与已填结果

完整字面 AST 与锁定 C 对照；可构造的有限内存不导入旧 probe。目标块82的偏移5–8为255／Vundef／7／1；两侧偏移4／9是17／29。调用者自己的指针和计数在块71／73，临时参数用原来未分配的块81／83。另有块99的123。

| 检查对象 | 调用前 | 循环结束、释放前 Ms | 实际返回后同一 Mf |
| --- | --- | --- | --- |
| 目标4字节 | 255、未初始化、7、1 | 全零；可建立 typed null 所有权 | 指针 load 为 Vnull |
| callee 的 pdest | 尚未分配 | 指向偏移9 | 全部4字节缺失 |
| callee 的 size | 尚未分配 | 0 | 全部2字节缺失 |
| caller 保存的指针 | 指向偏移5 | 仍指向偏移5 | 仍指向偏移5 |
| caller 保存的长度 | 4 | 4 | 4 |
| 同块两侧保护字节 | 17、29 | 17、29 | 17、29 |
| 其他资源 | 123 | 123 | 123 |

`CallConcreteExecution` 在同一返回 Mf 检查6项 load及全部6个已释放字节；总函数 `CallProgram` 与无入口前提的 `CallConcreteInstance` 排除程序映射前提不可满足的空证明。

## 实际验证

- 重新物化授权修复后的固定 C，用 clang 预处理／AST 复核全部94个函数身份及准确 OS_MemClr 函数体；C未改。
- 全部188个既有活动 Coq 源、旧测试和旧 audit 证据逐文件哈希不变。只新增一个生产模块，登记后189＝86目标＋103框架／tactics。
- 正式 `make build` 通过，复用原940个生产产物，耗时约0.85秒；**不是189源 source-only 冷构建**。
- 47个信任根及3模块 `coqchk` 实际通过，包括框架顶层、新生产模块和独立 probe。新接口只依赖既有 classic／dependent funext；未新增公理或占位证明。
- 初次 coqchk 因 probe 的逻辑库名映射不一致而失败；仅修正编译命令的 `-R`，源码／Proof 不变。原失败 `trust.json`／`coqchk.log` 保留；有效结果为 `trust02.json`。
- 三项前瞻单因素负控保留全部 Proof：目标错误地仍为非空、caller 指针错误地推进到9、已释放参数错误地仍可读，分别在预登记行153／154／164被拒绝。**只授对应最终连接拒绝信用，不授下游 safety 信用。**
- 全量测试 1153 项，391 failures／1 error；旧 392 项失败诊断全部保留，本轮新增7项测试均通过。 默认 `make audit` 仍exit2：`stale function evidence input identity`；不改旧证据或弱化门槛。正式六门仍94／1／1／1／1／0。

## 边界与下一步

通用接口要求 Vptr 参数、计数0–65535和不回绕的有效字节范围；不覆盖 NULL＋0 的完整调用。只是无交错的存在性 cstepstar，不是所有执行 safety。任意 R 一直按最终 callee 环境解释；返回后只暴露两个参数块外的内存相等，不把环境敏感断言偷搬回 caller。独立有限资源没有环境依赖，因此能据此读回。

不是13项整张指针表、完整TCB表／链、OSInit／OSStart可达性或运行共享不变式；GOOD_OS、同程序K1–K4和完整task／ISR仍开放，uCOS3未启动，无commit／push。下一步把这个真实调用接入固定 `OS_InitTCBList` 的两次清零，再建立 TCBNext 与空闲链。

本轮只清理已经完整登记并逐项复核的一次性编译目录、临时 C 物化目录和 probe 产物；保留所有旧缓存、945个可复用生产产物、probe源码及所有成功／失败日志。最终清单以 `audit/logs/stage45-mem-clear-call/cleanup.json` 和 `final-report.json` 为准。

## 入口

- 生产证明：`certiucos/v293/proofs/V293MemClrCall.v`
- 独立入口：`audit/probes/V293MemClrCallProbe.v`
- 前瞻协议／负控：`audit/logs/stage45-mem-clear-call/protocol.json`、`control-plan.json`
- 当前有效检查：`build.json`、`probe-mapped.json`、`trust02.json`、`control-results.json`
- 单元回归：`tests/test_mem_clear_call.py`
