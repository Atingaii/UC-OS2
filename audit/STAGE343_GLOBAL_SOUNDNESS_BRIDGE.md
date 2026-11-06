# 第343步：保留原契约的全局soundness连接

## 本步解决什么

第342步已取得任务级模拟，但原顶层证明的递归依赖仍含超出允许集的Eqdep。本步只修复这条通用证明链，不增加内核行为假设，不改变固定源码或配置。

连接关系为：原WFAPI、WFInt、WFIFun及side_condition → 方法/任务模拟 → ProgSim → 执行轨迹包含 → 原框架GOOD_OS。稳定入口是`V293_verified_os'`和`V293_Soundness`。

**这是有前提的通用soundness，不是具体内核GOOD_OS。** 定理没有提供当前内核全部WFAPI/WFInt/WFIFun与规范初始化实例；它不能反向证明自己的前提。

## 实际修复

1. 初始化分区：在`V293InitializationPartition.v`中泛化状态，以普通归纳重证原init_partmo两项契约。initst与side_condition前提不变，因此不是OSInit执行证明。
2. 轨迹转换：在`V293TraceRefinement.v`中先泛化完整低层world，再普通归纳，重证原progsim_imply_eref及辅助契约。空轨迹、无事件步、有事件步和abort分支全部保留。
3. 全局连接：`V293GlobalSoundness.v`复用第342步完整规则soundness，在原中断/全局契约中替换有额外假设的依赖。原框架文件不改写。

9项原契约由Coq直接检查类型一致，不以字符串相似作为证明。18个根包含带撇号定理及探针，逐项检查传递假设，并递归coqchk。允许集仍仅为`Classical_Prop.classic`与`FunctionalExtensionality.functional_extensionality_dep`。

## 为什么不能只看编译通过

最初全局候选已编译且原契约检查通过，但四个上层根仍含Eqdep；`new-dependencies-01.log`保留这一失败。诊断发现init_goodis及轨迹star引理没有该问题，剩余问题在progsim_imply_eref_aux。修复后重新检查同七根，Eqdep出现次数从4变为0；失败记录未覆盖。

事前计划的四项单因素对照分别仅换回旧初始化分区、API模拟、中断模拟、轨迹转换；其余全局证明和定理前提保持不变。每项均先编译完成，再在最终Soundness假设闭包中被原信任门拒绝。这证明四条依赖在本全局连接中均有独立作用，不代表具体中断/初始化实现已验证。

## 原有缺口与验证边界

- 当前程序的完整WFInt仍需真实ISR在**未过滤**的BuildintPre/BuildintRet下成立，不能用quiet子集冒充。
- 初始化分区只消解给定initst；规范初始化表来源、OSInit完整执行/可达性仍开放。
- 源码身份沿用冻结第337步，不重跑源码前端；不是经验证C前端，ADR0005临界归一化和两个CPU hook仍为缺口。
- 不把此通用连接登记为任一函数full_target_linked，不覆盖旧证据或旧测试。
- 同程序K1–K4及uCOS3仍未完成，总目标保持active。

## 检查与复现

生产文件分别重复编译两轮，探针检查9项原类型；信任检查逐根记录于`assumptions-by-root.json`。四个交换对照见`ablation.json`；源文件/契约/旧失败快照均保留。

```sh
PYTHONDONTWRITEBYTECODE=1 python3 -B -m unittest discover -s tests -p test_global_soundness_bridge.py -v
make build JOBS=1 COQBIN=/data/home/lucentzhou/.opam/default/bin/
```

全部实测结果及两轮全量回归见`audit/logs/stage343-global-soundness-bridge/verification.json`。历史基线是2997项、447失败、1错误；任何旧失败仍意味着全量未通过，不因本步局部证明通过而变绿。全量失败身份/顺序逐项比较，不豁免新增失败。旧总体审计过期身份及原六处空白问题继续保留。

最终两轮实测：3005项、447失败、1错误，旧失败/错误身份及顺序完全一致，无新增；全量仍未通过。新增8项两轮通过；构建和项目审计通过，make audit与git diff --check仍为原失败。清理数量与保留对象以verification.json为准。
