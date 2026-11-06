# 第281步：目标指针赋值接入原 TaskSim

## 本步推进的源码语句

固定版本仍为 uC/OS-II V2.93.01，源码身份及配置没有变化。`os_core.c:709`：

```c
OSTCBHighRdy = OSTCBPrioTbl[OSPrioHighRdy];
```

上一检查点从紧随其后的优先级比较起证明 TaskSim。本步把同一条模拟链前推到目标指针赋值前，不新增内核功能、修改框架或改写旧证明。

## 公开接口和依据

生产模块 `certiucos/v293/proofs/V293ExitTargetTaskSim.v` 仅暴露一个上层接口 `V293_exit_target_TaskSim`，三个内部引理服务它。

- 输入为名字绑定、抽象任务映射、所选任务优先级、最高 ready 条件及空间所有权。公开前提不要求已经证明执行、store、数组 eval 或 TaskSim。
- `V293_target_owned_pointer` 将同一 SWINVt 中的任务映射与给定抽象任务映射对齐，用13项优先级表和优先级表示单射性推导真实目标指针读取。
- 从目标单元的所有权构造写入，保存任意32位计数值。每个表达式与赋值小步在任意兼容 frame 上衔接原 TaskSim，而非用一次完整执行轨迹替代所有 frame 义务。
- 写入后复用第280步比较/计数、279步 handoff 和278步 switch 的同一后缀。

## 同一真实调用和单因素对照

独立探针 `audit/probes/V293ExitTargetTaskSimProbe.v` 从原完整分配调用到达赋值前切点。helper 的 `Call` 到其返回 SKIP，再沿 continuation 到赋值；不从赋值后的结果反推前驱。实际堆上的目标仍为 `Waiting`，优先级选择为4，旧缓存为6，计数为 `Int.mone`。

`ETpartition` 在这个实际堆上分离任务与外部资源，建立本步 TaskSim；`ETnonvacuous` 给出新鲜分配块存在性。saved(bs) 私有，saved98 与 RCframe 外部。

`ETactual_target_ablation` 在同一个前驱堆 M 上对照：正常赋值到比较入口时目标为 `Ready`；仅将这次赋值替为 SKIP 时目标仍为 `Waiting`。其余前驱、环境、continuation 完全不变。两边计数仍为 `Int.mone`，写入块93以外所有字节不变。这是**局部后缀消融**，并未声称删除赋值后的完整程序最终行为已经验证。

## 审查边界与未完成项

**不是完整调用入口 TaskSim；GOOD_OS 未闭合，同程序 K1–K4 未闭合，uCOS3 未开始。**

- helper/外层 guard 的逐步模拟及等分支完整资源返回仍待连接；本步仅覆盖最高优先级与旧缓存不同的分支。
- 使用既有弱 storage 布局，没有证明列表置换下 Inv 的等价；不以它替代强 current。不变的 cache=4、旧任务 blocked 强 guard 缺口保留。
- si=nil、ISR 全清、空 LINV、有限 SKIP caller、已有目标 pending、ADR-0010 接受的调用点抽象均是既有边界；不宣称任意中断交错、初始化可达性或旧任务全局切回。
- 第280步及以前的冻结输入和失败日志不修改。本步失败编译及当时源码快照保留；不能删除负面结果制造全仓通过。

## 可复验材料

`audit/logs/stage281-target-tasksim/` 包含事前 `protocol.json`、源码定位与身份、逐次编译快照、两次稳定编译、逐根假设与递归 `coqchk`、完整测试失败身份差分、清理清单及只读检查点。

以最终 `verification.json` 的实测结果为准；`checkpoint.py` 只核查该局部交付，不表示整核已完成。下一步应继续把 TaskSim 向真实 helper 调用和外层 guard 前推，而不是累计孤立模型数量。
