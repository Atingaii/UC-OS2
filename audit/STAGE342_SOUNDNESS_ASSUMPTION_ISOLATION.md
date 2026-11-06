# 第342步：不放宽信任边界，恢复完整时间接口任务模拟

## 问题与修复

第341步的强WFAPI已通过，但完整TaskSim链额外依赖`Eqdep.Eq_rect_eq.eq_rect_eq`。
本步保留旧结果为失败对照，不改框架、不改旧证据、不增加允许公理。

对全部40条规则的实际依赖逐项检查发现，三条调用规则共享的
`call_ignore_exprlist_sim`在固定内存索引上使用依赖归纳，带入额外Eqdep。
其余37条规则未出现该额外依赖。只把该处改成对泛化内存的普通归纳，
重证原三条调用规则，再连接完整40条规则、内部函数环境与API方法模拟。
`RuleSound`本身的原归纳方式不变；没有删掉调用规则或缩小语句子集。

新增文件：
- `certiucos/v293/proofs/V293CallSoundness.v`：原契约的调用规则与泛化归纳。
- `certiucos/v293/proofs/V293Soundness.v`：完整规则及函数/API语义桥。
- `certiucos/v293/proofs/V293TimeTaskSimulation.v`：原生成时间函数和强就绪/时钟不变量的通用任务模拟。
- `audit/probes/V293SoundnessBridgeProbe.v`：实际OSSchedNew内部映射、非空联合资源客户端及11项原契约检查。

## 如何判断不是“绕过检查”

1. 单因素是替换证明桥；源码、规格、不变量、TaskSim定义和允许集保持。
2. 原辅助引理、RuleSound、时间TaskSim及非空客户端重新打印依赖，仍出现Eqdep，保留红色对照。
3. 11项Coq定理直接取旧定理的完整类型，由新证明项填入；不是人工比较简化后的文字声明。
4. 不能以辅助引理单独通过代替整链；全部22个新增证明根分别打印依赖，并递归运行coqchk。
5. 允许集仍仅为`Classical_Prop.classic`与`FunctionalExtensionality.functional_extensionality_dep`。

实测命令、失败尝试、冻结输入、每根假设及完整回归保存在
`audit/logs/stage342-soundness-assumption-isolation/`。
数学通过与工程回归分别记录，旧第341步信任失败测试不会被改成绿色。

## 得到了什么，还缺什么

新的通用TaskSim保留原先全部结构条件，内部WFFuncsSim前提在非空实例中由实际
OSSchedNew环境证明，不使用空内部映射；中断映射仍只有显式结构义务。
入口资源是客户端局部与共享内核资源的真实join，不把成功执行作为前提。
这是任意任务级模拟关系，不只是某一次存在的有限执行。

但是它不是ProgSim，不是GOOD_OS，不是OSInit可达性。
旧非空实例中的未分配优先级槽别名不是规范初始化表。
实际ISR函数体的WFInt、规范初始化和全局程序连接还需要证明。
沿用第337步冻结源码对应，未声称本步新鲜重放；不是经验证C前端，
ADR0005临界归一化边界及两个CPU hook开放义务保持。
同程序K1–K4和uCOS3仍未完成，总目标保持active。

下一条主线是把实际ISR及规范初始化接到同一全局程序，不能把此局部任务模拟冒充整核完成。
