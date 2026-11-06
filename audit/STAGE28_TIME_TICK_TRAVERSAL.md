# 阶段28：真实 OSTimeTick 的零延时节点遍历

## 本次边界

固定函数 `os_core.c:937–1008`；源身份 `74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da`，配置后函数体 SHA256 `6103dfdd986ce129a03e1b8919997bea850989041632905f3d0ee0962ae1d251`。实现前冻结10805项已有文件、准确函数身份及单因素实验协议，见 `audit/logs/stage28-time-tick/`。

没有修改既有167个活动 Coq 源、C/config/port/framework/tactics、旧测试／门禁／证据／白名单。`_CoqProject` 仅末尾登记两个新生产模块；现169源＝66目标＋103框架／tactics。没有 Git 提交或推送。

## 实质连接

- `V293OSTimeTick.v` 表示完整配置后可执行语句，包括 cpu_sr 初始化、CPU hook、时间递增、OSRunning、整条 while 及非零延时／到期分支。不是已验证 C 前端，也还不是连接声明分配／返回的函数定义。
- `V293_tick_iteration_normalization` 和 `V293_tick_body_normalization` 检查分析端口宏到框架临界区 primitive 的转换；完整 body 的 hook 身份与 enter/exit 明确不同。
- `V293_tick_field_layout` 检查 TCB 大小56、Dly偏移44／Tint32、Next偏移20／Tcom_ptr410。
- **稳定执行接口 `V293_tick_zero_iteration_owned_execution`**：从局部指针完整权限和 Dly=0、Next 的实际空间所有权推出字段读取，构造真实局部 store，经既有 loststep 执行 enter→零延时判断→Next赋值→exit。局部指针 readback、节点字段、任意分离 `R` 均在**同一个最终 Mf**中返回；初始 IE／中断栈／临界区栈恢复，所有局部指针四字节范围之外的内存保持。
- 字面 probe 用编码内存构造入口，而非先假定执行。当前节点 `(81,8)`、不同后继 `(82,12)`，额外资源99，两个控制栈非空，定理对初始IE两个值均成立。不是初始化可达实例。

只给循环体中零延时分支执行信用；没有外层 guard、全链表遍历或中断交错信用。`Dly==0` 分支不触及到期处理／状态／位图；不能从“tick经过此节点”推出任务ready。

## 正反验证

`gate01` 实际8条命令全部符合预期：两个生产模块、旧空间fixture、新probe的4次编译；Next→Prev模型编译成功；对应生产证明拒绝；错误最终指针结论拒绝；最后独立 `coqchk` 对生产证明和新probe两模块检查通过。

- Next负控仅改 advance 中 field tag7→8；整份生产证明保持原文。错误在实际 assignment 执行连接处被拒绝，归一化／布局根本身仍可通过。
- 指针负控仅改字面定理的最终 load 结论；入口和完整 Proof 后缀保持，Read无法证明错误指针。
- 两者均 `downstream_credit=false`，不把早期拒绝当作其他机制有效。
- 生产4根：3根全局上下文闭合，执行根只依赖 `classic`、`functional_extensionality_dep`。字面3根：2根同样仅上述假设，1根闭合。没有新增假设。
- 复用了既有依赖产物，没有当前169源的source-only全仓干净构建声明。

开发时实际出现并保留了 import／保留notation `Ptr`／getmem状态推断／类型参数推断／单元素列表notation／hid作用域等编译失败与整源快照。只改新增实现和probe，没有改旧框架、规则或白名单。

## 回归状态

新增9项测试通过。旧998项运行357失败、1错误：以前347项诊断全部保留，新增11项诊断均明确定位 `_CoqProject` 的冻结hash或精确append断言，不改写旧快照。不能将原有347项都称为文件列表问题；完整差分见 `old-test-delta.json`。

清理后再次运行全量1007项，仍为357失败、1错误，按kind／id重数与本轮旧测试诊断完全一致；新增9项没有失败。`git diff --check` 通过。最终输入／历史文件身份与清理核对另存 `audit/logs/stage28-time-tick/final-report.json`；这不是全仓测试通过的声明。

范围和冻结C只读核对通过。默认 `make audit` 仍exit2：`stale function evidence input identity`；未运行重绑旧证据的check-functions。正式六门仍94／1／1／1／1／0，不因语句模型或有界执行定理而晋级。

## 清理与保留

按逐项大小／类别／SHA清单对**全部目标先验证，再首次删除**：361项（338个依赖软链接、23个一次性文件，实文件531514字节）及42个空目录。只删除隔离负控树和两个audit probe的编译产物；成功／失败源快照、日志、协议、所有源保留。两个新生产模块的10个可复用依赖产物保留，原835个依赖产物不改。

## 未完成与下一步

完整物理 Inv、初始化、正常无锁调度、其余 API／ISR、整核 GOOD_OS 及同程序K1–K4尚未闭合；uCOS3没有启动。下一步先连接同一循环体的“Dly非零、递减后仍非零”路径，再证明递减到零的等待结果／suspend／位图更新，不能用已写出的AST代替这些证明。

学习入口：[时钟中断如何跳过零延时任务](../docs/开发中/时钟中断如何跳过零延时任务.md)。
