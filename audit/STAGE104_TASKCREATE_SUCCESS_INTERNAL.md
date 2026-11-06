# 第104步：成功路径接入真实函数前后置构造器

## 要解决的缺口

第103步已证明原始完整 `OSTaskCreateExt` 函数体的一条受限成功路径，但其断言尚不是框架实际生成的函数入口／出口。仅证明语句体，不代表函数调用边界已经接好。本步把同一函数体接入真实 `BuildPreI / BuildRetI`，不新增或改写 C／AST。

稳定接口为 `V293_OSTaskCreateExt_success_internal_contract`，位于 `certiucos/v293/proofs/V293TaskCreateSuccessInternal.v`。编译和独立探针状态以本步冻结报告为准；没有冻结报告时不得当作已验收。

## 资源如何交接

1. 复用第100步真实声明布局：九个形参、三个局部变量 `psp / err / cpu_sr`，而非手写简化调用者环境。
2. 从精确声明域推出91–99这些全局标识符没有局部遮蔽；函数规格本身不携带调用者局部绑定或声明域。
3. 初始优先级槽为NULL，只保留一份可写槽资源；第103步原始前缀将其写成实际预留指针，再交给同一完整snapshot的TCB前置。
4. 栈调用、TCB调用和返回0均复用既有纵向证明。整个callee后置完整保留，不能只抽取“返回0”而丢弃链表／就绪表资源。
5. 返回时交还12个声明资源和精确声明域，并保留嵌套计数字节、只读OSRunning字节、全局绑定和完整callee后置。

## 独立检查与对照

`audit/probes/V293TaskCreateSuccessInternalProbe.v` 用冻结的真实字面内存布局构造精确12项局部环境，检查实际builder、入口满足性和同一有限规格表下的TCB函数体。`present` 同时量化旧任务链表为空／非空两种情况。它复用既有源码模型，不是独立 C 翻译器，也不是整个调用链的small-step执行轨迹。

控制只替换“期望的返回局部声明单元顺序”：正确组为psp、err、cpu，交换组为err、psp、cpu；每个变量仍附着原类型。实际 `buildq`、`BuildRetI`、程序和其余证明不变。两组先完成相同实际builder和断言类型检查，最后才比较精确布局等式。

交换后的分离断言在语义上可以交换还原。因此错误组只说明**不等于框架的规范声明布局**，不能声称它是不可满足断言、运行时错误或语义无效后置。初次两组共有的existential语法错误不计为对照成功；共同修复语法后重新观测，原始失败完整保留。

## 边界与下一步

仍要求入口IE=false、合法优先级、task上下文、空优先级槽、非空空闲TCB链表、OSRunning=0。栈初始化和两个CPU Hook仍是三个外部契约。探针中的NULL栈返回只是类型／连接见证，不是有效初始化栈或端口栈算法。

本步不是全部任务创建分支、活动调度、完整 `WFIFun`、全局不变量／可达性、初始化、源码级 `GOOD_OS` 或同程序K1–K4。六门仍为94/1/1/1/1/0；uCOS3尚未开始，总目标保持active。

后续应补齐任务创建的剩余原始分支及活动调度连接，再归并到同一函数规格，向 `WFIFun`、全局不变量和初始化推进，而不是继续把局部检查计为整核覆盖。Git保持原HEAD，本步不提交／推送。

所有尝试、单因素方案及原始输出均在 `audit/logs/stage104-taskcreate-success-internal/`；验收后以其中 `final-report.json` 和 `final-evidence-manifest.json` 为准。已有失败不得删除或重写成通过。

## 复核入口

正式证明已经纳入 `_CoqProject`，可运行增量构建与新增结构回归：

```bash
make -f Makefile.coq -j2 COQC=/data/home/lucentzhou/.opam/default/bin/coqc
PYTHONDONTWRITEBYTECODE=1 python3 -B -m unittest discover -s tests -p test_taskcreate_success_internal.py -v
```

若重跑独立探针，应按依赖顺序编译 `V293TCBSuccessInternalProbe.v`、`V293TaskCreateTCBCallProbe.v`，最后编译 `V293TaskCreateSuccessInternalProbe.v`，均使用 `coqc -q -R . CertiOS`。这会重新生成临时探针产品；本步验收后只清理这些产品，不删除探针源码或失败快照。

冻结后可运行 `PYTHONDONTWRITEBYTECODE=1 python3 -B audit/logs/stage104-taskcreate-success-internal/verify-readonly.py` 检查文件身份及已留存的验证记录。它不代替重新执行 Coq；本轮真正执行的编译、`Print Assumptions`、全活动模块 `coqchk`、构建与全量测试命令均单独留存。日志目录里的执行／冻结脚本使用不可覆盖标签，不应直接覆盖既有结果。

## 本轮执行结果

| 检查 | 实际结果 |
| --- | --- |
| 正式证明／独立探针 | `proof30`／`probe05` 编译通过；共35次正式／探针尝试，失败和中断记录全部保留 |
| 假设闭包 | 34个新根；只出现既有 `Classical_Prop.classic` 和 `functional_extensionality_dep` |
| `coqchk` | 270个活动模块和3个额外探针全部通过 |
| 增量构建 | 清理前后均通过、无待构建项；不是冷构建结果 |
| 新结构测试 | 6/6通过，不代替Coq检查 |
| 全量测试 | 清理前后均1522项、423失败、1错误；424个旧诊断ID逐项一致，无新增诊断 |
| 默认审计 | 仍因旧函数证据身份过期失败；不改写覆盖证据强行通过 |
| 空白检查 | 仍仅有旧 `inferules.v` 581–586六行问题 |
| 清理 | 删除41个本轮一次性文件，共5,229,121字节；原缓存已恢复，正式1350个产品和旧1345个产品保留 |

一次过早启动的只读验收因全量测试尚未结束、缺少结果JSON而失败，记录在 `verification-early.json`，不计为通过。后续必须等全部材料就绪再运行完整验收／冻结；不能删除缺失检查或降低门槛。
