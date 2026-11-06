# 第255步归档补充：保留失败，前向完成冻结

局部证明及测试结果不变：生产14根、probe 15根均通过实际 Coq 与递归 coqchk，新增6项回归通过；完整2440项测试仍427失败、1错误。整核 GOOD_OS 未完成。

第一次冻结检查发现一处归档时序错误：`checkpoint.py finalize` 的标准输出被重定向到本目录，清单对该仍在写入的日志取哈希后，退出时又追加了最后74字节。因此原 `checkpoint.py recheck` 真实失败。不是 Coq、源码或测试发生变化，亦不撤销或覆盖这个失败。

原 manifest、verification、失败日志和所有交付均保持原样。补充检查严格验证：原清单只有 `finalize-attempt01.log` 变化，原1158字节前缀哈希仍相同，追加内容必须精确等于那一行收尾输出。其余原清单项目逐字节不变。第二版清单冻结完整日志以及原失败证据，不删除不利结果或放宽数学检查。

当前复核入口：

```bash
python3 -B audit/logs/stage255-handoff-progsim/checkpoint-v2.py
```

当前清单为 `audit/logs/stage255-handoff-progsim/checkpoint-evidence-manifest-v2.json`；归档原因见同目录 `checkpoint-completion.json`。原入口仅用于重放已保留的第一次归档失败，不再作为当前成功复核入口。

本补充不修改原29根证明、所有假设检查、旧失败、覆盖计数、源代码或验收边界。一般暂停任务的后续模拟、完整中断返回、WFInt、初始化及 GOOD_OS 仍未闭合；uCOS3 未开始，未提交／推送。
