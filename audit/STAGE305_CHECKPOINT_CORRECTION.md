# 第305步复核入口勘误

生产证明、7个新结论的递归内核复核、4次稳定编译、6项新测试及完整2705项回归已完成。全回归仍为436失败、1错误，失败标识和顺序与第304步完全一致。

首次只读复核脚本存在文件名拼接错误：失败列表保存的是 `ablation-eoi-baseline.json`，脚本又附加 `.json`，因找不到 `ablation-eoi-baseline.json.json` 退出。它发生在证明、回归及逐项清理之后，不是 Coq 证明失败。

原始 `checkpoint.py`、失败日志、原 `verification.json` 和110项证据 manifest 全部原样保留。原 `verification.json` 的局部通过字段不能单独当作只读复核成功；最终状态请读取同目录 `verification-final.json`。

修正入口仅将该处改为按已含后缀的文件名读取，并检查后缀。其余全部验证条件逐字不变，仍校验原110项 manifest、全部旧输入、全部失败、缓存、源身份及证据。修正差异与源哈希先于复核冻结在 `checkpoint-correction.json`。

在仓库根目录运行：

```
PYTHONDONTWRITEBYTECODE=1 python3 -B audit/logs/stage305-builder-enter-resources/checkpoint-v2.py
```

本步的“只读复核通过”以 `corrected-checkpoint-01.json`、`corrected-checkpoint-02.json` 和 `verification-final.json` 为准。完整补充材料由 `completion-evidence-manifest.json` 绑定；原 manifest 不重写。

证明进展及范围仍见[第305步说明](STAGE305_BUILDER_ENTER_RESOURCES.md)。整核 `GOOD_OS`、完整 Exit、统一 WFInt、初始化及同程序 K1–K4 仍未完成；uCOS3未开始。当前目标 active，未提交或推送。
