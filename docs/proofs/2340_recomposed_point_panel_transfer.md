# 2340 - Recomposed point-plus-panel transfer

日期: 2026-10-01

结果: 计算上的重组通过 101 个 strip nodes。最大节点为 `j=-50`，
重组后的充分上界为 `706456.1761485817...`，低于冻结 pin
`2644542.8515`。这比 2339 的 `2644543.1669...` 更低，因为 2339
把旧完整 norm 与修复费用相加，重复计算了 2303 的 coefficient inflation。

这不是 producer GO。2340 仍是 artifact-grade transfer probe，没有把结果导入
Lean，也没有把精确修复后的 owner 交给 live consumer。

## 账目

`2303 point + panel` 是存储函数连续 strip norm 的基础上界。2340 保留这个
基础上界，乘以精确 `sigma=j/100` 与旧浮点 sigma 的权重转换因子，再加入：

- exact width-squared 与旧 binary64 radius 的几何差额；
- 2338 ideal coefficient 与 stored coefficient 的系数差额；
- 载波 `theta` 对一阶、二阶导数的贡献。

2340 不复用旧 coefficient inflation。脚本同时重算 ideal radius/coefficients 的
panel majorant 作为诊断字段，但最终上界仍以旧的连续 `point + panel` 基础证书
加显式函数差额构成。下一步需要把这一步写成逐项 directed-rounding 证明，不能
把诊断字段当成已完成的证明。

本轮修复了基础值合并的舍入边界：旧实现先用 binary64 做 `point + panel`，再把
结果提升到 Arb；这可能向内舍入。现在两个已存储的 binary64 操作数分别提升为
Arb 区间后再相加，并由测试检查结果不低于精确操作数和。这个修复只消除了一个
浮点实现缺口，不等于完成 point-sum、Euler--Maclaurin remainder 和 zero-count
条件的数学转移证明。

```text
+--------------------------------+-------------------------+
| Quantity                       | Reading                 |
+--------------------------------+-------------------------+
| Nodes                          | 101 / 101               |
| Maximum node                   | j = -50                 |
| Recomposed min-product upper  | 706456.1761485816...    |
| Frozen existing pin            | 2644542.8515            |
| Old inflation reused           | no                      |
| Owner transferred              | no                      |
| Producer GO / RH claim         | no / no                 |
+--------------------------------+-------------------------+
```

## 验证

原始计算使用 WSL resource runner。本轮修复后在 WSL 直接重算，九项 2340
自测通过，包含严格 pin 回读、导数常数、全节点加法、极端尺度和来源哈希。
结果文件由 Windows 工作树回读。验证摘要不将本轮直接执行冒称为资源调度执行。

运行时还检查 2303 的基础证书契约（baseline contract）：这里的契约是输入
必须满足的结构条件，不是数学证明。要求 corrected-owner 状态、zero-free
标签、连续范围 covered 标签及 -50..50 的完整 101 行。记录 2341 进一步给出
无需零点排除的单边面板界；2303 标签本身不能证明逐节点数值确实向外包围。

## 下一步

1. 把 2303 的 point+panel 连续范数上界拆成 directed node sum、panel EM remainder
   和 zero-count 条件，逐项证明 2340 的三角转移可以消费同一个基础上界。

2. 将 2340 的 101-node 上界接到现有 strip consumer，先保持 owner identity 与
   support-derived prime book 不变。完成标准是 Lean 只增加同一 owner 的明确前提，
   不引入 generic wrapper。

3. 再为完整 composed support 的 prime kernel 计算 signed repair charge。无权
   `< 3.602` 结果不能替代这个有符号、带核权重的预算。

证据:

- `scripts/routea_recomposed_point_panel_transfer_2340.py`
- `scripts/routea_recomposed_point_panel_transfer_selftest_2340.py`
- `results/2340_recomposed_point_panel_transfer.json`
- `build-logs/2340_recomposed_transfer.log`
- `build-logs/2340_recomposed_selftest.log`
