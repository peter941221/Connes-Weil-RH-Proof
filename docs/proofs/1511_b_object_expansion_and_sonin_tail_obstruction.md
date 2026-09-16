# 1511 — B 对象展开与 Sonin 尾部障碍核对

日期：2026-09-16。

状态：PAPER/FORMAL RECON。本文只整理已提交定义和定理，未加入新的
Lean 假设，也不宣称 RH。消费者是健康 `CompactLog` 上的 B5 同 owner
G8 readback。

## 1. 固定对象

以下记号均是提交代码中的定义：

```text
J   = sourceInclusion lambda
C   = rootConvolution owner
D   = detectorOperator owner
S   = finiteEulerPulledObliqueShear lambda family
W_n = fullBoundaryPositiveOperator owner.sourceTest
      (cutoffLower owner.sourceTest n) (cutoffUpper owner.sourceTest n)
G   = g8AdjointShearGram owner lambda family
```

由 `C1G8AdjointShearGram.lean` 中的定义，

```text
G = (I + S†)† D (I + S†) = (I + S) D (I + S†).
```

因此 endpoint 的极限对象确实是

```text
B_complex = ordinaryTraceAlong sourceBasis (J† C† G C J).
```

这里的 `B` 是复数迹；readback 只消费 `B_complex.re`。

## 2. 每个有限截断的精确四项恒等式

令

```text
t_n = re (ordinaryTraceAlong sourceBasis
            (g8SourceCutoffPairData owner lambda family
               globalBasis sourceBasis n).traceProduct)
```

展开 `G` 后，四个实数通道为

```text
b_n = re Tr(J† W_n† D W_n J)
x_n = re Tr(J† W_n† S D W_n J)
x'_n = re Tr(J† W_n† D S† W_n J)
l_n = re Tr(J† W_n† S D S† W_n J).
```

因为第二个交叉算子是第一个的 adjoint，
`re Tr(x'_n) = re Tr(x_n)`，故

```text
(B1)  t_n = b_n + 2*x_n + l_n.
```

供应者：

* `g8SourceCutoffPairData_traceProduct_eq_fourChannelLedger`：四个算子的
  复数级相等；
* `g8SourceCutoffPairData_ordinaryTrace_eq_fourChannelLedger`：沿同一
  `sourceBasis` 的迹可加；
* `g8SourceCutoffCross_trace_add_adjointCross_eq_two_re`：交叉项合并为
  `2 * re`；
* `g8EndpointSourceCutoffPairData_traceProduct_eq`：确认该有限截断正是
  G8 readback 所消费的 `J† W_n† G W_n J`，而不是 metric-coframe 的另一个
  迹对象。

这一步没有丢掉 `S`，也没有把 `C(Ju)` 错写成 source-carrier 向量。

同一恒等式现已由 `Dev/C1G8R5AggregateExpansion.lean` 中的
`g8EndpointSourceCutoffLimitOperator_eq_fourTerms` 在 Lean 中逐算子证明，
其配对审计叶只打印 `[propext, Classical.choice, Quot.sound]`。这只是
对象层代数闭合，不增加任何尾部估计或算术识别假设。

## 3. 极限和全部误差项

若记

```text
X = limit of x_n,
L = limit of l_n,
B = B_complex.re,
```

则完整的误差恒等式是

```text
(B2)  t_n - rho1_n - rho2_n - rho3_n - rho4_n
      = B + 2*X + L,
```

其中

```text
rho1_n = t_n - (b_n + 2*x_n + l_n)                  = 0,
rho2_n = 2*(x_n - X)                                 -> 0,
rho3_n = l_n - L                                     -> 0,
rho4_n = b_n - B                                     -> 0  (给定核心平方和),
rho5   = (B + 2*X + L) - qw(owner.sourceTest)        = 0  (仍需证明).
```

供应者和边界：

| 项 | 供应者 | 状态 |
|---|---|---|
| `rho1` | `g8SourceCutoffPairData_ordinaryTrace_eq_fourChannelLedger` 与交叉 adjoint 定理 | FORMAL 恒等式 |
| `rho2` | `tendsto_ordinaryTraceAlong_g8MetricLeakageSourceCross_actualCutoff`，以及 1481 的 adjoint 配对 | FORMAL |
| `rho3` | `tendsto_ordinaryTraceAlong_g8MetricLeakageSourceCross_actualCutoff` 的同 owner signed remainder 版本（1480） | FORMAL |
| `rho4` | `tendsto_g8EndpointSourceCutoffPairData_trace_of_survivorCore`（1502） | 依赖核心平方和 `(*)` |
| `rho5` | 需要新的对象级 Euler/阿基米德/P2 识别定理 | OPEN |

因此只要前三个极限以及 `rho4` 存在，readback 的唯一实质条件就是

```text
(B3)  B + 2*X + L = qw(owner.sourceTest).
```

这是 1504 的 `g8R5_readbackTendsto_iff_aggregateLimit_eq_qw` 所形式化的
同 owner iff。

## 4. 逐项对照素数幂、阿基米德项和 P2 余项

独立的算术对象是

```text
A_arith = arithmeticOperator owner family
        = eulerLogWeightedGlobalPairTraceOperatorSum owner family.terms.
```

现有定理给出

```text
Tr(projectionResponse owner lambda family)
  = sum_{pm in family.terms} owner.finitePrimeTerm (pm.1 ^ pm.2)
    + Tr(sameObjectResidual owner lambda family).
```

供应者是 `ordinaryTraceAlong_projectionResponse_eq_finitePrimeSum_add_residual`，
其素数幂逐项读回由
`ordinaryTraceAlong_eulerLogWeightedGlobalPairTraceOperatorSum_eq_finitePrimeTerm_pow_sum`
提供；canonical family 再由
`ordinaryTraceAlong_g8CanonicalFamilyVisibleBoundary_eq_selectedSupport_sum`
换成 owner 的 `globalPrimeIndexSet`。

`sameObjectResidual` 的结构恒等式为

```text
sameObjectResidual
  = (D ∘L prolateDifference - A_arith)
    - D ∘L compressionDifference.
```

这里已经明确出现三类内容：

1. `A_arith`：有限可见素数幂的算术和；
2. `D ∘L prolateDifference` 与 `D ∘L compressionDifference`：阿基米德/投影
   响应的同 owner 残差；
3. `sourceActualBandFiniteEulerRemainderResponse`：P2 余项的实际 source
   响应，满足 `sourceBandGramResponse = soninFirstJet - remainder`。

但是，当前没有定理把

```text
Tr(J† C† G C J)
```

逐项改写成上面这个 `projectionResponse` 的算术分解。尤其不能把已有的
`sourceCompression(G) = metricCoframe† D metricCoframe` 公式应用到
`C(Ju)`：它要求输入在 source compression 的右侧，实际输入是先经 ambient
卷积 `C`，类型和 owner 都不同。故“素数幂 + 阿基米德 + P2”目前只能写成
两个并列对象的精确分解，不能声称它们已经相等。这个未证明的桥正是
`rho5`，不是迹收敛问题。

## 5. 对核心尾部平方和的硬性检查

核心门槛为

```text
(*)  Summable i,
       ‖(J† C J)(sourceBasis i)‖².
```

已有三条事实应分开解释：

* 1488/1489 在 ambient `finiteSCarrier` 上构造了相隔平移的正交轨道，且
  未压缩 leakage 输出范数最终被正下界控制；所以 ambient leakage 算子不是
  Hilbert--Schmidt。这是有效的反例型障碍，但输入不在实际 Sonin carrier
  的命名基底上。
* 1490 证明同一轨道经 `sourceSoninProjection` 后范数趋于零。因而不能把
  ambient 轨道正规化后直接搬到 Sonin carrier；该投影会消灭所需的下界。
* Sonin carrier 是 radial half-line 条件与 Hardy--Titchmarsh image
  half-line 条件的交集，不具备普通平移不变性。故目前没有已证明的
  “实际 Sonin 载体中的不衰减正交序列”；1490 只排除了最直接的 ambient
  轨道迁移。

结论：(*) 仍然是 OPEN，但当前证据不是“已找到 Sonin 反例”，而是
“ambient 反例不能转移，真正的 Sonin 尾部需要新的构造或估计”。

## 6. 相位估计的真实入口和停止条件

提交代码中 Hardy--Titchmarsh 变换满足

```text
F(HT u)(xi) = m(xi) * F(u)(-xi),
m(xi) = Gamma_R(1/2 - 2*pi*i*xi) /
         Gamma_R(1/2 + 2*pi*i*xi),
|m(xi)| = 1,
m(-xi) = conjugate(m(xi)).
```

这些定理只给出 unit modulus、连续性、反射共轭和 involution。它们还没有
给出 `arg m` 的导数界、二阶差分界或随 `|xi|` 增长的相位余项界。因此从
当前 Mathlib/提交接口不能推出(*) 的定量尾部界。

不过，相位的第一导数可以在纸面上精确定位。由已提交的
`logDeriv_GammaR_eq_log_pi_add_digamma`，若 `m(xi) = exp(i theta(xi))` 在一
个连续分支上，则

```text
m'(xi) / m(xi)
  = -2*pi*i * ( Re digamma(1/4 - pi*i*xi) - log pi ),
theta'(xi)
  = -2*pi * ( Re digamma(1/4 - pi*i*xi) - log pi ).
```

这说明真正需要的是 digamma 的定量渐近，而不是 multiplier 的模长；形式
上还应有 `theta'(xi) = -2*pi*log|xi| + O(1/xi^2)`（`|xi|` 足够大时）。
该渐近及其误差常数目前既没有在 Mathlib 中出现，也没有在本项目中证明，
所以这里只把它登记为下一块的纸面目标，不把它当作已得估计。

可接受的下一块必须先证明一个明确的相位输入，例如在某个 `R` 以上

```text
|arg m(xi) - phase_model(xi)| <= E_R(xi),
sum_{|xi|>R} E_R(xi)^2 * column_weight(xi) < infinity,
```

再把它送入 Hardy 压缩后的整列平方和或 Cotlar 型几乎正交估计。只证明
`|m| = 1`、逐向量趋零，或 ambient 轨道的点态衰减，均不足以关闭(*)。

## 7. 本次核对后的工作顺序

1. 先为 `rho5` 写对象级桥的 Lean 目标：左侧固定为
   `ordinaryTraceAlong sourceBasis (J† C† G C J)`，右侧固定为有限素数幂和、
   阿基米德项和 P2 余项，禁止先把两侧定义成同一个对象。
2. 并行的数学入口是相位：先补 `arg m` 的可计算表达和余项界，再尝试
   Sonin 压缩尾部的整列估计；没有相位输入时停止尾部路线。
3. 只有在 (*) 或者一个等价的 `P C P` Hilbert--Schmidt 结论落地后，才能
   使用 1502 的 `rho4`，再处理 1507 的 Euler-content bridge 和 1504 的
   `rho5` iff。

本记录没有改变绑定路线，也没有把 ROOT 窗口正性、coverage root 或 ambient
leakage 反例提升为 Sonin 正性结论。

## 8. “四个骨头”不是四个独立门

此前把 S3、B3/B4、`rho5`、C3 并列，会高估独立义务。严格按
`G8SameOwnerReadbackData` 的字段，真正需要的只有三个证明包：

1. **总对角能量包**：survivor 的 in-Sonin square-sum，以及 visible-boundary
   输出的有限族 square-sum。它们可以由一个更强的统一 Hilbert--Schmidt
   定理一起供应；目前没有已知定理说明 survivor 能量会推出 boundary 能量，
   所以不能在数学上直接删掉后者。
2. **同对象聚合桥**：`rho5`，把 `J* C* G C J` 的迹与素数幂、阿基米德和
   P2 余项放到同一个 owner 上。它是代数/算术识别义务，不是新的正性门。
3. **最终 readback**：将前两包组装成 `G8SameOwnerReadbackData`。这一步已有
   正迹消费者；因此 C3 的 `qw >= 0` 不是独立数学骨头，而是该数据结构被
   `qw_nonnegative_of_g8SameOwnerReadbackData` 消费后的形式化推论。

所以当前最小的独立障碍数是 **两个生产器**（总对角能量、`rho5`），外加
一个已经写好的组装接口。若把 survivor/boundary 的能量证明合并成一个主定理，
甚至可以只留下两个待证定理；把整个 readback 一次性证明也可以只写一个目标，
但不会减少其中的数学内容。
