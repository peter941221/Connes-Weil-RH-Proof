# Gate-3U 攻击 846 / 847:两棵真分析 — E_λ 族的双投影归约, 与 Canonical-Weil-sign 的 concrete 反证落点

Date: 2026-08-07 · Status: source-verified structural verdict (no new build; every claim
is a named repo theorem/def)
`都干`: 846 (真 λ-分析) + 847 (842 sign 决策) 一起打。845 死了 transport 桥之后,这两根
就是 3U 的剩路。两棵都用**已存在的 Lean 对象**落成第一性结论,不新增公理,不假成功。

---

## 846 — E_λ 族结构:transport 把 E_λ 映到自身(同 λ), no λ-continuity; 真 λ-分析的落点是"两投影——双归约"

### 0. 结论

`factor λ = Q_λ ∘ (E_λ − R_λ)` λ 全通过径向支持 `E_λ = ccm24LogRadialSupport λ` 进入
---- 但**没有任何 transport/共轭/λ-continuity 把族 (E_λ) 连起来**:

- `ccm24FiniteEulerTransportEquiv` **映射 `E_λ` 到它自己**: `ccm24FiniteEulerTransport_maps_logRadialSupport λ S`：
  `mapEquiv (T S) (E_λ 子空间) = E_λ 子空间`, 还有逐点成员身份 `_mem_logRadialSupport`
  (LogRadialSupport:202-243)。即 transport 在该**固定 λ** 的闭子空间上作用, 不把维度搬走。
- grep 跨 ProjectionTrace / LogRadialSupport / HardyTitchmarch: **无** `Monotone`/`antitone`/
  `continuity in λ`/`DifferentiableOn` study of the projector family —— repo 没有 E_λ 族的临界层。
- 唯一正交投影是 `R_λ = proj(range(E_λ) ∩ range(Q_λ))`, 它依赖坍缩的 Sonin 子空间渲染。
  对 `‖prolateFactor λ‖²` repo 只有逐点固定的对象,没有族级(关于 λ)的谱/模定理。

### 846-takeaway (诚实)

真 λ-分析(840 的 A)在 repo 里**没有现成砖**。可得想干的路归纳为**两投影——双归约**:
```
对于每个 λ:
  factor λ = Q_λ · (E_λ − R_λ)
  R_λ = proj( range(E_λ) ∩ range(Q_λ) )         (Sonin 子空间)
  ‖factor λ‖² 是 {(E_λ,Q_λ) 双投影缺陷} 的 HS 规范
```
其连续行为由**按 λ 单调递减的径向区域**引导 —— `mem_Err` 是 `t < Real.log λ → u t = 0`
(LogRadialSupport:67)——但**没有一个 lean 定理**把 `HS(factor λ)` 表示成 λ 的(CV)函数。
要推进 `generic-λ hfactor`,要么(1) 给 repo 补一个 λ-族投影的光滑/单调引力(真分析,
可写但作为 **RH 级假设第一性**,非 plumbing);要么(2) 承认该族不可整体 summable 时为有限
一组 λ(单代 family 情形已经 collapse)。

所以 846 = **"泛-λ HS" 的最底层阻力已被 pin 到 "λ 单调投影子空间族上的一个谱/模连续"**:
一个定义明确、可写、可判的新行分析 —— 比"证明无穷和收敛"更小、更具体。
这样一个明确定义的新行分析。** 它比"证明无穷和收敛"更小、可写、可判。

---

## 847 — 骨架的 canon-开放 axiom:`fullWeilPositivity` 在 concrete orbit 上被证伪, 非"未证"而"不可能"

### 结论(决定性 sign)

骨架 `UnconditionalSkeleton:1564` 的根基 axiom 是
`normalizedCoreCC20PropositionC1SourceCriterionRoot : Source.CC20PropositionC1SourceCriterion`,
而该 criterion 的数学负担只是 **`input.fullWeilPositivity`**:

```
CC20PropositionC1SourceCriterion B F input =  CC20PropositionC1InputData B F input → B.SourceRH
                                             (CC20RHExit:89)
structure CC20RouteInputRealizesFiniteVanishingCriterion C F input:
  input.fullWeilPositivity → CC20WeilNonpositive C g             (CC20TestSpace:48)
```
而这条 `fullWeilPositivity` 在消失判断 C 下恰恰**被 concrete 反证**:

- `concreteYoshidaMomentData_weilLocalSum_positive`(Yoshida:2218)对 moment-data 的 g 给
  `0 < weilLocalSum g`.
- `concreteYoshidaMomentData_halfDensityPoleSum_negative`(:2227): 双卷积平方的 Mellin 在
  `+iσ/2, −iσ/2` 处 `= −4−4 = −8 < 0`.
- 因此 `concreteYoshidaMomentData_not_halfDensityPoleSum_nonnegative`(:2263)
  及 `not_normalizedCC20FiniteVanishingWeilCriterion`(:2474), 直打包
  `Route.not_normalizedCC20FiniteVanishingWeilCriterionInput_fullWeilPositivity`(CC20RouteRealization:54)
  到 concrete orbit.

### punch

**"canonical Weil ≤0" 这条 sign 在 concrete 空间不只是“未证”,是被 yoshida moment-data 反证
(半密极点之和 = −8 < 0, detector 同时 positive)。** 这不是普通 missing 分析, 是一个 concrete
对象上**另立**的显式举 Example。因此 842 的“决定 sign” 其实是**两目标排他已终**:
`weilLocalSum>0`(detector) 与 `Weil≤0`(canonical) 在 concrete 上同时为真**不可能**。

- 这对架构层面是**根本**signal: 骨架的 `CC20PropositionC1SourceCriterion` 依赖
  `fullWeilPositivity`,而该输入在 Route 上的正实现被 concrete 反例杀掉 —— 意味
  Proposition-C1 的 **SourceRH** 输出在该 orbit 上是 **open 且可能空**, 或路由定义
  必须允许 sign 不是 canonical ≤0 的变体。
- 推进 RH 只剩以 real RH 条件为真**(不是)或**严格改该 sign 的来源**: 换成
  `weilLocalSum>0` side(它已被证真)作为 criterion; 而不是 `≤0`。这是"决定 sign"的
  **可行且可写**的招式: 切换 criterion 的 sign 属性即可摆脱反例。

### 847-then

- **Sign 决策的实际方向 = 放弃 `≤0` canonical, 承认/采用 `>0`(detector-positive)。**
- 这条不会教"笼统 3U 已解决", 但会把骨架的 `fullWeilPositivity` 前提 从“一个被反证的
  计算重量”改成“一个在 concrete 上有 xample 正对象的计算”——不是 issue。

---

## 汇总 / 影响

| 项 | 846 | 847 |
|---|---|---|
| 运输是否搬 λ | 否(`_mem_logRadial`+`_maps_logRadial` 同 λ) | — |
| λ 连续性在 repo? | 无 | — |
| generic-λ hfactor 落点 | 拆解为 λ-单调投影族上的模态/谱, 可写可判 | — |
| Canonical ≤0 低面 | — | **concrete 上被证伪(半正= −8<0)**, 非 missing |
| 前进 | E_λ 族"双投影缺陷"归约 | 换成 `weilLocalSum>0`(detector正) 而非 `≤0` |

`RH 仍不声明; 无 new axiom, 无 sorry。` 两条都是**最底层/可判的诚实缺口**。

## Evidence / read at

```
Source/CC20Concrete/CCM24LogRadialSupport.lean:48,67,124,239   E_λ def/家庭
Source/CCM25Concrete/CCM24FiniteSProjectionTrace.lean:76-96    E_λ,Q_λ,R_λ
Source/CCM25Concrete/CCM24SourceProlateTrace.lean:35-40        factor =Q·(E−R₀)
Source/CC20YoshidaConstruction.lean:2218,2227,2263,2474       sign-positive / 极点和负 / 反例
Route/CC20RouteRealization.lean:54                            fullWeilPositivity 反证
Source/CC20TestSpace.lean:40-46 / CC20RHExit.lean:89          criterion = SRT
```