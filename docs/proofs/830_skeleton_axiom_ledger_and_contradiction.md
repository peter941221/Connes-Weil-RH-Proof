# 830 — 《"一个等式" vs "40 个 sorry"》：`UnconditionalSkeleton.lean` 全部 40 个 `axiom` 的对账表 + 一处构造矛盾

Date: 2026-08-06 · Status: analysis / audit (self-created).
File audited: `ConnesWeilRH/Dev/UnconditionalSkeleton.lean` (8060 lines).
Related: `ConnesWeilRH/Dev/CCM25SourceDataGuards.lean`,
`ConnesWeilRH/Source/AnalyticCore.lean`, `ConnesWeilRH/Source/ObjectTheoremBasePackage.lean`.

## 0. 一句话结论

815 说"RH 整个归约到**一个算子恒等式**（Gate-3U）"是对 **数学墙** 的表述；
`UnconditionalSkeleton.lean` 里 **40 个 `axiom`** 是对 **这条归一化路线未完成装配** 的表述。
两者**不重叠、不矛盾**，但骨架这端有一个**更要紧的事实**：其中两个声明在同一文件里**互相矛盾**，导致这套底件 axiom 系统**内部不一致**。

## 1. 最刺眼的一处：axiom 与同文件定理直接矛盾

`UnconditionalSkeleton.lean` 自己的两行：

```
L137  axiom normalizedCoreSourceWeilFormDataRoot :
        Source.AnalyticCore.SourceWeilFormData
          normalizedCoreSourceTestAlgebraFromTheorems

L152  theorem not_nonempty_normalizedCoreSourceWeilFormData :
        ¬ Nonempty (Source.AnalyticCore.SourceWeilFormData
                      normalizedCoreSourceTestAlgebraFromTheorems)
      := by
        simpa [...] using
          CCM25SourceDataGuards.not_nonempty_concreteSourceWeilFormData
```

关键链（已在 54–56 行确认 `rfl` 精确等式）：

```
normalizedCoreSourceTestAlgebraFromTheorems
      = SourceConcreteBaseLayer.concreteTestAlgebra     (L54-56, rfl)
CCM25SourceDataGuards.not_nonempty_concreteSourceWeilFormData   (λp两)
      : ¬ Nonempty (SourceWeilFormData concreteTestAlgebra)     (L30, 已证)
```

所以 **`axiom 137` 断言一个已被 `theorem 152` 证明不存在的对象**。

而该 axiom 的产物 `normalizedCoreSourceWeilFormDataFromTheorems`（141）被**装配进骨架源分析核心**：

```
L318  normalizedCoreSourceAnalyticCoreFromTheorems : Source.AnalyticCore.SourceAnalyticCore where
   testAlgebra := ...concreteTestAlgebra
L322  weilForm := normalizedCoreSourceWeilFormDataFromTheorems   ← axiom 137
```

`normalizedCoreSourceAnalyticCoreFromTheorems` 又是后续 **30+ 个 `Root`、整条归一化路线、最终 `unconditional_rh_skeleton`** 共用的"源分析核心"地基（657/1067/1076/1551/1706 … 全都吃它）。即：**整栋楼盖在一块已被证明不存在的基石上**。

编译能过，是因为 `RiemannHypothesis` 是 `Prop`，axiom 被当黑盒接受、不做 proof-relevant 计算；一旦路线把 `weilForm` 计算到具体值，会在第一质数处撞出 `False`（见 `CCM25SourceDataGuards` 的证明结构）。所以这不是"没证完"，是**自相矛盾**。

## 2. 40 个 axiom 的完整账本（逐行）

| Ln | name | 类型 | 类 | 有无 `Source/` 真实定理 |
|----|------|------|----|----|
| 137 | normalizedCoreSourceWeilFormDataRoot | `SourceWeilFormData concreteTestAlgebra` | A | **无——与已证定理矛盾** |
| 657 | normalizedCoreCCM25FinitePrimeArithmeticSourceDataRoot | `CommonFinitePrimeArithmeticSourceData (core.toWeilFormSymbols)` | A | 吃 137 地基 |
| 1067 | normalizedCoreS2B1RemainderRowsOutsideNoBulkRoot | `S2B1NormalizedCC20RemainderRowsOutsideNoBulk seed` | A | 吃 657 地基 |
| 1076 | normalizedCoreS2B1TracePackageRemaindersRoot | `CC20TracePackageRemainderData seed` | A | 吃 657 地基 |
| 1551 | normalizedCoreCC20ProposedC1SourceCriterionRoot | `∀input, CC20ProposedC1SourceCriterion bridge` | B(定理形) | `Source/CC20RHExit.lean:89` 有 def |
| 1665 | normalizedSourceObjectBridgeReadOffRowsInputRoot | `NormalizedSourceObjectBridgeReadOffRowsInput` | B(包装) | — |
| 1706 | normalizedSourceObjectScalarRemainderRowsProviderRoot | `∀ seed, NormalizedScalarCC20RemainderRows seed` | B(定理形) | `ObjectTheoremBasePackage:3124 scalarCC20RemainderRows` **可白捡** |
| 2715 | normalizedSelectedFinitePrimeIndexDifferenceInputRoot | `NormalizedSelectedFinitePrimeIndexDifferenceInput` | C · Input | 管道 |
| 4736 | normalizedRestrictedToFullFinitePrimeIndexDifferenceRowsRoot | `...RowsProvider` | C | 管道 |
| 5883 | normalizedSelectedYoshidaDetectorPolePairingNonnegativeCoreRoot | `...NonnegativeRealizer` | B(定理形) | 无现存 Source 定理 |
| 7741 | normalizedSelectedFinalRouteDetectorCoverageRoot | `...DetectorCoverage` | C | 位移校准 |
| 7744 | normalizedSelectedFinalRouteTraceFrontB2Root | `...TraceFrontComparisonB2Calibration` | C | 位移校准 |
| 7747 | normalizedSelectedFinalRouteConcreteCanonicalRoutePackageCoverageRoot | ...Coverage | C | 位移校准 |
| 7750 | normalizedSelected | `...FinitePrimeIndexDifferenceCalibration` | C | 位移校准 |
| 7753 | normalizedSelected | `...DirectGlobalUnfilteredTermMassCalibration` | C | 位移校准 |
| 7759 | normalizedSelected | `...TermForSourceTestAtomPackage...RowsCalibration` | C | 位移校准 |
| 7762 ~ 7831 | normalizedSelectedLineDifference...Input x 12+ | `...Input` | C(纯 Input包) | 纯装配 |
| 7881 | normalizedSelectedFinalRouteCertificateCarrierRoot | `...CertificateCarrier` | C | 装配 |

> 注：7741–7831 实为同一条"detector-selected 位移校准升级阶梯"，把上一根的输出包成下一根的输入；
> 7807+ 一段在文件里被 section 降级（"belonged only to the demoted..."）。
> "类"：A=含源数据存在性数学；B=定理形/可接线；C=纯装配位移校准。

## 3. 三类根 / 真正要补的数学

```
  40  axiom
    ├─ C 类  纯位移校准 / 输入包装   ~28（7741–7881 大部分）
    │        → 是"装配工作"，不是"新数学"。等 A/B 有了对接就有定义可填。
    ├─ B 类  定理形 / 可读接口        ~4（1551,1665,1706,5883）
    │        → 1706 在 Source 已可白捡（scalarCC20RemainderRows）。
    │          others 需看单点。
    └─ A 类  源数据/地基存在性根       5（137,657,1067,1076,+ AnalyticCore)
             → 这里才是真数学底本。
               其中最要命的一条 137 与定理 152 矛盾。

真数学增量 ≈ A 类的少数几根——不是 40。
```

## 4. 与 815「一个等式」的对齐

- **815 的"一个等式"** = **E1/3U 门**：`‖bcpoint‖≤1 ⟺ forward+outer+secondSupport+prolate=0`（跨分支消除，out无穷 sum 归零）。那是 **MATH 墙**，开。
- **40 个 axiom** = **归一化路线装配账本**，与 Gate 无关；逐段声明"这一段的输入存在"，等 A 类地基有了真实证明，B/C 类大多能按编号直接填成定义。
- 所以**把它们都叫"sorry"会高估**（大多是可定位的装配缺口），**也都叫"接线"会低估**（A 类里至少一条与已证定理矛盾）。

诚实的对账表：

| 实验 | 这句话为什么对 | 这句话哪里过头 |
| ----- | ---- | ---- |
| "只剩一个算子恒等式"(815) | 3U 门外壁链确实收缩到唯一一个跨分支消除恒等式 | 它没覆盖 A 类源底基存在性；那些根不在 815 视野里 |
| "还有 40 个 sorry"（骨架） | 40 个 axiom + 1 处 sorryAx 真实躺在 `#print axioms` | 大多是可装配的位移焊接位，不是 40 个独立开放猜想;且最严重的是 137 与 152 矛盾，而非单纯"没证" |

## 4. 判定：RH 依旧无条件地走不通，原因升级

无条件 `unconditional_rh_skeleton : RiemannHypothesis` **现在不但没证完，它的 axiom 地基还自相矛盾**（137 vs 152）。

- `#print axioms unconditional_ih_skeleton` = `[propext, Classical.choice, Quot.sound, sorryAx]` 之上叠加了这组不一致的 `...Root`。
- 因此：**不能** 把"若干"假设为"conditional provision"。任何"清理全部 40 根" 的工作，**第一优先级是把 `SourceWeilFormData` 的地基理顺**（要么换一个不在 `∃` 强制存在性的 concrete 代数，要么把 137 换成真实构造），否则后面的根焊接毫无意义。

## 5. 结论 / 交付

- 文档已产出：全部 40 根的分类账（L137–L7881）。
- 关键新发现（这次审计的独有贡献）：`axiom 137` 与 `theorem 152` 在同一文件矛盾 ⇒ 归一化路线地基不一致。
- 建议路线：
  1. 先修 A 类地基 —— 废弃/替换 137 的存在性，改接到一个真实可构造的 `SourceWeilFormData`（或把 137 换成一个 Source 里的真定理）。
  2. 再按 B→C 顺序把与 `Source/` 一致时可白捡的根（如 1706/1551）换成真实接线。
  3. 之后才回到 815 的 3U 门跨分支消除（真正的 MATH 增长）。

最后：RH 状态仍是无条件走不通，也**没有**迫近 —— 因为地基不一致。

## Handoff

- Files read: `Unconditional...`（全 40 根分类）、`AnalyticCore.lean:7746+`（`SourceWeilFormData` 结构）、`ObjectTheoremBasePackage.lean:3124`（可白捡的 `scalarCC20RemainderRows`）。
- Declarations changed: none（纯审计）。
- 与既往 probe 的关系：829 证 `outer 门 wall 非 HS` ；830 证明这一层的"40 sorry"主要是可装配账 + A 类地基不一致。