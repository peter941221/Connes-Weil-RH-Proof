# 833 — L137/L152 的根源与修复边界：矛盾的 100% 落在一个 `∀F` 后端 witness

Date: 2026-08-07 · Status: verdict (build-verified probe).
Probe: `ConnesWeilRH/Dev/CarrierReplacementFeasibilityProbe.lean`
Build: `lake build ConnesWeilRH.Dev.CarrierReplacementFeasibilityProbe`（WSL，通过 2936 jobs，axiom-clean `[propext, Classical.choice, Quot.sound]`，无 sorryAx）。
Related: `docs/proofs/832_…`（载体替换不可行，推论）、`UnconditionalSkeleton.lean:137/152`、`CCM25SourceDataGuards.lean:30`。
Previous: `docs/proofs/830_…`、`docs/proofs/831_…`。

## 0. 一句话结论

L137/L152 的矛盾，根源**落在且只落在** `SourceFinitePrimeExactSupportData` 里那一条「对**所有**测试 `F : A.Test` 的**后端** witness」`n ∈ carrier → term n F ≠ 0`。

- **旧的（有矛盾）形状**要求：`∀F, n∈carrier → term n F ≠ 0`。载体的零元素 `z` 一旦 `∈ carrier`，就被迫 `term n z ≠ 0`——但零元素的语义项恒为 0。
- **真实路线（无矛盾）形状**（`FixedLambdaCommonFinitePrimeSupportData`，FinitePrimeSourceData.lean:84）：`globalIndexData`/`routeVisibleGlobalIndex` 都**绑定到单一 `common.sourceTest`**，后端 witness 不 `∀F`——所以零测试不受牵连。

探针已在 Lean 中**证明**（非口头）旧形状不可容纳非零素项（`exactSupport_has_no_visible_prime`），且证明这不需要具体名字——对任何带「零元素 + 可见素原子」的载体都成立。

## 1. 探针证了什么（分两侧）

### 侧 A：旧形状不可容纳（build 已证）

```
theorem exactSupport_has_no_visible_prime
  {A} {z} (hZ : EncodesZeroPointwise A z) (E) (S) (n) :
  ¬ ∃ F : A.Test, E.sourceFinitePrimeTerm n F ≠ 0
```

证明链（`EncodesZeroPointwise A z := ∀x, encode z x = 0`）：
```
任意可见项 F (term n F ≠ 0)
  → S.sourceVisibleGlobalIndex F n : n ∈ carrier
  → S.globalPrimeIndexCarrier.2 z n : term n z ≠ 0      ← ∀F 后端，套到零元素 z
  → 与 zero_sourceFinitePrimeTerm (term n z = 0) 冲突
```
`#print axioms = [propext, Classical.choice, Quot.sound]`，**无 sorryAx**。

### 侧 B：后端 witness 是唯一阻塞（源码审计）

`SourceWeilFormData` 的三层字段里，另两层 trivial 可构造：

```
evaluation    : SourceEvaluationData A      == 空结构 → SourceEvaluationData.mk 即可
archimedean   : A.Test → ℝ                 == fun _ => 0
finitePrime   : SourceFinitePrimeData A E   == 唯一卡点 = .exactSupport 的 ∀F 后端 witness
```

空结构 `SourceEvaluationData`（AnalyticCoreBase.lean:262：`structure … where`，无字段）→ 构造它对 concrete 载体**完全 trivial**。唯一阻障是 `SourceWeilFormData` 的 `finitePrime.exactSupport`，而这正是 ∀F 后端 witness。

## 2. 真实健康路线的形态（可构造 → 骨架该接的对象）

`FixedLambdaCommonFinitePrimeSupportData`（已存于 `FinitePrimeSourceData.lean:84`，被 `LPackage`/`Bridge`/`Route` 大量消费）——
```
  globalIndexData :    n∈W.globalIndexSet → SourceGlobalIndexData … commonTest
  routeVisibleGlobalIndex : atomVisible(common convolution) → n∈W.globalIndexSet
  # 只对 common.sourceTest，后端不对 ∀F
```
它**正是** `SourceWeilFormData` 该有却没有的「per-common 有界」形态，且**已在真实路线里造出**。这说明矛盾的**修法不是换载体、不是全树重构**，而是：「Source 抽象层的 `SourceWeilFormData` 过度约束（∀F POST），应改用/对齐这条健康 per-common 读图形态」。

## 3. 对「处理掉」的定位与边界

（a）**一定不要做**：去 `WeilFormSymbols.globalPrimeIndexSet : Finset ℕ`（单一集合）→ per-test。这会牵动下游 31 文件/约 200 处求和，是本次审计证明**非必要**的过度重构。

（b）**唯一被探针指定的定点**：`SourceFinitePrimeExactSupportData` 的 `globalPrimeIndexCarrier.2 / restrictedPrimeIndexCarrier.2` 后端 witness。它是「对全部测试非零」的坏 witness；骨架真正要的 per-common 数据已存在健康版本。所以**最小诚实动作**是：让骨架的有限素数据不再从 `SourceWeilFormData` 出发（它已证假），而是从真实路线的 per-common 数据（`FixedLambdaCommon…`/证书）构造——这正是把 L137 的「假 axiom」替换成「真数据」的连线，且不碰 31 文件共享形状。

## 4. 判定

- **L137 是必须废除的假前提**（它在断言的载体上已被证明不存在），不是「待接线」。
- **L152 是正确判定**（明示 concrete 上那个 ∀F 后端形状的 `SourceWeilFormData` 无对象）——它**没有**过证；它精确拒斥了坏形状。
- **真正的「处理干净」= 用真实 per-common 健康数据取代 L137 假根**，而不动 `WeilFormSymbols` 结构。这一步是 build-able、温和、可回滚的局部接线，而不是一次 31 文件的巨型重构。

## Handoff

- Files read: `AnalyticCore.lean:7355-7470`（载体/ExactSupport 定义）、`FinitePrimeSourceData.lean:84-108`（per-common 健康形）、`FinitePrimeInterface.lean`、`Basic.lean`（WeilFormSymbols 单集合）、`UnconditionalSkeleton.lean:137/152`、`ObjectTheoremBasePackage.lean`（scalarCC20RemainderRows 白捡）。
- Declarations changed: **只新增** `ConnesWeilRH/Dev/CarrierReplacementFeasibilityProbe.lean`（axiom-clean，build 通过）。Source/Route 未改，未污染任何共享类型。
- Build: `lake build ConnesWeilRH.Dev.CarrierReplacementFeasibilityProbe`（通过）。基线骨架 `UnconditionalSkeleton` 的 3495 jobs 未测（本轮只加探针，不改其依赖）。
- 下一步（建议）：在骨架内把 `L137/152` 换成「从真实 per-common 构造器拉取有限素数据」的实构造，跑 `lake build ConnesWeilRH.Dev.UnconditionalSkeleton` 验证。这是小的、可回滚的、直击矛盾点的步。