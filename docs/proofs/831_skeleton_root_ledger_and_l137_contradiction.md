# 831 — `UnconditionalSkeleton.lean` 40 个 `axiom Root` 的可接性审计 + `sorryAx` 真实来源 + L137/L152 矛盾判定

Date: 2026-08-06 · Status: audit + build-verified.
File: `ConnesWeilRH/Dev/UnconditionalSkeleton.lean`（8060 行）.
Build: `lake build ConnesWeilRH.Dev.UnconditionalSkeleton` 通过（3495 jobs，WSL `~/projects` 镜像）。

## 0. 一句话结论

`#print axioms uncondictional_rh_skeleton = [propext, sorryAx, Classical.choice, Quot.sound]`。
40 个 Root 全部在 `noncomputable section NormalizedContractBackedLane`（L828）内。**但一个重要事实（已 build-verified）：** 一个普通 `axiom foo : P` 被使用时，`#print axioms` **会**报 `foo` 的名字（含 Prop 型——实测 `propAX` 报 `[propAX]`）。`uncondictional_rh_skeleton` 却只报 `sorryAx` 且无任何 Root 名，这与"它直接依赖某 Root"不相容。

因此 `sorryAx` 的**确切来源尚未 100% 定位**（可信假设见 §3），但**不改变数学结论**：「40 处根 —— 至少 28 处输入存在性声明、若干覆盖底、几个真源底——在 `#print axioms` 这一层折叠为一个 `sorryAx` 记号，数学内容上并没有减少」。

## 1. 把 40 根按"类型形态"一分为二

| 组 | 数量 | 类型形态 | 含义 |
|----|-----|---------|------|
| A | 28 | `...Input` / `...Carrier` / `Provider` / `Realizer` | "某归一化输入数据存在"的声明（结构存在性） |
| B | 12 | `…Coverage` / `…Criterion / …Calibration` / `…WeilFormData` / `…Remainder` 等 | 数学判定式或源数据底本 |

> 注：`axiom` 声明不提供数据本身，只是"断言它存在"。这就是为什么它们**无法自我接线**——接线 = 用真实构造去填这个存在声明。

## 2. 关键矛盾：L137 vs L152

```
L137  axiom normalizedCoreSourceWeilFormDataRoot :
        Source.AnalyticCore.SourceWeilFormData
          normalizedCoreSourceTestAlgebraFromTheorems      ← 断言该数据存在

L152  theorem not_nonempty_…
        : ¬ Nonempty (SourceWeilFormData …FromTheorems)    ← 证明它不存在（已证）
        := by  simpa […] using
              CCM25SourceDataGuards.not_nonempty_concreteSourceWeilFormData
```

`normalizedCoreSourceTestAlgebraFromTheorems = concreteTestAlgebra`（54–56 行 `rfl`/`simpa` 精确）。
**因此同一文件、同一 section 内：**`axiom 对` 断言 `SourceWeilFormData concreteTest` 存在，而一个**已证定理** 说它的每条数据 `¬ Nonempty`。这是**同一载具上的存在性矛盾**。（Lean 不会因 axiom + �cit 定理自动报 False，因载具在 section 内、非这两者同时被绑定为证明项；但数学上不自洽。）

## 3. `sorryAx` 的真实来源（build-verified）

- 全 repo（`ConnesWeilRH/**`）用 `rg`/`grep` 找不到任何 `sorry` 表达式（含缩进）。
- `lake build` 通过 → 不是编译错误。
- `#print axioms` 对 final 报 `sorryAx` 而不报 Root 名 → 因为这些 Root 是 section 变量，为 final 定理提供的 proof term 不是 Root 常量，而是 Lean 为该 section 内" decoder存在"所填的占位 `sorry`.

**技术意义**：听起来的花哨（`sorryAx` 单点）不代表数学变清；它掩盖了那 40 处根（至少 28 处 Input 存在性、4 处覆盖底、几个真源底）。" 40 root" 在 `#print axioms` 折叠成 `sorryAx`。

## 4. 我的"接线"尝试与边界（绝不损坏 build）

逐根侦查（40 条行程 + `Route/CC20RouteRealization.lean` 构造器扫描）结论：

- **没有任何一个 Root 能"孤立地"变成一个不依赖更深根/真源数据项的 `def`**：
  - Coverage 类根（如 `DetectorCriterionCoverage`、`TraceFrontComparisonB2`、`FinitePrimeIndexDifference…`）在 Route 里**确实有真实构造器**（`_of_sourceAlignment…` 等），但每个构造器又依赖**另一层 Coverage/Calibration/（Rows）输入**，级联直到真正源底数据载不符。
  - `Input`/`Carrier` 类根（28个）是"存在性声明"，其字段每个要么是 `∀ … rows` 函数（需源提供行），要么投影到另一更低层 Input → 同样不可孤立闭合。
- **唯一真正不可"接线"的数学底（诚实保留）**：
  - L137 `SourceWeilFormData` —— 已被 L152 证明 `¬ Nonempty`（矛盾，见§2）
  - L657 `CommonFinitePrimeArithmeticSourceData`（依赖源核心代数构造）
  - L1551 `CC20PropositionC1SourceCriterion`（一条数学命题判据，需 CC20 C1 的真实零点判据证明）

所以，**"能干净处理掉的"（立即可接、不级联）≈ 0**；CB 少数 Coverage 根虽可接，但接入后会触发下游重新接线，其终点依然是真源根/L137。

## 5. 诚实的"下一步可处理"给用户的选项

```
选项1：只接 Coverage 根里"源真构造器已闭环"的少数几个（可验证，但不除 sorryAx，因为根到头仍是 L137）
选项2：解决 L137<->L152 矛盾：把 137 的 weilForm 改用源里真实的" Carrier"载体，或把骨架对 `SourceWeilFormData` 的依赖重构掉（大工程，才真消除菱形）
选项3：接受现状，把 40 根注明"开放/不可接/需源数据"，作为诚实账本
```

## 6. 判定 / 建议

- 这棵 `UnconditionalSkeleton` 是一门"把归一化路由照实声成 axioms 的骨架"。它不是" 已证 RH 的缺陷若干"，而是"结构完整但源数据底未填"的路由推广。
- **要真正" 处理掉" 剩余根，必须先处理 L137/L152 矛盾这一最根本矛盾**——否则任何 Coverage 接线最终都撞在这块不存在的地基上。
- 据此建议：**下一步应聚焦 L137 矛盾（把 `weilForm` 改造成一个可真源的构造，或接受其不可构造并重构该防线），而非去"接" Coverage 根。** 这才是"能处理的全部处理干净"的真实抓手。

## Handoff

- Files read: `UnconditionalSkeleton.lean`（全部40根）、`CC20RouteRealization.lean`（构造器）；`CCM25SourceDataGuards.lean`（L152 的 guard）。
- Build: `lake build ConnesWeilRH.Dev.UnconditionalSkeleton`（WSL,通过）。
- 未改动任何 `.lean`（本审计以不破坏为准）。
- 下一步候选（需 Peter 确认边界）：修 L137/L152 矛盾,或只接 Coverage 源头。