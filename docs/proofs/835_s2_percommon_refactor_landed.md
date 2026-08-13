# 835 — S2 per-common 重构落地：`SourceWeilFormData` 换成 per-common 承载，L137/L152 自相矛盾解除

> **CURRENT ADDENDUM (2026-08-12).** 本文正确记录了 S2 结构修复，但其
> “L137 仍为开放 axiom”的阶段性状态已经继续推进：
> `Dev/UnconditionalSkeleton.lean` 现在用
> `ConcreteP1SupportProbe.concreteWeilForm` axiom-clean 地构造该类型。
> 剩余 source-data 缺口是 all-pairs finite-prime certificates 与
> `scopedArchimedeanContributionBalance`；真正的顶层 RH 根是 detector
> criterion coverage。见 `docs/proofs/1005_rh_route_after_psp_audit.md`。

Date: 2026-08-07 · Status: landed (build-verified, committed, RH 仍不声明).
Related: `docs/proofs/830_…`、`831_…`、`832_…`、`833_…`、`834_…`（探针/证据根基）。
Commits: `e65c92b`（S2 翻转 + 承载 anchor）、`ba7925b`（修骨架 stale guard + L152）。
Build: full repo `lake build` 绿（4147 jobs）；骨架 `UnconditionalSkeleton` 绿（3495 jobs）。

## 0. 一句话结论

把 `SourceWeilFormData` / `SourceFinitePrimeData` 从"∀F 后端全局 exactSupport"重构成
**per-common 承载**（`PerCommonSourceFinitePrimeSupport` 只对单一 `common.sourceTest`
断言 reverse witness）。这让 L137/L152 的**自相矛盾解除**：二者不再是"互杀"的假前提 vs 正确拒斥，
而是 L152 随旧后端一起退役、L137 保留为诚实的开放式数学底部。RH 依旧**不声明无条件**。

## 1. 之前（834 定下的死结）

- 834 全链证据：骨架所有 finite-prime 主线追到唯一赋值 `SourceAnalyticCore.weilForm
  = normalizedCoreSourceWeilFormDataFromTheorems`（L322），唯一数据源是 **L137 axiom**，
  而 L137 断言的对象被 **L152 `¬ Nonempty`** 证明不存在 → 基座**内部不一致**。
- 根因（833/832）：`SourceWeilFormData.finitePrime.exactSupport` 的
  `sourceVisibleGlobalIndex : ∀F, ∀n, …→ n∈carrier` + 反向 POST witness `n∈carrier → term n F ≠ 0`
  都 `∀ F : Test`，零元素被迫非零 → 任何带零元素的实际承载都容纳不下。
- 结论（834 A2）：要接线必须先**改共享类型**，即 per-common 重构（831 量出 ~31 文件/~200 求和族）。

## 2. 本次实际做的（两个 commit）

| Step | 内容 | commit |
|------|------|--------|
| Step-1（先前 toehold） | 新增 `PerCommonSourceFinitePrimeSupport` 与旧 `exactSupport` 并存，不影响旧侧 | `79fc069` |
| Step-2 翻转 + 共同 anchor | `SourceFinitePrimeData` 改为 `support : PerCommonSourceFinitePrimeSupport`（丢 `exactSupport`）；`SourceWeilFormData` 增 `common : A.Test` + per-common `finitePrime`；`ObjectExpandedRows` / `RouteTheorem` / `FinitePrimeSourceDataBridge` / `CC20RouteRealization` 适配 + 把 per-common 卷积方块 anchor 作为 owner 必填字段并贯穿两类承载 | `e65c92b` |
| 修骨架死链 | 删陈旧 `not_nonempty_concreteSourceWeilFormData` 守卫（其引用的 `W.finitePrime.exactSupport` 字段已不存在）+ 骨架 L152；一致性恢复 | `ba7925b` |

核心 shape 变化（`Source/AnalyticCore.lean`）：

```
旧: structure SourceFinitePrimeData (A) (E) where
      exactSupport : SourceFinitePrimeExactSupportData A E   # 全局, ∀F 反向
新: structure SourceFinitePrimeData (A) (E) (common : A.Test) where
      support : PerCommonSourceFinitePrimeSupport A E common
    structure SourceWeilFormData (A) where
      evaluation  : SourceEvaluationData A
      common      : A.Test
      finitePrime : SourceFinitePrimeData A evaluation common
```

per-common 反向 witness（`commonGlobalIndex : n∈global → term n common ≠ 0`）只对
`common` 断言，**零元素不再被迫非零**，831/832/833 的结构性矛盾消除。

## 3. 骨架状态：L137 现在是"开"不是"互相杀"

- 删除 `CCM25SourceDataGuards.not_non_empty_concreteSourceWeilFormData`：它靠
  `W.finitePrime.exactSupport`（已被删字段）构造，per-common 下不成立（类型不再被迫为空）；
  其结论是"现在开放的 L137 `axiom` 是矛盾"的误判。结构性 verdict 已自包含保留在
  `Dev/CarrierReplacementFeasibilityProbe`。
- 骨架 L152 随守卫一并移除，换为说明性注释。
- `UnconditionalSkeleton` 现在 **40 根 axiom + 0 sorryAx + 0 内部矛盾** 构建绿；
  `normalizedCoreSourceWeilFormDataRoot` 仍是 `Source.AnalyticCore.SourceWeilFormData concreteTestAlgebra`
  的**开放底部**（不再有一个 `¬ Nonempty` 与之驳斥）。

## 4. RH 声明状态（不变）

- 仓库**从不声明 RH 无条件**。骨架 `unconditional_rh_skeleton`（L8061）仍通过 40 个
  `…Root` axiom 提供——这些 axiom 是开放的数学底部，不因本次重构减少。
- 本次改动只改变了"承载数据对象"的一致性与真实可造性；**没有新增任何真素证明**。

## 5. Build & 验证

```
WSL mirror == Windows (md5 校验一致)
lake build                                     # 4147 jobs green
lake build ConnesWeilRH.Dev.UnconditionalSkeleton  # 3495 jobs green
# axioms: skeleton 40 Roots / no sorryAx
```

## 6. 后续（供 Peter 决策）

| 方向 | 内容 | 状态 |
|------|------|------|
| A2-继续 | 用 per-common 承载真正构造一个具体的 `SourceWeilFormData`（需选一个真实 `common` 测试给具体素项），把 L137 `axiom` 换成真实构造 | 未做，是下一个真正数学增量 |
| 清理 | 删除陈旧的 `\`-目录/重名 tracked 垃圾（非本任务，建议单独 PR） | 未做 |

## Handoff

- Files changed: `Source/AnalyticCore`、`Source/ObjectExpandedRows`、`Route/RouteTheorem`、
  `Source/CCM25Concrete/FinitePrimeSourceDataBridge`、`Route/CC20RouteRealization`、
  `Dev/CCM25SourceDataGuards`（删除守卫）、`Dev/UnconditionalSkeleton`.
- Build: full repo 4147 green；skeleton 3495 green。
- 未动：`WeilFormSymbols.globalPrimeIndexSet` 本体；`CarrierReplacementFeasibilityProbe` 自包含 verdict。
