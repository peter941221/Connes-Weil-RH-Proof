/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.StripDensityTraceLedger
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Audit: the compression of a positive operator is not an operator inequality

Record 1625 section 2 priced the strip term by the chain

  `Tr(P M_Δ P) ≤ Tr(E M_Δ E) = volume(Δ ∩ S) ≤ Λ`,

whose middle step was stated as the operator-level sandwich

  `P (E M_Δ E) P ≤ E M_Δ E`     for orthogonal projections `P ≤ E`.

That step is **false**.  This leaf carries the refutation, in the smallest
possible model: `E = 1`, `M = rankOne u u ≥ 0`, `P = rankOne e e` a rank-one
orthogonal projection, and a test vector `w` with

  `⟪e, e⟫ = 1`,  `⟪e, u⟫ = 1`,  `⟪u, w⟫ = 0`,  `⟪e, w⟫ = -1`

(the two-dimensional witness below realizes these relations in `ℂ²` by
`e = e₂`, `u = e₁ + e₂`, `w = e₁ - e₂`).  In that model

  `(M - P M P) w = e`   and   `re ⟪w, (M - P M P) w⟫ = -1 < 0`,

so `M - P M P` is not positive, i.e. `P M P ≤ M` fails.

What is formalized here: the refutation `rankOne_compression_not_le`, the
projection facts `IsIdempotentElem`/`IsSelfAdjoint` for `rankOne x x` from
`⟪x, x⟫ = 1`, the positivity `IsPositive` of both rank-one operators, and the
`ℂ²` witness for the four inner-product relations.  One standard step is *not*
formalized here: `P ≤ 1` for a rank-one projection (Cauchy–Schwarz,
`re ⟪y, P y⟫ = ‖⟪e, y⟫‖² ≤ ‖y‖²` for `‖e‖ = 1`); it is the only hypothesis of
1625's sandwich that the refutation does not verify inside Lean, and the
refutation itself does not use it.

The conclusion of 1625 is unaffected: the trace-level statement
`re Tr(P T P) ≤ re Tr(T)` is true for positive `T`, is named as
`StripDensityCompressionObligation` in the parent module, and is what the
repaired chain consumes.
-/

namespace ConnesWeilRH
namespace Dev
namespace StripDensityTraceLedgerAudit

open scoped ComplexConjugate InnerProduct InnerProductSpace
open InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ## The general refutation -/

omit [CompleteSpace E] in
/-- **The compression of a positive rank-one operator is not below it.**  If
`P = rankOne e e` is a rank-one projection (`⟪e, e⟫ = 1`), `M = rankOne u u` is
positive, and the test vector `w` satisfies `⟪u, w⟫ = 0` and `⟪e, w⟫ = -1`, then
`P M P ≤ M` fails. -/
theorem rankOne_compression_not_le (u e w : E)
    (hue : ⟪e, u⟫_ℂ = 1) (huw : ⟪u, w⟫_ℂ = 0) (hew : ⟪e, w⟫_ℂ = -1) :
    ¬ (rankOne ℂ e e ∘L rankOne ℂ u u ∘L rankOne ℂ e e ≤ rankOne ℂ u u) := by
  intro hle
  have hpos :
      (rankOne ℂ u u - rankOne ℂ e e ∘L rankOne ℂ u u ∘L rankOne ℂ e e).IsPositive :=
    hle
  have hnn : 0 ≤ (⟪w, (rankOne ℂ u u
      - rankOne ℂ e e ∘L rankOne ℂ u u ∘L rankOne ℂ e e) w⟫_ℂ).re :=
    hpos.re_inner_nonneg_right w
  have hue' : ⟪u, e⟫_ℂ = 1 := by rw [← inner_conj_symm, hue, map_one]
  have hPMP : rankOne ℂ e e ∘L rankOne ℂ u u ∘L rankOne ℂ e e = rankOne ℂ e e := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, rankOne_apply, inner_smul_right,
      hue, hue', mul_one]
  have hTw : (rankOne ℂ u u - rankOne ℂ e e ∘L rankOne ℂ u u ∘L rankOne ℂ e e) w = e := by
    rw [ContinuousLinearMap.sub_apply, hPMP, rankOne_apply, huw, zero_smul, zero_sub,
      rankOne_apply, hew]
    simp
  have hval : (⟪w, (rankOne ℂ u u
      - rankOne ℂ e e ∘L rankOne ℂ u u ∘L rankOne ℂ e e) w⟫_ℂ).re = -1 := by
    rw [hTw, ← inner_conj_symm, hew, map_neg, map_one]
    simp
  linarith

/-! ## The rank-one projection facts -/

omit [CompleteSpace E] in
/-- A rank-one operator `rankOne x x` with `⟪x, x⟫ = 1` is idempotent, i.e. a
projection. -/
theorem isIdempotentElem_rankOne_of_inner_self (x : E) (hx : ⟪x, x⟫_ℂ = 1) :
    IsIdempotentElem (rankOne ℂ x x) := by
  rw [IsIdempotentElem, ContinuousLinearMap.mul_def, rankOne_comp_rankOne, hx, one_smul]

/-- A rank-one operator `rankOne x x` with `⟪x, x⟫ = 1` is self-adjoint (the
adjoint of `rankOne x x` is itself), hence an orthogonal projection. -/
theorem isSelfAdjoint_rankOne_of_inner_self (x : E) (hx : ⟪x, x⟫_ℂ = 1) :
    IsSelfAdjoint (rankOne ℂ x x) :=
  (ContinuousLinearMap.IsIdempotentElem.isPositive_iff_isSelfAdjoint
      (isIdempotentElem_rankOne_of_inner_self x hx)).mp
    (InnerProductSpace.isPositive_rankOne_self x)

/-! ## The two-dimensional witness -/

namespace TwoDimensional

/-- The second standard basis vector `e₂` of `ℂ²`, playing the role of `e`. -/
noncomputable def eTwo : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single 1 1

/-- `e₁ + e₂`, playing the role of `u`. -/
noncomputable def uTwo : EuclideanSpace ℂ (Fin 2) :=
  EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1

/-- `e₁ - e₂`, playing the role of the test vector `w`. -/
noncomputable def wTwo : EuclideanSpace ℂ (Fin 2) :=
  EuclideanSpace.single 0 1 - EuclideanSpace.single 1 1

theorem inner_eTwo_uTwo : ⟪eTwo, uTwo⟫_ℂ = 1 := by
  simp [eTwo, uTwo, EuclideanSpace.inner_single_left]

theorem inner_uTwo_wTwo : ⟪uTwo, wTwo⟫_ℂ = 0 := by
  simp [uTwo, wTwo, inner_add_left, inner_sub_right, EuclideanSpace.inner_single_left]

theorem inner_eTwo_wTwo : ⟪eTwo, wTwo⟫_ℂ = -1 := by
  simp [eTwo, wTwo, inner_sub_right, EuclideanSpace.inner_single_left]

theorem inner_eTwo_self : ⟪eTwo, eTwo⟫_ℂ = 1 := by
  simp [eTwo]

/-- **The counterexample, in `ℂ²`.**  With `E = 1`, `M = rankOne u u ≥ 0` and
`P = rankOne e e` a rank-one orthogonal projection, the operator inequality
`P M P ≤ M` fails. -/
theorem rankOne_compression_counterexample :
    ¬ (rankOne ℂ eTwo eTwo ∘L rankOne ℂ uTwo uTwo ∘L rankOne ℂ eTwo eTwo
        ≤ rankOne ℂ uTwo uTwo) :=
  rankOne_compression_not_le uTwo eTwo wTwo
    inner_eTwo_uTwo inner_uTwo_wTwo inner_eTwo_wTwo

end TwoDimensional

/-! ## Axiom audit -/

#print axioms ConnesWeilRH.Dev.StripDensityTraceLedger.re_ordinaryTraceAlong_eq_tsum_re
#print axioms ConnesWeilRH.Dev.StripDensityTraceLedger.ordinaryTraceAlong_re_nonneg
#print axioms ConnesWeilRH.Dev.StripDensityTraceLedger.ordinaryTraceAlong_re_mono
#print axioms ConnesWeilRH.Dev.StripDensityTraceLedger.stripDensity_trace_le_of_compression
#check @ConnesWeilRH.Dev.StripDensityTraceLedger.stripDensity_compression_of_positiveComposition
#print axioms
  ConnesWeilRH.Dev.StripDensityTraceLedger.stripDensity_compression_of_positiveComposition
#print axioms ConnesWeilRH.Dev.StripDensityTraceLedgerAudit.rankOne_compression_not_le
#print axioms
  ConnesWeilRH.Dev.StripDensityTraceLedgerAudit.TwoDimensional.rankOne_compression_counterexample

end StripDensityTraceLedgerAudit
end Dev
end ConnesWeilRH
