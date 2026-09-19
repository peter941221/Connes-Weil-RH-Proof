/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.PositiveTrace
import ConnesWeilRH.Source.CC20Concrete.HilbertSchmidtIdeal
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# The StripDensity trace ledger: positivity, Loewner monotonicity, and the compression obligation

Record 1625 section 2 priced the strip term in the G8 residual identity by the
five-line chain

  `Tr(P M_Δ P) ≤ Tr(E M_Δ E) = volume(Δ ∩ S) ≤ Λ`.

The chain's middle step was stated there as an *operator-level* sandwich
`P (E M_Δ E) P ≤ E M_Δ E` for orthogonal projections `P ≤ E`.  That step is
**false** as stated: the compression of a positive operator by a projection is
not below the operator in the Loewner order (the audit companion
`StripDensityTraceLedgerAudit` carries an explicit two-dimensional
counterexample in raw vector coordinates).  The *conclusion* of the chain is
unaffected; what the repaired proof needs is the trace-level statement.

This module supplies, for the diagonal-series trace `ordinaryTraceAlong` of
`Source.CC20Concrete.PositiveTrace`:

* `re_ordinaryTraceAlong_eq_tsum_re` — the real part of the trace is the real
  series of the diagonal real parts (no summability beyond the given one);
* `ordinaryTraceAlong_re_nonneg` — a positive operator has nonnegative real
  trace (the positivity half of 1625's irreducible ingredient 2);
* `ordinaryTraceAlong_re_mono` — the Loewner monotonicity
  `A ≤ B -> re Tr A ≤ re Tr B` (the second half of that ingredient);
* `StripDensityCompressionObligation` — the exact remaining ingredient, named:
  `re Tr(P T P) ≤ re Tr(T)` for `T` positive and `P` a projection, together
  with the conditional reduction `stripDensity_trace_le_of_compression`, which
  reproduces 1625's chain with that step as an explicit hypothesis.

The compression inequality is standard (its usual proof factors `T = T^{1/2}
T^{1/2}` and uses `T^{1/2} P T^{1/2} ≤ T^{1/2} T^{1/2}`); what is missing here
is an operator square root in the tree's layer, which is why it is filed as a
named obligation rather than proved.  No estimate on `P ∘L C ∘L J`, on S3, on
B4, on (★), or on RH is claimed.
-/

namespace ConnesWeilRH
namespace Dev
namespace StripDensityTraceLedger

open scoped ComplexConjugate InnerProduct InnerProductSpace
open ConnesWeilRH.Source.CC20Concrete.PositiveTrace

variable {ι κ H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## Real part of the diagonal series -/

omit [CompleteSpace H] in
/-- The real part of the diagonal-series trace is the real series of the
diagonal real parts.  Only the given summability of the complex series is
needed. -/
theorem re_ordinaryTraceAlong_eq_tsum_re (basis : HilbertBasis ι ℂ H)
    (operator : H →L[ℂ] H) (hsum : IsTraceClassAlong basis operator) :
    (ordinaryTraceAlong basis operator).re
      = ∑' i, (⟪basis i, operator (basis i)⟫_ℂ).re := by
  rw [ordinaryTraceAlong]
  simpa [Complex.reCLM_apply] using Complex.reCLM.map_tsum hsum

/-! ## Positivity -/

omit [CompleteSpace H] in
/-- A positive operator has nonnegative real trace along any Hilbert basis,
whenever the diagonal series is summable. -/
theorem ordinaryTraceAlong_re_nonneg (basis : HilbertBasis ι ℂ H)
    (operator : H →L[ℂ] H) (hpos : operator.IsPositive)
    (hsum : IsTraceClassAlong basis operator) :
    0 ≤ (ordinaryTraceAlong basis operator).re := by
  rw [re_ordinaryTraceAlong_eq_tsum_re basis operator hsum]
  exact tsum_nonneg fun i => hpos.re_inner_nonneg_right (basis i)

/-! ## Loewner monotonicity -/

omit [CompleteSpace H] in
/-- The diagonal real part of a Loewner-smaller operator is pointwise smaller
along any basis. -/
theorem re_inner_self_le_of_le (basis : HilbertBasis ι ℂ H)
    {left right : H →L[ℂ] H} (hle : left ≤ right) (i : ι) :
    (⟪basis i, left (basis i)⟫_ℂ).re ≤ (⟪basis i, right (basis i)⟫_ℂ).re := by
  have hpos : (right - left).IsPositive := hle
  have hsplit : (⟪basis i, right (basis i)⟫_ℂ).re
      = (⟪basis i, left (basis i)⟫_ℂ).re
        + (⟪basis i, (right - left) (basis i)⟫_ℂ).re := by
    rw [ContinuousLinearMap.sub_apply, inner_sub_right, Complex.sub_re]
    ring
  have hnonneg : 0 ≤ (⟪basis i, (right - left) (basis i)⟫_ℂ).re :=
    hpos.re_inner_nonneg_right (basis i)
  linarith [hsplit]

omit [CompleteSpace H] in
/-- Loewner monotonicity of the real diagonal-series trace: if `left ≤ right`
and both diagonal series are summable, the real traces are ordered. -/
theorem ordinaryTraceAlong_re_mono (basis : HilbertBasis ι ℂ H)
    {left right : H →L[ℂ] H} (hle : left ≤ right)
    (hleft : IsTraceClassAlong basis left) (hright : IsTraceClassAlong basis right) :
    (ordinaryTraceAlong basis left).re ≤ (ordinaryTraceAlong basis right).re := by
  have hleftRe : Summable fun i => (⟪basis i, left (basis i)⟫_ℂ).re :=
    hleft.mapL Complex.reCLM
  have hrightRe : Summable fun i => (⟪basis i, right (basis i)⟫_ℂ).re :=
    hright.mapL Complex.reCLM
  calc (ordinaryTraceAlong basis left).re
      = ∑' i, (⟪basis i, left (basis i)⟫_ℂ).re :=
        re_ordinaryTraceAlong_eq_tsum_re basis left hleft
    _ ≤ ∑' i, (⟪basis i, right (basis i)⟫_ℂ).re :=
        hleftRe.tsum_le_tsum (fun i => re_inner_self_le_of_le basis hle i) hrightRe
    _ = (ordinaryTraceAlong basis right).re :=
        (re_ordinaryTraceAlong_eq_tsum_re basis right hright).symm

/-! ## The compression obligation and 1625's chain -/

/-- **The compression obligation** (the missing layer of record 1625 section 4,
item 3, at the trace level): for `T` positive and `P` an orthogonal projection,
the compressed operator has real trace at most that of `T`,

  `re Tr(P T P) ≤ re Tr(T)`.

The proof in the literature factors `T = T^{1/2} T^{1/2}` and bounds
`T^{1/2} P T^{1/2} ≤ T`; the tree's layer has no operator square root, so the
statement is named here as an obligation to be discharged by a future brick
(or replaced by a direct measure-theoretic basis-to-integral identity, the
other reading of the same missing layer). -/
def StripDensityCompressionObligation (basis : HilbertBasis ι ℂ H)
    (projection operator : H →L[ℂ] H) : Prop :=
  (ordinaryTraceAlong basis (projection ∘L operator ∘L projection)).re
    ≤ (ordinaryTraceAlong basis operator).re

/-- Compression cannot increase the trace of a positive composition when the
positive operator is presented by a Hilbert--Schmidt factor.  This is the
factorization form of the missing compression obligation: no operator square
root is required, and the proof uses the established Hilbert--Schmidt ideal
estimate for precomposition by a bounded map. -/
theorem stripDensity_compression_of_positiveComposition
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G]
    (basis : HilbertBasis ι ℂ H)
    (targetBasis : HilbertBasis κ ℂ G)
    (factor : H →L[ℂ] G) (projection : H →L[ℂ] H)
    (hself : projection.adjoint = projection)
    (hnorm : ‖projection‖ ≤ 1)
    (hfactor : Summable fun i => ‖factor (basis i)‖ ^ 2) :
    StripDensityCompressionObligation basis projection
      (factor.adjoint ∘L factor) := by
  let compressed : H →L[ℂ] G := factor ∘L projection
  have hcompressed : Summable fun i => ‖compressed (basis i)‖ ^ 2 := by
    exact Source.CC20Concrete.PositiveTrace.summable_normSq_precomp basis targetBasis basis
      factor projection hfactor
  let data : Source.CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) basis :=
    { left := factor
      right := factor
      left_summable_normSq := hfactor
      right_summable_normSq := hfactor }
  let compressedData : Source.CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) basis :=
    { left := compressed
      right := compressed
      left_summable_normSq := hcompressed
      right_summable_normSq := hcompressed }
  have hcompressedOperator : compressedData.traceProduct =
      projection ∘L (factor.adjoint ∘L factor) ∘L projection := by
    dsimp [compressedData, compressed,
      Source.CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.traceProduct]
    rw [ContinuousLinearMap.adjoint_comp, hself]
    simp only [ContinuousLinearMap.comp_assoc]
  have htrace_data :
      (ordinaryTraceAlong basis data.traceProduct).re =
        ∑' i, ‖factor (basis i)‖ ^ 2 := by
    rw [ordinaryTraceAlong]
    have hdiag : (fun i => ⟪basis i, data.traceProduct (basis i)⟫_ℂ) =
        (fun i => ((‖factor (basis i)‖ ^ 2 : ℝ) : ℂ)) := by
      funext i
      rw [data.traceProduct_diagonal]
      simpa only [data, Complex.ofReal_pow] using
        (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (factor (basis i)))
    rw [hdiag]
    have hmap :
        ((∑' i, ‖factor (basis i)‖ ^ 2 : ℝ) : ℂ) =
          ∑' i, ((‖factor (basis i)‖ ^ 2 : ℝ) : ℂ) := by
      exact Complex.ofRealCLM.map_tsum hfactor
    rw [← hmap]
    simp
  have htrace_compressed :
      (ordinaryTraceAlong basis compressedData.traceProduct).re =
        ∑' i, ‖compressed (basis i)‖ ^ 2 := by
    rw [ordinaryTraceAlong]
    have hdiag : (fun i =>
        ⟪basis i, compressedData.traceProduct (basis i)⟫_ℂ) =
        (fun i => ((‖compressed (basis i)‖ ^ 2 : ℝ) : ℂ)) := by
      funext i
      rw [compressedData.traceProduct_diagonal]
      simpa only [compressedData, Complex.ofReal_pow] using
        (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (compressed (basis i)))
    rw [hdiag]
    have hmap :
        ((∑' i, ‖compressed (basis i)‖ ^ 2 : ℝ) : ℂ) =
          ∑' i, ((‖compressed (basis i)‖ ^ 2 : ℝ) : ℂ) := by
      exact Complex.ofRealCLM.map_tsum hcompressed
    rw [← hmap]
    simp
  unfold StripDensityCompressionObligation
  have hdataOperator : data.traceProduct = factor.adjoint ∘L factor := by
    rfl
  rw [← hcompressedOperator, htrace_compressed, ← hdataOperator, htrace_data]
  have hbound :=
    Source.CC20Concrete.PositiveTrace.tsum_normSq_precomp_le basis targetBasis basis
      factor projection hfactor
  calc
    ∑' i, ‖compressed (basis i)‖ ^ 2 ≤
        ‖projection‖ ^ 2 * (∑' i, ‖factor (basis i)‖ ^ 2) := hbound
    _ ≤ 1 * (∑' i, ‖factor (basis i)‖ ^ 2) := by
      gcongr
      simpa using ((sq_le_sq₀ (norm_nonneg _) (by norm_num)).mpr hnorm)
    _ = ∑' i, ‖factor (basis i)‖ ^ 2 := by ring

omit [CompleteSpace H] in
/-- **1625's chain, repaired.**  If `P` is a projection below `E` (so that
`P E = E P = P`), `M` is any operator, and the compression obligation holds
for the positive operator `E M E`, then the strip density along `P` is at most
the trace of `E M E`:

  `re Tr(P M P) ≤ re Tr(E M E)`.

This is 1625 section 2's conclusion with its invalid operator sandwich replaced
by the trace-level obligation. -/
theorem stripDensity_trace_le_of_compression (basis : HilbertBasis ι ℂ H)
    {P E M : H →L[ℂ] H} (hPE : P ∘L E = P) (hEP : E ∘L P = P)
    (hcomp : StripDensityCompressionObligation basis P (E ∘L M ∘L E)) :
    (ordinaryTraceAlong basis (P ∘L M ∘L P)).re
      ≤ (ordinaryTraceAlong basis (E ∘L M ∘L E)).re := by
  have hmid : P ∘L (E ∘L M ∘L E) ∘L P = P ∘L M ∘L P := by
    rw [show P ∘L (E ∘L M ∘L E) ∘L P = (P ∘L E) ∘L M ∘L (E ∘L P) by
      simp only [ContinuousLinearMap.comp_assoc]]
    rw [hPE, hEP]
  rw [← hmid]
  exact hcomp

end StripDensityTraceLedger
end Dev
end ConnesWeilRH
