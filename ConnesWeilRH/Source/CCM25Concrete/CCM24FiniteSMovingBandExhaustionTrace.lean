/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSMovingBandSelfAdjointTrace

/-!
# Trace limits along a natural Hilbert-basis exhaustion

Proof 450 used a bound for every finite diagonal subset.  That hypothesis
also bounds the absolute diagonal mass and is stronger than the signed Gate
3U scalar estimate.  This module keeps the fixed-S trace-class witness and
uses only the nested `Finset.range N` partial sums, which converge to the
ordinary diagonal trace without selecting arbitrary positive and negative
subsets.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSMovingBandExhaustionTrace

open CC20Concrete
open MeasureTheory
open scoped InnerProduct InnerProductSpace
open CCM24FiniteSProjectionTrace
open CCM24FiniteSBandTrace
open CCM24FiniteSCanonicalCompletedResponse
open CCM24FiniteSMovingBandDiagonalIntegral
open CCM24FiniteSMovingBandTraceLimit
open CCM24FiniteSMovingBandSelfAdjointTrace
open CCM24FiniteSRootSandwichedMovingFlow

private theorem abs_tsum_le_of_forall_range_abs_sum_le
    (f : ℕ → ℝ) (hf : Summable f) (C : ℝ)
    (hbound : ∀ N : ℕ, |∑ i ∈ Finset.range N, f i| ≤ C) :
    |∑' i, f i| ≤ C := by
  exact le_of_tendsto'
    (continuous_abs.continuousAt.tendsto.comp hf.hasSum.tendsto_sum_nat) hbound

/-! The range-exhaustion bridge is weaker than an all-finsets bound. -/
theorem ordinaryTraceAlong_re_abs_le_of_rangeDiagonalIntegralBound
    (basis : HilbertBasis ℕ ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (C : ℝ)
    (htrace : PositiveTrace.IsTraceClassAlong basis
      (rootSandwichedBandResponse owner lambda family))
    (hbound : ∀ N : ℕ,
      |∫ alpha : ℝ in 0..1,
        ∑ i ∈ Finset.range N,
          (⟪basis i, actualMovingSoninRootFlow owner lambda alpha
            family.visiblePrimes (basis i)⟫_ℂ).re| ≤ C) :
    |(PositiveTrace.ordinaryTraceAlong basis
      (rootSandwichedBandResponse owner lambda family)).re| ≤ C := by
  rw [PositiveTrace.IsTraceClassAlong] at htrace
  have hreal : Summable (fun i =>
      (⟪basis i, rootSandwichedBandResponse owner lambda family
        (basis i)⟫_ℂ).re) := by
    exact Complex.reCLM.summable htrace
  have htrace_eq :
      (PositiveTrace.ordinaryTraceAlong basis
        (rootSandwichedBandResponse owner lambda family)).re =
        ∑' i, (⟪basis i, rootSandwichedBandResponse owner lambda family
          (basis i)⟫_ℂ).re := by
    rw [PositiveTrace.ordinaryTraceAlong]
    exact Complex.reCLM.map_tsum htrace
  rw [htrace_eq]
  apply abs_tsum_le_of_forall_range_abs_sum_le _ hreal C
  intro N
  have hfinite :=
    finiteDiagonalResponse_re_eq_neg_integral_finiteDiagonalFlow_re
      basis (Finset.range N) owner lambda family
  rw [hfinite]
  simpa only [abs_neg] using hbound N

theorem ordinaryTraceAlong_norm_le_of_rangeDiagonalIntegralBound
    (basis : HilbertBasis ℕ ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (C : ℝ)
    (htrace : PositiveTrace.IsTraceClassAlong basis
      (rootSandwichedBandResponse owner lambda family))
    (hbound : ∀ N : ℕ,
      |∫ alpha : ℝ in 0..1,
        ∑ i ∈ Finset.range N,
          (⟪basis i, actualMovingSoninRootFlow owner lambda alpha
            family.visiblePrimes (basis i)⟫_ℂ).re| ≤ C) :
    ‖PositiveTrace.ordinaryTraceAlong basis
      (rootSandwichedBandResponse owner lambda family)‖ ≤ C := by
  rw [ordinaryTraceAlong_rootSandwichedBandResponse_eq_re
    basis owner lambda family]
  simpa only [Complex.norm_real, Real.norm_eq_abs] using
    (ordinaryTraceAlong_re_abs_le_of_rangeDiagonalIntegralBound
      basis owner lambda family C htrace hbound)

theorem canonicalOrdinaryTraceAlong_norm_le_supportRadiusPolynomial_of_rangeDiagonalBound
    (basis : HilbertBasis ℕ ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (htrace : PositiveTrace.IsTraceClassAlong basis
      (rootSandwichedBandResponse owner lambda (canonicalFamily owner)))
    (hbound : ∀ N : ℕ,
      |∫ alpha : ℝ in 0..1,
        ∑ i ∈ Finset.range N,
          (⟪basis i, actualMovingSoninRootFlow owner lambda alpha
            (canonicalFamily owner).visiblePrimes (basis i)⟫_ℂ).re| ≤
        2 * (owner.supportRadius + Real.log 3) *
          (1 + owner.supportRadius + Real.log 3)) :
    ‖PositiveTrace.ordinaryTraceAlong basis
      (rootSandwichedBandResponse owner lambda (canonicalFamily owner))‖ ≤
      2 * (owner.supportRadius + Real.log 3) *
        (1 + owner.supportRadius + Real.log 3) := by
  exact ordinaryTraceAlong_norm_le_of_rangeDiagonalIntegralBound
    basis owner lambda (canonicalFamily owner)
      (2 * (owner.supportRadius + Real.log 3) *
        (1 + owner.supportRadius + Real.log 3)) htrace hbound

end CCM24FiniteSMovingBandExhaustionTrace
end CCM25Concrete
end Source
end ConnesWeilRH
