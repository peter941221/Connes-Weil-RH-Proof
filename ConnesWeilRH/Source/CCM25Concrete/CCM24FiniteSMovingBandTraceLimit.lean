/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSMovingBandDiagonalIntegral
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCanonicalCompletedResponse

/-!
# Trace limit without exchanging an infinite sum and the time integral

Proof 447 gives an identity for every finite diagonal truncation.  This module
proves the exact limiting principle needed by Gate 3U: if the endpoint
diagonal is summable and all finite signed diagonal integrals share one bound,
then the same bound holds for the ordinary trace.  No infinite
`tsum`/integral exchange and no total-variation estimate is used.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSMovingBandTraceLimit

open CC20Concrete
open MeasureTheory
open scoped InnerProduct InnerProductSpace
open CCM24FiniteSProjectionTrace
open CCM24FiniteSBandTrace
open CCM24FiniteSCanonicalCompletedResponse
open CCM24FiniteSMovingBandDiagonalIntegral
open CCM24FiniteSRootSandwichedMovingFlow

private theorem abs_tsum_le_of_forall_finset_abs_sum_le
    {ι : Type*} (f : ι → ℝ) (hf : Summable f) (C : ℝ)
    (hbound : ∀ J : Finset ι, |∑ i ∈ J, f i| ≤ C) :
    |∑' i, f i| ≤ C := by
  exact le_of_tendsto'
    (continuous_abs.continuousAt.tendsto.comp hf.hasSum) hbound

/-! This theorem is the trace-limit bridge.  The trace-class hypothesis is
kept explicit because the actual finite-S same-carrier owner still has to be
constructed; it is not inferred from compactness or from finite truncations. -/
theorem ordinaryTraceAlong_re_abs_le_of_finiteDiagonalIntegralBound
    {ι : Type*} (basis : HilbertBasis ι ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (C : ℝ)
    (htrace : PositiveTrace.IsTraceClassAlong basis
      (rootSandwichedBandResponse owner lambda family))
    (hbound : ∀ J : Finset ι,
      |∫ alpha : ℝ in 0..1,
        ∑ i ∈ J,
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
  apply abs_tsum_le_of_forall_finset_abs_sum_le _ hreal C
  intro J
  have hfinite := finiteDiagonalResponse_re_eq_neg_integral_finiteDiagonalFlow_re
    basis J owner lambda family
  rw [hfinite]
  simpa only [abs_neg] using hbound J

/-! Canonical-family specialization at the support-radius polynomial already
used by the synchronized Euler-energy ledger.  The finite-diagonal bound is
the remaining signed analytic producer; diagonal energy is not used to infer
it. -/
theorem canonicalOrdinaryTraceAlong_re_abs_le_supportRadiusPolynomial_of_finiteDiagonalBound
    {ι : Type*} (basis : HilbertBasis ι ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (htrace : PositiveTrace.IsTraceClassAlong basis
      (rootSandwichedBandResponse owner lambda (canonicalFamily owner)))
    (hbound : ∀ J : Finset ι,
      |∫ alpha : ℝ in 0..1,
        ∑ i ∈ J,
          (⟪basis i, actualMovingSoninRootFlow owner lambda alpha
            (canonicalFamily owner).visiblePrimes (basis i)⟫_ℂ).re| ≤
        2 * (owner.supportRadius + Real.log 3) *
          (1 + owner.supportRadius + Real.log 3)) :
    |(PositiveTrace.ordinaryTraceAlong basis
      (rootSandwichedBandResponse owner lambda
        (canonicalFamily owner))).re| ≤
      2 * (owner.supportRadius + Real.log 3) *
        (1 + owner.supportRadius + Real.log 3) := by
  exact ordinaryTraceAlong_re_abs_le_of_finiteDiagonalIntegralBound
    basis owner lambda (canonicalFamily owner)
      (2 * (owner.supportRadius + Real.log 3) *
        (1 + owner.supportRadius + Real.log 3)) htrace hbound

end CCM24FiniteSMovingBandTraceLimit
end CCM25Concrete
end Source
end ConnesWeilRH
