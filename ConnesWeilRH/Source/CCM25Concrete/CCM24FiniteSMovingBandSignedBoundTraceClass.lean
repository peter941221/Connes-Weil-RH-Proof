/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSMovingBandSelfAdjointTrace

/-!
# Trace legality from the signed moving-band bound

For a self-adjoint endpoint, a uniform bound on every finite signed diagonal
sum already forces absolute summability of the diagonal.  Proof 447 turns the
finite moving-flow integral bound into exactly those endpoint sums.

Consequently the signed Gate 3U producer supplies its own same-carrier
`IsTraceClassAlong` witness.  No separate trace-legality premise is needed.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSMovingBandSignedBoundTraceClass

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

theorem rootSandwichedBandResponse_isTraceClassAlong_of_finiteDiagonalIntegralBound
    {ι : Type*} (basis : HilbertBasis ι ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (C : ℝ)
    (hbound : ∀ J : Finset ι,
      |∫ alpha : ℝ in 0..1,
        ∑ i ∈ J,
          (⟪basis i, actualMovingSoninRootFlow owner lambda alpha
            family.visiblePrimes (basis i)⟫_ℂ).re| ≤ C) :
    PositiveTrace.IsTraceClassAlong basis
      (rootSandwichedBandResponse owner lambda family) := by
  apply isTraceClassAlong_of_selfAdjoint_finiteDiagonalBound basis _
    (rootSandwichedBandResponse_adjoint_eq owner lambda family) C
  intro J
  have hfinite := finiteDiagonalResponse_re_eq_neg_integral_finiteDiagonalFlow_re
    basis J owner lambda family
  rw [hfinite]
  simpa only [abs_neg] using hbound J

theorem ordinaryTraceAlong_norm_le_of_finiteDiagonalIntegralBound
    {ι : Type*} (basis : HilbertBasis ι ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (C : ℝ)
    (hbound : ∀ J : Finset ι,
      |∫ alpha : ℝ in 0..1,
        ∑ i ∈ J,
          (⟪basis i, actualMovingSoninRootFlow owner lambda alpha
            family.visiblePrimes (basis i)⟫_ℂ).re| ≤ C) :
    ‖PositiveTrace.ordinaryTraceAlong basis
      (rootSandwichedBandResponse owner lambda family)‖ ≤ C := by
  have htrace :=
    rootSandwichedBandResponse_isTraceClassAlong_of_finiteDiagonalIntegralBound
      basis owner lambda family C hbound
  rw [ordinaryTraceAlong_rootSandwichedBandResponse_eq_re basis owner lambda]
  simpa only [Complex.norm_real, Real.norm_eq_abs] using
    (ordinaryTraceAlong_re_abs_le_of_finiteDiagonalIntegralBound
      basis owner lambda family C htrace hbound)

theorem canonicalRootSandwichedBandResponse_isTraceClassAlong_of_finiteDiagonalBound
    {ι : Type*} (basis : HilbertBasis ι ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (hbound : ∀ J : Finset ι,
      |∫ alpha : ℝ in 0..1,
        ∑ i ∈ J,
          (⟪basis i, actualMovingSoninRootFlow owner lambda alpha
            (canonicalFamily owner).visiblePrimes (basis i)⟫_ℂ).re| ≤
        2 * (owner.supportRadius + Real.log 3) *
          (1 + owner.supportRadius + Real.log 3)) :
    PositiveTrace.IsTraceClassAlong basis
      (rootSandwichedBandResponse owner lambda (canonicalFamily owner)) := by
  exact
    rootSandwichedBandResponse_isTraceClassAlong_of_finiteDiagonalIntegralBound
      basis owner lambda (canonicalFamily owner)
      (2 * (owner.supportRadius + Real.log 3) *
        (1 + owner.supportRadius + Real.log 3)) hbound

theorem canonicalOrdinaryTraceAlong_norm_le_of_finiteDiagonalBound
    {ι : Type*} (basis : HilbertBasis ι ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (hbound : ∀ J : Finset ι,
      |∫ alpha : ℝ in 0..1,
        ∑ i ∈ J,
          (⟪basis i, actualMovingSoninRootFlow owner lambda alpha
            (canonicalFamily owner).visiblePrimes (basis i)⟫_ℂ).re| ≤
        2 * (owner.supportRadius + Real.log 3) *
          (1 + owner.supportRadius + Real.log 3)) :
    ‖PositiveTrace.ordinaryTraceAlong basis
      (rootSandwichedBandResponse owner lambda (canonicalFamily owner))‖ ≤
      2 * (owner.supportRadius + Real.log 3) *
        (1 + owner.supportRadius + Real.log 3) := by
  exact ordinaryTraceAlong_norm_le_of_finiteDiagonalIntegralBound
    basis owner lambda (canonicalFamily owner)
      (2 * (owner.supportRadius + Real.log 3) *
        (1 + owner.supportRadius + Real.log 3)) hbound

end CCM24FiniteSMovingBandSignedBoundTraceClass
end CCM25Concrete
end Source
end ConnesWeilRH
