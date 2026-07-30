/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualSchurPhysicalResidualUniformControl

/-!
# Hilbert--Schmidt energy of the actual physical residual

Proof 572 gives a family-uniform operator-norm bound for the physical-versus-
Schur residual.  This module consumes that bound only after a Hilbert--Schmidt
source input and a bounded physical right leg have been fixed.  The result is
an absolute energy estimate, uniform in the visible finite prime list:

```text
sum_i ||M residual_S input(e_i)||^2
  <= 4 ||M||^2 sum_i ||input(e_i)||^2.
```

This is deliberately not a Douglas estimate through the adjacent Julia
analysis column.  It controls the residual contribution to a physical energy
ledger while retaining the separate relative-factorization obligation.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSActualSchurPhysicalResidualEnergy

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CCM24FiniteSActualJuliaInput
open CCM24FiniteSActualSchurForwardPhysicalDifference
open CCM24FiniteSActualSchurPhysicalResidualUniformControl
open CCM24FiniteSGramResponse
open CCM24FiniteSProjectionTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Generic bounded-residual energy -/

theorem tsum_normSq_postcomp_residual_le
    {ι H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (basis : HilbertBasis ι ℂ H)
    (input : H →L[ℂ] H)
    (hinput : Summable fun i => ‖input (basis i)‖ ^ 2)
    (residual : H →L[ℂ] K)
    (hresidual : ‖residual‖ ≤ (2 : ℝ))
    (rightLeg : K →L[ℂ] G) :
    (∑' i, ‖(rightLeg ∘L residual ∘L input) (basis i)‖ ^ 2) ≤
      4 * ‖rightLeg‖ ^ 2 * (∑' i, ‖input (basis i)‖ ^ 2) := by
  have hresidualInput : Summable fun i =>
      ‖(residual ∘L input) (basis i)‖ ^ 2 := by
    exact summable_normSq_postcomp basis input residual hinput
  have houtput : Summable fun i =>
      ‖(rightLeg ∘L residual ∘L input) (basis i)‖ ^ 2 := by
    simpa only [ContinuousLinearMap.comp_assoc] using
      (summable_normSq_postcomp basis (residual ∘L input) rightLeg
        hresidualInput)
  have hpoint : ∀ i,
      ‖(rightLeg ∘L residual ∘L input) (basis i)‖ ^ 2 ≤
        4 * ‖rightLeg‖ ^ 2 * ‖input (basis i)‖ ^ 2 := by
    intro i
    have hresidualPoint :
        ‖residual (input (basis i))‖ ≤
          2 * ‖input (basis i)‖ := by
      calc
        ‖residual (input (basis i))‖ ≤
            ‖residual‖ * ‖input (basis i)‖ :=
          residual.le_opNorm _
        _ ≤ 2 * ‖input (basis i)‖ := by
          exact mul_le_mul_of_nonneg_right hresidual (norm_nonneg _)
    have hrightPoint :
        ‖rightLeg (residual (input (basis i)))‖ ≤
          ‖rightLeg‖ * (2 * ‖input (basis i)‖) := by
      calc
        ‖rightLeg (residual (input (basis i)))‖ ≤
            ‖rightLeg‖ * ‖residual (input (basis i))‖ :=
          rightLeg.le_opNorm _
        _ ≤ ‖rightLeg‖ * (2 * ‖input (basis i)‖) := by
          exact mul_le_mul_of_nonneg_left hresidualPoint
            (norm_nonneg _)
    have hrightSq := (sq_le_sq₀
      (norm_nonneg (rightLeg (residual (input (basis i)))))
      (mul_nonneg (norm_nonneg rightLeg)
        (mul_nonneg (by norm_num) (norm_nonneg (input (basis i)))))).mpr
      hrightPoint
    calc
      ‖(rightLeg ∘L residual ∘L input) (basis i)‖ ^ 2 =
          ‖rightLeg (residual (input (basis i)))‖ ^ 2 := by rfl
      _ ≤ (‖rightLeg‖ * (2 * ‖input (basis i)‖)) ^ 2 := hrightSq
      _ = 4 * ‖rightLeg‖ ^ 2 * ‖input (basis i)‖ ^ 2 := by ring
  have hmajorant : Summable fun i =>
      4 * ‖rightLeg‖ ^ 2 * ‖input (basis i)‖ ^ 2 := by
    exact hinput.mul_left (4 * ‖rightLeg‖ ^ 2)
  calc
    (∑' i, ‖(rightLeg ∘L residual ∘L input) (basis i)‖ ^ 2) ≤
        ∑' i, 4 * ‖rightLeg‖ ^ 2 * ‖input (basis i)‖ ^ 2 :=
      houtput.tsum_le_tsum hpoint hmajorant
    _ = 4 * ‖rightLeg‖ ^ 2 *
        (∑' i, ‖input (basis i)‖ ^ 2) := by
      rw [tsum_mul_left]

/-! ## Actual finite-S residual -/

theorem sourceActualBandForwardTransportResidual_tsum_normSq_postcomp_le
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime)
    {ι : Type*}
    (basis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    (input : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda)
    (hinput : Summable fun i => ‖input (basis i)‖ ^ 2)
    (rightLeg : finiteSCarrier →L[ℂ] G) :
    (∑' i, ‖(rightLeg ∘L
        sourceActualBandForwardTransportResidual lambda stepData S ∘L input)
        (basis i)‖ ^ 2) ≤
      4 * ‖rightLeg‖ ^ 2 * (∑' i, ‖input (basis i)‖ ^ 2) := by
  apply tsum_normSq_postcomp_residual_le basis input hinput
    (sourceActualBandForwardTransportResidual lambda stepData S)
  · exact sourceActualBandForwardTransportResidual_norm_le_two lambda stepData S

end CCM24FiniteSActualSchurPhysicalResidualEnergy
end CCM25Concrete
end Source
end ConnesWeilRH
