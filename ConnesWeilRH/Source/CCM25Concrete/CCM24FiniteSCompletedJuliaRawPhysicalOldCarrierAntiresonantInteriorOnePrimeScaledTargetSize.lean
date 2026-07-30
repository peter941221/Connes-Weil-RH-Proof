/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorTwoStepCoboundaryFactorization

/-!
# The scaled target-size gate for the one-prime subfamily

Proof 655 isolates the necessary horizon-one estimate
`||C_(p,S)|| / s_p`. Proof 638 already gives
`||C_(p,[])|| <= 244 q_p ||detector||` for an arithmetic visible prime.
Since

```text
q_p / s_p = sqrt(q_p) (1 + q_p) <= 2,
```

the complete empty-suffix scaled target is bounded by
`488 ||detector||`, uniformly in `p`. Thus the size gate is closed for the
one-prime subfamily. The nonempty-suffix size gate and the two-step
coboundary factor remain open.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorOnePrimeScaledTargetSize

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualJuliaRangeSineAmbientScaleGuard
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFiniteHorizonCoboundary
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorOnePrimeNumeratorDecay
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorOneStepTargetSize
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantRadialBlockRecurrence
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24UnitScaleProlateAlignment

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Scalar comparison -/

/-- Dividing the Euler coefficient by the ambient-loss scale leaves one
square root and the harmless upper Euler factor. -/
theorem coefficient_div_primeEulerAmbientLossScale_eq
    (p : CCM24VisiblePrime) :
    ccm24PrimeEulerCoefficient p / primeEulerAmbientLossScale p =
      Real.sqrt (ccm24PrimeEulerCoefficient p) *
        (1 + ccm24PrimeEulerCoefficient p) := by
  have hq : 0 ≤ ccm24PrimeEulerCoefficient p :=
    ccm24PrimeEulerCoefficient_nonneg p
  have hsqrt : 0 < Real.sqrt (ccm24PrimeEulerCoefficient p) :=
    Real.sqrt_pos.2 (ccm24PrimeEulerCoefficient_pos p)
  have hupper : 0 < 1 + ccm24PrimeEulerCoefficient p := by
    linarith [ccm24PrimeEulerCoefficient_pos p]
  unfold primeEulerAmbientLossScale
  field_simp [ne_of_gt hsqrt, ne_of_gt hupper]
  nlinarith [Real.sq_sqrt hq]

/-- The coefficient-to-loss-scale ratio is uniformly at most two. -/
theorem coefficient_div_primeEulerAmbientLossScale_le_two
    (p : CCM24VisiblePrime) :
    ccm24PrimeEulerCoefficient p / primeEulerAmbientLossScale p ≤ 2 := by
  rw [coefficient_div_primeEulerAmbientLossScale_eq]
  have hq : 0 ≤ ccm24PrimeEulerCoefficient p :=
    ccm24PrimeEulerCoefficient_nonneg p
  have hqOne : ccm24PrimeEulerCoefficient p ≤ 1 :=
    (ccm24PrimeEulerCoefficient_lt_one p).le
  have hsqrtNonneg :
      0 ≤ Real.sqrt (ccm24PrimeEulerCoefficient p) := Real.sqrt_nonneg _
  have hsqrtOne : Real.sqrt (ccm24PrimeEulerCoefficient p) ≤ 1 := by
    nlinarith [Real.sq_sqrt hq]
  calc
    Real.sqrt (ccm24PrimeEulerCoefficient p) *
        (1 + ccm24PrimeEulerCoefficient p) ≤ 1 * 2 := by
      exact mul_le_mul hsqrtOne (by linarith) (by positivity) zero_le_one
    _ = 2 := one_mul 2

/-! ## Empty-suffix size gate -/

/-- The empty-suffix complete target divided by its genuine loss scale is
uniformly bounded across arithmetic visible primes. -/
theorem norm_onePrime_scaledCompleteCoupledAmbientTarget_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (p : CCM24VisiblePrime) (hp : Nat.Prime p.1) :
    ‖((primeEulerAmbientLossScale p : Complex)⁻¹) •
        suffixActualBandCompleteCoupledAmbientTarget
          owner unitSoninScale p []‖ ≤
      488 * ‖detectorOperator owner‖ := by
  have hscale : 0 < primeEulerAmbientLossScale p :=
    primeEulerAmbientLossScale_pos p
  have hinterior :=
    norm_signedCompressedInteriorOwner_nil_le_twoHundredFortyFour_coefficient
      owner unitSoninScale p hp
  have htarget :
      ‖suffixActualBandCompleteCoupledAmbientTarget
          owner unitSoninScale p []‖ ≤
        244 * ccm24PrimeEulerCoefficient p * ‖detectorOperator owner‖ := by
    rw [norm_suffixActualBandCompleteCoupledAmbientTarget_eq_interior]
    exact hinterior
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hscale]
  calc
    (primeEulerAmbientLossScale p)⁻¹ *
        ‖suffixActualBandCompleteCoupledAmbientTarget
          owner unitSoninScale p []‖ ≤
        (primeEulerAmbientLossScale p)⁻¹ *
          (244 * ccm24PrimeEulerCoefficient p *
            ‖detectorOperator owner‖) :=
      mul_le_mul_of_nonneg_left htarget (inv_nonneg.mpr hscale.le)
    _ = 244 *
          (ccm24PrimeEulerCoefficient p /
            primeEulerAmbientLossScale p) *
          ‖detectorOperator owner‖ := by
      rw [div_eq_mul_inv]
      ring
    _ ≤ 244 * 2 * ‖detectorOperator owner‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (coefficient_div_primeEulerAmbientLossScale_le_two p)
          (by norm_num))
        (norm_nonneg _)
    _ = 488 * ‖detectorOperator owner‖ := by ring

/-- The one-prime size-gate predicate, separated from the nonempty-suffix
route family. -/
def SuffixCompleteCoupledOnePrimeUniformScaledTargetBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (bound : Real) : Prop :=
  0 ≤ bound ∧ ∀ p : CCM24VisiblePrime, Nat.Prime p.1 →
    ‖((primeEulerAmbientLossScale p : Complex)⁻¹) •
        suffixActualBandCompleteCoupledAmbientTarget
          owner unitSoninScale p []‖ ≤ bound

/-- Proof 638 closes the one-prime size gate with the explicit constant
`488 ||detector||`. -/
theorem onePrimeUniformScaledTargetBound
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    SuffixCompleteCoupledOnePrimeUniformScaledTargetBound owner
      (488 * ‖detectorOperator owner‖) := by
  refine ⟨mul_nonneg (by norm_num) (norm_nonneg _), ?_⟩
  intro p hp
  exact norm_onePrime_scaledCompleteCoupledAmbientTarget_le owner p hp

end
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorOnePrimeScaledTargetSize
end CCM25Concrete
end Source
end ConnesWeilRH
