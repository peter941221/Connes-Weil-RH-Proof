/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorLocalCofactor
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierMomentDecay

/-!
# Complete one-prime numerator bound

For the empty suffix, the complete interior owner is the one-prime boundary
moment dressed on the left and right by the paired Schur--Markov transitions:

```text
Interior_(p,[]) = -Transition_p^dagger * Moment_[p] * Reverse_p^dagger.
```

Both transition factors are contractions.  The existing one-prime moment
estimate therefore gives a uniform bound for the complete numerator itself,
not merely for its restriction to the unrenewed new-frame column.  Along the
arithmetic-prime sequence, both `sqrt(q_p) ||Interior_(p,[])||` and the
corresponding weighted operator energy tend to zero.

This rules out a numerator-growth obstruction on the empty suffix.  It does
not compare the numerator with the renewed antiresonant denominator, whose
range can still contain approximate-kernel sequences.  Bone 1 remains open.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorOnePrimeNumeratorBound

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaRawCoframeBoundaryTelescope
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorGap
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorLocalCofactor
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierMomentDecay
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierMovingMomentColumnSelector
open CCM24FiniteSCompletedJuliaRawPhysicalOnePrimeMomentNorm
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawLocalTraceFactorization
open CCM24FiniteSSchurMarkovPairing

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/- A generic three-factor contraction estimate keeps this calculation away
from the expanded CCM24 frame and coframe implementations. -/
set_option maxHeartbeats 1000000 in
-- Operator-norm composition elaboration needs a larger deterministic budget.
theorem norm_comp_comp_le_of_left_right_contractions
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (left middle right : H →L[ℂ] H) (bound : ℝ)
    (hleft : ‖left‖ ≤ 1) (hmiddle : ‖middle‖ ≤ bound)
    (hright : ‖right‖ ≤ 1) (hbound : 0 ≤ bound) :
    ‖(left ∘L middle) ∘L right‖ ≤ bound := by
  calc
    ‖(left ∘L middle) ∘L right‖ ≤
        ‖left ∘L middle‖ * ‖right‖ :=
      ContinuousLinearMap.opNorm_comp_le (left ∘L middle) right
    _ ≤ (‖left‖ * ‖middle‖) * ‖right‖ := by
      exact mul_le_mul_of_nonneg_right
        (ContinuousLinearMap.opNorm_comp_le left middle) (norm_nonneg right)
    _ ≤ (1 * bound) * 1 := by
      exact mul_le_mul
        (mul_le_mul hleft hmiddle (norm_nonneg _) zero_le_one)
        hright (norm_nonneg _) (mul_nonneg zero_le_one hbound)
    _ = bound := by ring

/-- The complete empty-suffix interior numerator is uniformly bounded over
all arithmetic one-prime steps.  No renewed denominator is inverted. -/
theorem norm_signedCompressedInteriorOwner_nil_le_twentyFour_mul_detector
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (hp : Nat.Prime p.1) :
    ‖signedCompressedInteriorOwner owner lambda p []‖ ≤
      24 * ‖detectorOperator owner‖ := by
  let moment := rawCoframeBoundaryMoment owner lambda
    (suffixActualBandForwardCoframe lambda [p])
    (suffixActualBandForwardEndpointCoframe lambda [p])
  have hmoment : ‖moment‖ ≤ 24 * ‖detectorOperator owner‖ := by
    exact norm_onePrimeRawCoframeBoundaryMoment_le_twentyFour_mul_detector
      owner lambda p (singlePrimeFamily p hp)
        (singlePrimeFamily_visiblePrimes p hp)
  have hleft : ‖-(suffixEulerFrameTransition lambda p [])†‖ ≤ 1 := by
    calc
      ‖-(suffixEulerFrameTransition lambda p [])†‖ =
          ‖(suffixEulerFrameTransition lambda p [])†‖ :=
        ContinuousLinearMap.opNorm_neg _
      _ = ‖suffixEulerFrameTransition lambda p []‖ :=
        ContinuousLinearMap.adjoint.norm_map _
      _ ≤ 1 := suffixEulerFrameTransition_norm_le_one lambda p []
  have hright : ‖(suffixEulerFrameReverseTransition lambda p [])†‖ ≤ 1 := by
    calc
      ‖(suffixEulerFrameReverseTransition lambda p [])†‖ =
          ‖suffixEulerFrameReverseTransition lambda p []‖ :=
        ContinuousLinearMap.adjoint.norm_map _
      _ ≤ 1 := suffixEulerFrameReverseTransition_norm_le_one lambda p []
  rw [signedCompressedInteriorOwner_eq_rawPhysicalFourTermRow_comp_reverseAdjoint,
    suffixActualBandRawPhysicalFourTermRow_cons_nil_eq_neg_boundaryMoment]
  exact norm_comp_comp_le_of_left_right_contractions
    (-(suffixEulerFrameTransition lambda p [])†) moment
    ((suffixEulerFrameReverseTransition lambda p [])†)
    (24 * ‖detectorOperator owner‖)
    hleft hmoment hright (by positivity)

/-- The square-root Euler weight kills the complete empty-suffix numerator in
operator norm along the genuine arithmetic-prime sequence. -/
theorem
    tendsto_sqrtCoefficient_mul_norm_interior_nil_arithmeticVisiblePrimeSequence
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    Filter.Tendsto
      (fun n =>
        Real.sqrt (ccm24PrimeEulerCoefficient
            (arithmeticVisiblePrimeSequence n)) *
          ‖signedCompressedInteriorOwner owner lambda
            (arithmeticVisiblePrimeSequence n) []‖)
      Filter.atTop (nhds 0) := by
  have hcoeff :=
    tendsto_ccm24PrimeEulerCoefficient_arithmeticVisiblePrimeSequence
  have hsqrt : Filter.Tendsto
      (fun n => Real.sqrt (ccm24PrimeEulerCoefficient
        (arithmeticVisiblePrimeSequence n)))
      Filter.atTop (nhds 0) := by
    simpa only [Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hcoeff
  have hupper : ∀ n,
      Real.sqrt (ccm24PrimeEulerCoefficient
          (arithmeticVisiblePrimeSequence n)) *
          ‖signedCompressedInteriorOwner owner lambda
            (arithmeticVisiblePrimeSequence n) []‖ ≤
        Real.sqrt (ccm24PrimeEulerCoefficient
          (arithmeticVisiblePrimeSequence n)) *
          (24 * ‖detectorOperator owner‖) := by
    intro n
    exact mul_le_mul_of_nonneg_left
      (norm_signedCompressedInteriorOwner_nil_le_twentyFour_mul_detector
        owner lambda (arithmeticVisiblePrimeSequence n)
          (arithmeticVisiblePrimeSequence_isPrime n))
      (Real.sqrt_nonneg _)
  have hlimit : Filter.Tendsto
      (fun n => Real.sqrt (ccm24PrimeEulerCoefficient
          (arithmeticVisiblePrimeSequence n)) *
        (24 * ‖detectorOperator owner‖))
      Filter.atTop (nhds 0) := by
    simpa using hsqrt.mul_const (24 * ‖detectorOperator owner‖)
  exact squeeze_zero
    (fun n => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    hupper hlimit

/-- Energy form of the preceding decay, matching the explicit numerator
weight in the renewal-deviation formulation of Bone 1. -/
theorem
    tendsto_coefficient_mul_norm_sq_signedCompressedInteriorOwner_nil_arithmeticVisiblePrimeSequence
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    Filter.Tendsto
      (fun n =>
        ccm24PrimeEulerCoefficient (arithmeticVisiblePrimeSequence n) *
          ‖signedCompressedInteriorOwner owner lambda
            (arithmeticVisiblePrimeSequence n) []‖ ^ 2)
      Filter.atTop (nhds 0) := by
  have hcoeff :=
    tendsto_ccm24PrimeEulerCoefficient_arithmeticVisiblePrimeSequence
  have hupper : ∀ n,
      ccm24PrimeEulerCoefficient (arithmeticVisiblePrimeSequence n) *
          ‖signedCompressedInteriorOwner owner lambda
            (arithmeticVisiblePrimeSequence n) []‖ ^ 2 ≤
        ccm24PrimeEulerCoefficient (arithmeticVisiblePrimeSequence n) *
          (24 * ‖detectorOperator owner‖) ^ 2 := by
    intro n
    exact mul_le_mul_of_nonneg_left
      (sq_le_sq₀ (norm_nonneg _) (by positivity) |>.2
        (norm_signedCompressedInteriorOwner_nil_le_twentyFour_mul_detector
          owner lambda (arithmeticVisiblePrimeSequence n)
            (arithmeticVisiblePrimeSequence_isPrime n)))
      (ccm24PrimeEulerCoefficient_nonneg _)
  have hlimit : Filter.Tendsto
      (fun n => ccm24PrimeEulerCoefficient (arithmeticVisiblePrimeSequence n) *
        (24 * ‖detectorOperator owner‖) ^ 2)
      Filter.atTop (nhds 0) := by
    simpa using hcoeff.mul_const ((24 * ‖detectorOperator owner‖) ^ 2)
  exact squeeze_zero
    (fun n => mul_nonneg (ccm24PrimeEulerCoefficient_nonneg _) (sq_nonneg _))
    hupper hlimit

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorOnePrimeNumeratorBound
end CCM25Concrete
end Source
end ConnesWeilRH
