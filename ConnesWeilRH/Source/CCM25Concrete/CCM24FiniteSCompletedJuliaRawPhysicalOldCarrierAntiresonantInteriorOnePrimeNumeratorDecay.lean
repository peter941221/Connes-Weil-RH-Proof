/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorOnePrimeNumeratorBound
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelRenewalDeviation
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierOnePrimeAntiresonantScreen

/-!
# Complete one-prime numerator decay

The normalized inverse in the reverse transition has the exact renewal split

```text
N_p^dagger = rho_p I + sqrt(q_p) L_p^dagger N_p^dagger.
```

After the genuine old/new polar frames are inserted, the complete signed
interior numerator therefore splits as

```text
Interior_(p,S)
  = rho_p (ReducedRow_(p,S) newFrame_S)
    + sqrt(q_p) ReducedRow_(p,S) RenewedColumn_(p,S).
```

For the empty suffix, the first column is already `O(q_p)` and the reduced
row is uniformly bounded by the one-prime boundary moment estimate.  The
renewed column contributes a second factor `O(sqrt(q_p))`.  Hence the complete
one-prime numerator is `O(q_p)` in operator norm.

This removes the scalar large-prime obstruction on the empty suffix.  It does
not control the approximate antiresonant kernel of `I + U_(log p)` and does
not prove Bone 1.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorOnePrimeNumeratorDecay

open scoped InnerProduct InnerProductSpace
open scoped Topology

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCausalMarkov
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization
open CCM24FiniteSCompletedJuliaPolarRawReadout
open CCM24FiniteSCompletedJuliaRawCoframeBoundaryTelescope
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorGap
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorLocalCofactor
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorOnePrimeNumeratorBound
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelFactorization
open
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorSingleChannelRenewalDeviation
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierFixedSourceKernelGuard
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierMomentDecay
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierMovingMomentColumnSelector
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierOnePrimeAntiresonantScreen
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierReduction
open CCM24FiniteSCompletedJuliaRawPhysicalOnePrimeMomentNorm
open CCM24FiniteSCompletedJuliaRawPhysicalOnePrimeMomentReduction
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawLocalTraceFactorization
open CCM24FiniteSSchurMarkovPairing
open CCM24FiniteSSchurMarkovUniformBound

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Exact renewal split -/

/-- The complete signed interior is the reduced row followed by the normalized
inverse adjoint on the actual new suffix frame. -/
theorem signedCompressedInteriorOwner_eq_reducedRow_comp_inverseAdjoint_comp_newFrame
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    signedCompressedInteriorOwner owner lambda p S =
      suffixActualBandRawPhysicalReducedRow owner lambda p S ∘L
        (normalizedPrimeEulerInverse p)† ∘L newSuffixFrame lambda S := by
  rw [signedCompressedInteriorOwner_eq_rawPhysicalFourTermRow_comp_reverseAdjoint]
  simp only [suffixEulerFrameReverseTransition,
    suffixEulerFrameSchurStep,
    ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint,
    suffixActualBandRawPhysicalReducedRow,
    ContinuousLinearMap.comp_assoc]

/-- The part of the complete numerator which already factors through the
renewed antiresonant column. -/
noncomputable def suffixInteriorRenewalCorrectionReadout
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] sourceSoninCarrier lambda :=
  (Real.sqrt (ccm24PrimeEulerCoefficient p) : ℂ) •
    suffixActualBandRawPhysicalReducedRow owner lambda p S

/-- Exact same-object renewal split.  The second summand is already a bounded
readout of the final renewed Bone 1 denominator; no factor is commuted. -/
theorem signedCompressedInteriorOwner_eq_scalar_reducedColumn_add_correction
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    signedCompressedInteriorOwner owner lambda p S =
      (primeSchurMarkovScalar p : ℂ) •
        (suffixActualBandRawPhysicalReducedRow owner lambda p S ∘L
          newSuffixFrame lambda S) +
      suffixInteriorRenewalCorrectionReadout owner lambda p S ∘L
        suffixEulerFrameRenewedAntiresonantColumn lambda p S := by
  rw [signedCompressedInteriorOwner_eq_reducedRow_comp_inverseAdjoint_comp_newFrame]
  apply ContinuousLinearMap.ext
  intro x
  have hdeviation := DFunLike.congr_fun
    (primeEulerRenewalDeviation_eq_sqrtCoefficient_smul_lossAdjoint_comp_inverseAdjoint
      p) (newSuffixFrame lambda S x)
  have hsum :
      ContinuousLinearMap.adjoint (normalizedPrimeEulerInverse p)
          (newSuffixFrame lambda S x) =
        (primeSchurMarkovScalar p : ℂ) • newSuffixFrame lambda S x +
          (Real.sqrt (ccm24PrimeEulerCoefficient p) : ℂ) •
            ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p)
              (ContinuousLinearMap.adjoint (normalizedPrimeEulerInverse p)
                (newSuffixFrame lambda S x)) := by
    simp only [ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.comp_apply] at hdeviation
    calc
      ContinuousLinearMap.adjoint (normalizedPrimeEulerInverse p)
          (newSuffixFrame lambda S x) =
          (ContinuousLinearMap.adjoint (normalizedPrimeEulerInverse p)
              (newSuffixFrame lambda S x) -
            (primeSchurMarkovScalar p : ℂ) • newSuffixFrame lambda S x) +
          (primeSchurMarkovScalar p : ℂ) • newSuffixFrame lambda S x := by
        abel
      _ = (Real.sqrt (ccm24PrimeEulerCoefficient p) : ℂ) •
            ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p)
              (ContinuousLinearMap.adjoint (normalizedPrimeEulerInverse p)
                (newSuffixFrame lambda S x)) +
          (primeSchurMarkovScalar p : ℂ) • newSuffixFrame lambda S x := by
        rw [hdeviation]
      _ = (primeSchurMarkovScalar p : ℂ) • newSuffixFrame lambda S x +
          (Real.sqrt (ccm24PrimeEulerCoefficient p) : ℂ) •
            ContinuousLinearMap.adjoint (primeEulerAmbientLossFactor p)
              (ContinuousLinearMap.adjoint (normalizedPrimeEulerInverse p)
                (newSuffixFrame lambda S x)) := by
        abel
  simp only [suffixInteriorRenewalCorrectionReadout,
    suffixEulerFrameRenewedAntiresonantColumn,
    suffixEulerFrameSchurStep,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply]
  conv_lhs => rw [hsum]
  rw [map_add, map_smul, map_smul]

/-! ## Empty-suffix norm bounds -/

private theorem norm_threefold_le_of_contractions
    {E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    (left : G →L[ℂ] H) (middle : F →L[ℂ] G) (right : E →L[ℂ] F)
    (bound : ℝ) (hleft : ‖left‖ ≤ 1) (hmiddle : ‖middle‖ ≤ bound)
    (hright : ‖right‖ ≤ 1) (hbound : 0 ≤ bound) :
    ‖left ∘L middle ∘L right‖ ≤ bound := by
  calc
    ‖left ∘L middle ∘L right‖ ≤
        ‖left ∘L middle‖ * ‖right‖ :=
      ContinuousLinearMap.opNorm_comp_le (left ∘L middle) right
    _ ≤ (‖left‖ * ‖middle‖) * ‖right‖ := by
      exact mul_le_mul_of_nonneg_right
        (ContinuousLinearMap.opNorm_comp_le left middle) (norm_nonneg right)
    _ ≤ (1 * bound) * 1 :=
      mul_le_mul (mul_le_mul hleft hmiddle (norm_nonneg _) zero_le_one)
        hright (norm_nonneg _) (mul_nonneg zero_le_one hbound)
    _ = bound := by ring

/-- The one-prime reduced row is uniformly bounded before it is evaluated on
the new frame. -/
theorem norm_onePrime_reducedRow_le_twentyFour_mul_detector
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (hp : Nat.Prime p.1) :
    ‖suffixActualBandRawPhysicalReducedRow owner lambda p []‖ ≤
      24 * ‖detectorOperator owner‖ := by
  have hmoment :=
    norm_onePrimeRawCoframeBoundaryMoment_le_twentyFour_mul_detector
      owner lambda p (singlePrimeFamily p hp)
        (singlePrimeFamily_visiblePrimes p hp)
  have htransition :
      ‖-(suffixEulerFrameTransition lambda p [])†‖ ≤ (1 : ℝ) := by
    rw [ContinuousLinearMap.opNorm_neg]
    calc
      ‖(suffixEulerFrameTransition lambda p [])†‖ =
          ‖suffixEulerFrameTransition lambda p []‖ :=
        ContinuousLinearMap.adjoint.norm_map _
      _ ≤ 1 := suffixEulerFrameTransition_norm_le_one lambda p []
  have hold :
      ‖(suffixEulerFrameSchurStep lambda p []).oldFrame†‖ ≤ (1 : ℝ) := by
    calc
      ‖(suffixEulerFrameSchurStep lambda p []).oldFrame†‖ =
          ‖(suffixEulerFrameSchurStep lambda p []).oldFrame‖ :=
        ContinuousLinearMap.adjoint.norm_map _
      _ ≤ 1 := by
        change ‖oldSuffixFrame lambda p []‖ ≤ (1 : ℝ)
        simpa only [oldSuffixFrame] using
          newSuffixFrame_norm_le_one lambda [p]
  rw [
    suffixActualBandRawPhysicalReducedRow_cons_nil_eq_neg_transitionAdjoint_moment_oldFrameAdjoint]
  exact norm_threefold_le_of_contractions
    (-(suffixEulerFrameTransition lambda p [])†)
    (rawCoframeBoundaryMoment owner lambda
      (suffixActualBandForwardCoframe lambda [p])
      (suffixActualBandForwardEndpointCoframe lambda [p]))
    ((suffixEulerFrameSchurStep lambda p []).oldFrame†)
    (24 * ‖detectorOperator owner‖)
    htransition hmoment hold (by positivity)

/-- The correction readout gains one square root of the Euler coefficient. -/
theorem norm_onePrimeRenewalCorrectionReadout_nil_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (hp : Nat.Prime p.1) :
    ‖suffixInteriorRenewalCorrectionReadout owner lambda p []‖ ≤
      24 * Real.sqrt (ccm24PrimeEulerCoefficient p) *
        ‖detectorOperator owner‖ := by
  rw [suffixInteriorRenewalCorrectionReadout, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    Real.sqrt (ccm24PrimeEulerCoefficient p) *
        ‖suffixActualBandRawPhysicalReducedRow owner lambda p []‖ ≤
      Real.sqrt (ccm24PrimeEulerCoefficient p) *
        (24 * ‖detectorOperator owner‖) := by
      exact mul_le_mul_of_nonneg_left
        (norm_onePrime_reducedRow_le_twentyFour_mul_detector
          owner lambda p hp) (Real.sqrt_nonneg _)
    _ = 24 * Real.sqrt (ccm24PrimeEulerCoefficient p) *
        ‖detectorOperator owner‖ := by ring

/-- The complete renewed column has the other square-root Euler gain. -/
theorem norm_renewedAntiresonantColumn_le_two_sqrt_coefficient
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖suffixEulerFrameRenewedAntiresonantColumn lambda p S‖ ≤
      2 * Real.sqrt (ccm24PrimeEulerCoefficient p) := by
  have hloss : ‖(primeEulerAmbientLossFactor p)†‖ ≤
      2 * Real.sqrt (ccm24PrimeEulerCoefficient p) :=
    primeEulerAmbientLossFactor_adjoint_norm_le_two_sqrt_coefficient p
  have hinverse : ‖(normalizedPrimeEulerInverse p)†‖ ≤ (1 : ℝ) := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact norm_normalizedPrimeEulerInverse_le_one p
  have hframe : ‖newSuffixFrame lambda S‖ ≤ (1 : ℝ) :=
    newSuffixFrame_norm_le_one lambda S
  rw [suffixEulerFrameRenewedAntiresonantColumn]
  calc
    ‖((primeEulerAmbientLossFactor p)† ∘L
          (normalizedPrimeEulerInverse p)†) ∘L
        newSuffixFrame lambda S‖ ≤
      ‖(primeEulerAmbientLossFactor p)† ∘L
          (normalizedPrimeEulerInverse p)†‖ *
        ‖newSuffixFrame lambda S‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (‖(primeEulerAmbientLossFactor p)†‖ *
          ‖(normalizedPrimeEulerInverse p)†‖) *
        ‖newSuffixFrame lambda S‖ := by
      exact mul_le_mul_of_nonneg_right
        (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ ≤ ((2 * Real.sqrt (ccm24PrimeEulerCoefficient p)) * 1) * 1 := by
      exact mul_le_mul
        (mul_le_mul hloss hinverse (norm_nonneg _) (by positivity))
        hframe (norm_nonneg _) (by positivity)
    _ = 2 * Real.sqrt (ccm24PrimeEulerCoefficient p) := by ring

/-- The complete empty-suffix numerator gains the full Euler coefficient. -/
theorem norm_signedCompressedInteriorOwner_nil_le_twoHundredFortyFour_coefficient
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (hp : Nat.Prime p.1) :
    ‖signedCompressedInteriorOwner owner lambda p []‖ ≤
      244 * ccm24PrimeEulerCoefficient p * ‖detectorOperator owner‖ := by
  have hq : 0 ≤ ccm24PrimeEulerCoefficient p :=
    ccm24PrimeEulerCoefficient_nonneg p
  have hrho : 0 ≤ primeSchurMarkovScalar p :=
    (primeSchurMarkovScalar_pos p).le
  have hrhoOne : primeSchurMarkovScalar p ≤ 1 :=
    primeSchurMarkovScalar_le_one p
  have hfirst :
      ‖(primeSchurMarkovScalar p : ℂ) •
          (suffixActualBandRawPhysicalReducedRow owner lambda p [] ∘L
            newSuffixFrame lambda [])‖ ≤
        196 * ccm24PrimeEulerCoefficient p *
          ‖detectorOperator owner‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hrho]
    calc
      primeSchurMarkovScalar p *
          ‖suffixActualBandRawPhysicalReducedRow owner lambda p [] ∘L
            newSuffixFrame lambda []‖ ≤
        1 * (196 * ccm24PrimeEulerCoefficient p *
          ‖detectorOperator owner‖) := by
        exact mul_le_mul hrhoOne
          (norm_reducedRow_comp_newSuffixFrame_nil_le owner lambda p hp)
          (norm_nonneg _) zero_le_one
      _ = 196 * ccm24PrimeEulerCoefficient p *
          ‖detectorOperator owner‖ := by ring
  have hsecond :
      ‖suffixInteriorRenewalCorrectionReadout owner lambda p [] ∘L
          suffixEulerFrameRenewedAntiresonantColumn lambda p []‖ ≤
        48 * ccm24PrimeEulerCoefficient p *
          ‖detectorOperator owner‖ := by
    calc
      ‖suffixInteriorRenewalCorrectionReadout owner lambda p [] ∘L
          suffixEulerFrameRenewedAntiresonantColumn lambda p []‖ ≤
        ‖suffixInteriorRenewalCorrectionReadout owner lambda p []‖ *
          ‖suffixEulerFrameRenewedAntiresonantColumn lambda p []‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (24 * Real.sqrt (ccm24PrimeEulerCoefficient p) *
          ‖detectorOperator owner‖) *
        (2 * Real.sqrt (ccm24PrimeEulerCoefficient p)) := by
        exact mul_le_mul
          (norm_onePrimeRenewalCorrectionReadout_nil_le owner lambda p hp)
          (norm_renewedAntiresonantColumn_le_two_sqrt_coefficient lambda p [])
          (norm_nonneg _) (by positivity)
      _ = 48 * Real.sqrt (ccm24PrimeEulerCoefficient p) ^ 2 *
          ‖detectorOperator owner‖ := by ring
      _ = 48 * ccm24PrimeEulerCoefficient p *
          ‖detectorOperator owner‖ := by
        rw [Real.sq_sqrt hq]
  rw [signedCompressedInteriorOwner_eq_scalar_reducedColumn_add_correction]
  calc
    ‖(primeSchurMarkovScalar p : ℂ) •
          (suffixActualBandRawPhysicalReducedRow owner lambda p [] ∘L
            newSuffixFrame lambda []) +
        suffixInteriorRenewalCorrectionReadout owner lambda p [] ∘L
          suffixEulerFrameRenewedAntiresonantColumn lambda p []‖ ≤
      ‖(primeSchurMarkovScalar p : ℂ) •
          (suffixActualBandRawPhysicalReducedRow owner lambda p [] ∘L
            newSuffixFrame lambda [])‖ +
        ‖suffixInteriorRenewalCorrectionReadout owner lambda p [] ∘L
          suffixEulerFrameRenewedAntiresonantColumn lambda p []‖ :=
      norm_add_le _ _
    _ ≤ 196 * ccm24PrimeEulerCoefficient p *
          ‖detectorOperator owner‖ +
        48 * ccm24PrimeEulerCoefficient p *
          ‖detectorOperator owner‖ := add_le_add hfirst hsecond
    _ = 244 * ccm24PrimeEulerCoefficient p *
        ‖detectorOperator owner‖ := by ring

/-- Along the actual arithmetic primes, the complete empty-suffix numerator
itself tends to zero in operator norm. -/
theorem tendsto_norm_signedCompressedInteriorOwner_nil_arithmeticVisiblePrimeSequence
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    Filter.Tendsto
      (fun n =>
        ‖signedCompressedInteriorOwner owner lambda
          (arithmeticVisiblePrimeSequence n) []‖)
      Filter.atTop (nhds 0) := by
  have hcoefficient :=
    tendsto_ccm24PrimeEulerCoefficient_arithmeticVisiblePrimeSequence
  have hupper : ∀ n,
      ‖signedCompressedInteriorOwner owner lambda
          (arithmeticVisiblePrimeSequence n) []‖ ≤
        244 * ccm24PrimeEulerCoefficient
          (arithmeticVisiblePrimeSequence n) *
            ‖detectorOperator owner‖ := by
    intro n
    exact
      norm_signedCompressedInteriorOwner_nil_le_twoHundredFortyFour_coefficient
        owner lambda (arithmeticVisiblePrimeSequence n)
          (arithmeticVisiblePrimeSequence_isPrime n)
  have hlimit : Filter.Tendsto
      (fun n => 244 * ccm24PrimeEulerCoefficient
        (arithmeticVisiblePrimeSequence n) * ‖detectorOperator owner‖)
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero, zero_mul] using
      (hcoefficient.const_mul 244).mul_const ‖detectorOperator owner‖
  exact squeeze_zero (fun n => norm_nonneg _) hupper hlimit

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorOnePrimeNumeratorDecay
end CCM25Concrete
end Source
end ConnesWeilRH
