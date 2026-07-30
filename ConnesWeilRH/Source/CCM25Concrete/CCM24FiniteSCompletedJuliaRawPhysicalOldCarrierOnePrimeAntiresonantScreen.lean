/-
Copyright (c) 2026 Connes-WeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeAntiresonantReduction
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierMomentDecay

/-!
# One-prime antiresonant screen for Bone 1

Proof 608 shows that every Bone 1 factor forces divisibility of the reduced
row on the new-frame range by the ambient-loss column.  For the empty suffix,
the numerator in that quotient is exactly the one-prime boundary-moment
column followed by the contractive transition adjoint.

Proof 589 already bounds the whole boundary-moment column by `O(q_p)`.  The
results below transfer that operator-norm decay to the actual reduced row.
Consequently no uniformly bounded source sequence in this new-frame column
can produce a nondecaying-numerator obstruction.  This does not prove the
required quotient: the ambient-loss denominator may still decay faster.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierOnePrimeAntiresonantScreen

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierMomentDecay
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierMovingMomentColumnSelector
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierReduction
open CCM24FiniteSCompletedJuliaRawPhysicalOnePrimeMomentObstruction
open CCM24FiniteSCompletedJuliaRawPhysicalOnePrimeMomentReduction
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- Exact one-prime reduced-row column.  No norm estimate or scalar inverse is
used in this identity. -/
theorem reducedRow_comp_newSuffixFrame_nil_eq_neg_transitionAdjoint_comp_column
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime) :
    suffixActualBandRawPhysicalReducedRow owner lambda p [] ∘L
        newSuffixFrame lambda [] =
      -(suffixEulerFrameTransition lambda p [])† ∘L
        onePrimeBoundaryMomentColumn owner lambda p := by
  rw [suffixActualBandRawPhysicalReducedRow_cons_nil_eq_neg_transitionAdjoint_moment_oldFrameAdjoint]
  apply ContinuousLinearMap.ext
  intro x
  rfl

/-- The entire one-prime reduced-row column is `O(q_p)`, uniformly over its
source unit ball. -/
theorem norm_reducedRow_comp_newSuffixFrame_nil_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (hp : Nat.Prime p.1) :
    ‖suffixActualBandRawPhysicalReducedRow owner lambda p [] ∘L
        newSuffixFrame lambda []‖ ≤
      196 * ccm24PrimeEulerCoefficient p * ‖detectorOperator owner‖ := by
  rw [reducedRow_comp_newSuffixFrame_nil_eq_neg_transitionAdjoint_comp_column,
    ContinuousLinearMap.opNorm_neg]
  calc
    ‖(suffixEulerFrameTransition lambda p [])† ∘L
        onePrimeBoundaryMomentColumn owner lambda p‖ ≤
      ‖(suffixEulerFrameTransition lambda p [])†‖ *
        ‖onePrimeBoundaryMomentColumn owner lambda p‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖suffixEulerFrameTransition lambda p []‖ *
        ‖onePrimeBoundaryMomentColumn owner lambda p‖ := by
      exact congrArg
        (fun r : ℝ => r * ‖onePrimeBoundaryMomentColumn owner lambda p‖)
        (ContinuousLinearMap.adjoint.norm_map
          (suffixEulerFrameTransition lambda p []))
    _ ≤ 1 *
        (196 * ccm24PrimeEulerCoefficient p * ‖detectorOperator owner‖) := by
      exact mul_le_mul
        (suffixEulerFrameTransition_norm_le_one lambda p [])
        (norm_onePrimeBoundaryMomentColumn_le owner lambda p hp)
        (norm_nonneg _) zero_le_one
    _ = 196 * ccm24PrimeEulerCoefficient p * ‖detectorOperator owner‖ := by
      ring

/-- Along the genuine arithmetic-prime sequence, the operator norm of the
complete one-prime reduced-row new-frame column tends to zero. -/
theorem tendsto_reducedRow_comp_newSuffixFrame_nil_norm_arithmeticVisiblePrimeSequence
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    Filter.Tendsto
      (fun n =>
        ‖suffixActualBandRawPhysicalReducedRow owner lambda
            (arithmeticVisiblePrimeSequence n) [] ∘L
          newSuffixFrame lambda []‖)
      Filter.atTop (nhds 0) := by
  have hcoeff :=
    tendsto_ccm24PrimeEulerCoefficient_arithmeticVisiblePrimeSequence
  have hupper : ∀ n,
      ‖suffixActualBandRawPhysicalReducedRow owner lambda
          (arithmeticVisiblePrimeSequence n) [] ∘L
        newSuffixFrame lambda []‖ ≤
      196 * ccm24PrimeEulerCoefficient (arithmeticVisiblePrimeSequence n) *
        ‖detectorOperator owner‖ := by
    intro n
    exact norm_reducedRow_comp_newSuffixFrame_nil_le owner lambda
      (arithmeticVisiblePrimeSequence n)
      (arithmeticVisiblePrimeSequence_isPrime n)
  have hlimit : Filter.Tendsto
      (fun n =>
        196 * ccm24PrimeEulerCoefficient (arithmeticVisiblePrimeSequence n) *
          ‖detectorOperator owner‖)
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero, zero_mul] using
      (hcoeff.const_mul 196).mul_const ‖detectorOperator owner‖
  exact squeeze_zero (fun n => norm_nonneg _) hupper hlimit

/-- The preceding operator-norm convergence controls every uniformly bounded
moving source column. -/
theorem tendsto_reducedRow_newSuffixFrame_nil_norm_of_uniformly_bounded_source
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (x : ℕ → sourceSoninCarrier lambda) (sourceBound : ℝ)
    (hsourceBound : ∀ n, ‖x n‖ ≤ sourceBound) :
    Filter.Tendsto
      (fun n =>
        ‖suffixActualBandRawPhysicalReducedRow owner lambda
            (arithmeticVisiblePrimeSequence n) []
          (newSuffixFrame lambda [] (x n))‖)
      Filter.atTop (nhds 0) := by
  have hop :=
    tendsto_reducedRow_comp_newSuffixFrame_nil_norm_arithmeticVisiblePrimeSequence
      owner lambda
  have hupper : ∀ n,
      ‖suffixActualBandRawPhysicalReducedRow owner lambda
          (arithmeticVisiblePrimeSequence n) []
        (newSuffixFrame lambda [] (x n))‖ ≤
      ‖suffixActualBandRawPhysicalReducedRow owner lambda
          (arithmeticVisiblePrimeSequence n) [] ∘L
        newSuffixFrame lambda []‖ * sourceBound := by
    intro n
    calc
      _ ≤ ‖suffixActualBandRawPhysicalReducedRow owner lambda
              (arithmeticVisiblePrimeSequence n) [] ∘L
            newSuffixFrame lambda []‖ * ‖x n‖ :=
        (suffixActualBandRawPhysicalReducedRow owner lambda
            (arithmeticVisiblePrimeSequence n) [] ∘L
          newSuffixFrame lambda []).le_opNorm (x n)
      _ ≤ ‖suffixActualBandRawPhysicalReducedRow owner lambda
              (arithmeticVisiblePrimeSequence n) [] ∘L
            newSuffixFrame lambda []‖ * sourceBound := by
        exact mul_le_mul_of_nonneg_left (hsourceBound n) (norm_nonneg _)
  have hlimit : Filter.Tendsto
      (fun n =>
        ‖suffixActualBandRawPhysicalReducedRow owner lambda
            (arithmeticVisiblePrimeSequence n) [] ∘L
          newSuffixFrame lambda []‖ * sourceBound)
      Filter.atTop (nhds 0) := by
    simpa using hop.mul_const sourceBound
  exact squeeze_zero (fun n => norm_nonneg _) hupper hlimit

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierOnePrimeAntiresonantScreen
end CCM25Concrete
end Source
end ConnesWeilRH
