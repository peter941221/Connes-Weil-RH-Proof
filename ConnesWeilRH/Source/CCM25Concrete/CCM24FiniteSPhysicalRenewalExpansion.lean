/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSTwoSidedIndexBridge

/-!
# Full physical Gate 3U renewal expansion

The two-sided projection atoms are inserted into the completed physical
leakage and the selected detector response.  Outer, second-support, and
prolate pieces remain recombined through the exact source Sonin complement.
This is an operator identity only; it does not assert the still-missing scalar
compact-displacement cancellation.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSPhysicalRenewalExpansion

open scoped InnerProduct

open CC20Concrete
open _root_.ConnesWeilRH.CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSBandTrace
open CCM24FiniteSCoframeResponse
open CCM24FiniteSPhysicalLeakage
open CCM24FiniteSNormalizedCoframe
open CCM24FiniteSNormalizedPhysicalResponse
open CCM24FiniteSNormalizedCausalCoframe
open CCM24FiniteSMultiRenewal
open CCM24FiniteSForwardRenewal
open CCM24FiniteSTwoSidedOperatorExpansion

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- One complete physical leakage atom.  The source Sonin complement is the
already-recombined outer/second-support/prolate boundary owner. -/
noncomputable def finiteEulerPhysicalLeakageAtom
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (forwardIndex : FiniteEulerForwardIndex family.visiblePrimes)
    (renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  (ContinuousLinearMap.id ℂ finiteSCarrier -
      sourceSoninProjection lambda) ∘L
    finiteEulerProjectionSandwichTerm lambda family forwardIndex
      renewalIndex ∘L sourceInclusion lambda

/-- One complete selected-detector response atom on the source Sonin
carrier. -/
noncomputable def finiteEulerPhysicalResponseAtom
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (forwardIndex : FiniteEulerForwardIndex family.visiblePrimes)
    (renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  -((sourceInclusion lambda)†) ∘L detectorOperator owner ∘L
    finiteEulerPhysicalLeakageAtom lambda family forwardIndex renewalIndex

theorem summable_norm_finiteEulerPhysicalLeakageAtom
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (forwardIndex : FiniteEulerForwardIndex family.visiblePrimes) :
    Summable (fun renewalIndex =>
      ‖finiteEulerPhysicalLeakageAtom lambda family forwardIndex
        renewalIndex‖) := by
  let C := ‖ContinuousLinearMap.id ℂ finiteSCarrier -
      sourceSoninProjection lambda‖ *
    ‖finiteEulerForwardOperatorTerm family.visiblePrimes forwardIndex‖ *
    ‖transportedSoninProjection lambda family‖ * ‖sourceInclusion lambda‖
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
  · intro renewalIndex
    calc
      ‖finiteEulerPhysicalLeakageAtom lambda family forwardIndex renewalIndex‖ ≤
        ‖ContinuousLinearMap.id ℂ finiteSCarrier -
          sourceSoninProjection lambda‖ *
          ‖finiteEulerProjectionSandwichTerm lambda family forwardIndex
            renewalIndex ∘L sourceInclusion lambda‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖ContinuousLinearMap.id ℂ finiteSCarrier -
          sourceSoninProjection lambda‖ *
          (‖finiteEulerProjectionSandwichTerm lambda family forwardIndex
              renewalIndex‖ * ‖sourceInclusion lambda‖) := by
        exact mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
      _ ≤ C * finiteEulerRenewalWeight family.visiblePrimes renewalIndex := by
        dsimp [C]
        calc
          _ ≤ ‖ContinuousLinearMap.id ℂ finiteSCarrier -
              sourceSoninProjection lambda‖ *
            ((‖finiteEulerForwardOperatorTerm family.visiblePrimes
                forwardIndex‖ *
              (‖transportedSoninProjection lambda family‖ *
                finiteEulerRenewalWeight family.visiblePrimes renewalIndex)) *
              ‖sourceInclusion lambda‖) := by
            gcongr
            exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
              (mul_le_mul_of_nonneg_left
                (ContinuousLinearMap.opNorm_comp_le _ _)
                (norm_nonneg _))
              |>.trans
                (mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left
                    (norm_finiteEulerRenewalAdjointOperatorTerm_le _ _)
                    (norm_nonneg _))
                  (norm_nonneg _))
          _ = _ := by ring
  · exact (summable_finiteEulerRenewalWeight
      family.visiblePrimes).mul_left C

theorem summable_finiteEulerPhysicalLeakageAtom
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (forwardIndex : FiniteEulerForwardIndex family.visiblePrimes) :
    Summable (finiteEulerPhysicalLeakageAtom lambda family forwardIndex) :=
  Summable.of_norm
    (summable_norm_finiteEulerPhysicalLeakageAtom lambda family forwardIndex)

theorem summable_finiteEulerPhysicalResponseAtom
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (forwardIndex : FiniteEulerForwardIndex family.visiblePrimes) :
    Summable
      (finiteEulerPhysicalResponseAtom owner lambda family forwardIndex) := by
  let C := ‖(sourceInclusion lambda)†‖ * ‖detectorOperator owner‖
  apply Summable.of_norm_bounded
    ((summable_norm_finiteEulerPhysicalLeakageAtom lambda family
      forwardIndex).mul_left C)
  intro renewalIndex
  rw [finiteEulerPhysicalResponseAtom, norm_neg]
  calc
    _ ≤ ‖(sourceInclusion lambda)†‖ *
        ‖detectorOperator owner ∘L
          finiteEulerPhysicalLeakageAtom lambda family forwardIndex
            renewalIndex‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖(sourceInclusion lambda)†‖ *
        (‖detectorOperator owner‖ *
          ‖finiteEulerPhysicalLeakageAtom lambda family forwardIndex
            renewalIndex‖) := by
      exact mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ = C * ‖finiteEulerPhysicalLeakageAtom lambda family forwardIndex
          renewalIndex‖ := by dsimp [C]; ring

set_option maxHeartbeats 800000 in
-- The operator `tsum` is transported through two fixed boundary maps.
/-- Push the two fixed physical boundary maps through one inverse-renewal
series. -/
theorem physicalLeakageSeries_eq
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (forwardIndex : FiniteEulerForwardIndex family.visiblePrimes) :
    (ContinuousLinearMap.id ℂ finiteSCarrier -
        sourceSoninProjection lambda) ∘L
      (∑' renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes,
        finiteEulerProjectionSandwichTerm lambda family forwardIndex
          renewalIndex) ∘L sourceInclusion lambda =
      ∑' renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes,
          finiteEulerPhysicalLeakageAtom lambda family forwardIndex
          renewalIndex := by
  let C := ContinuousLinearMap.id ℂ finiteSCarrier -
    sourceSoninProjection lambda
  let J := sourceInclusion lambda
  let A := finiteEulerProjectionSandwichTerm lambda family forwardIndex
  let rightCompose :=
    (ContinuousLinearMap.compL ℂ (sourceSoninCarrier lambda)
      finiteSCarrier finiteSCarrier).flip J
  let leftCompose := ContinuousLinearMap.compL ℂ
    (sourceSoninCarrier lambda) finiteSCarrier finiteSCarrier C
  let transform := leftCompose ∘L rightCompose
  have hA : Summable A :=
    summable_finiteEulerProjectionSandwichTerm lambda family forwardIndex
  change transform (∑' renewalIndex, A renewalIndex) = _
  rw [transform.map_tsum hA]
  apply tsum_congr
  intro renewalIndex
  rfl

/-- Assemble the per-forward-choice physical series into the complete
normalized leakage. -/
theorem normalizedSourcePhysicalCoframeLeakage_eq_renewalExpansion
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    normalizedSourcePhysicalCoframeLeakage lambda family =
      ∑ forwardIndex : FiniteEulerForwardIndex family.visiblePrimes,
        ∑' renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes,
          finiteEulerPhysicalLeakageAtom lambda family forwardIndex
            renewalIndex := by
  rw [normalizedPhysicalLeakage_eq_causal_covariance,
    ← normalizedFiniteEulerInverse_adjoint_eq_lowerFactor]
  change (ContinuousLinearMap.id ℂ finiteSCarrier -
      sourceSoninProjection lambda) ∘L
      normalizedTransportedSoninCovariance lambda family ∘L
        sourceInclusion lambda = _
  rw [normalizedTransportedSoninCovariance_eq_sum_tsum]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_sum', Finset.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro forwardIndex _
  exact congrFun (congrArg DFunLike.coe
    (physicalLeakageSeries_eq lambda family forwardIndex)) u

set_option maxHeartbeats 800000 in
-- The operator `tsum` is transported through the detector and compression.
/-- Push the selected detector and source compression through one physical
renewal series. -/
theorem physicalResponseSeries_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (forwardIndex : FiniteEulerForwardIndex family.visiblePrimes) :
    -((sourceInclusion lambda)†) ∘L detectorOperator owner ∘L
      (∑' renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes,
        finiteEulerPhysicalLeakageAtom lambda family forwardIndex
          renewalIndex) =
      ∑' renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes,
          finiteEulerPhysicalResponseAtom owner lambda family forwardIndex
          renewalIndex := by
  let D := -((sourceInclusion lambda)†) ∘L detectorOperator owner
  let A := finiteEulerPhysicalLeakageAtom lambda family forwardIndex
  let transform := ContinuousLinearMap.compL ℂ
    (sourceSoninCarrier lambda) finiteSCarrier
      (sourceSoninCarrier lambda) D
  have hA : Summable A :=
    summable_finiteEulerPhysicalLeakageAtom lambda family forwardIndex
  change transform (∑' renewalIndex, A renewalIndex) = _
  rw [transform.map_tsum hA]
  apply tsum_congr
  intro renewalIndex
  rfl

/-- Assemble the complete selected-detector response without separating the
physical branches. -/
theorem normalizedSourceBandGramResponse_eq_renewalExpansion
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    normalizedSourceBandGramResponse owner lambda family =
      ∑ forwardIndex : FiniteEulerForwardIndex family.visiblePrimes,
        ∑' renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes,
          finiteEulerPhysicalResponseAtom owner lambda family forwardIndex
            renewalIndex := by
  rw [normalizedSourceBandGramResponse_eq_neg_physical_leakage,
    normalizedSourcePhysicalCoframeLeakage_eq_renewalExpansion]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.coe_sum', Finset.sum_apply, map_sum]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro forwardIndex _
  exact congrFun (congrArg DFunLike.coe
    (physicalResponseSeries_eq owner lambda family forwardIndex)) u

end CCM24FiniteSPhysicalRenewalExpansion
end CCM25Concrete
end Source
end ConnesWeilRH
