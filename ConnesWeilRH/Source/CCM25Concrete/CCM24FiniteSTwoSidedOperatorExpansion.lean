/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSForwardRenewal

/-!
# Operator-level two-sided finite Euler expansion

This module inserts the genuine transported-Sonin orthogonal projection
between the signed forward Euler adjoint and the causal inverse adjoint.  Each
atom remains `U_left P_target U_right`; the two translations are deliberately
not merged across the projection.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSTwoSidedOperatorExpansion

open scoped InnerProduct

open CC20Concrete
open _root_.ConnesWeilRH.CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSCausalSupport
open CCM24FiniteSInverseMetric
open CCM24FiniteSMultiRenewal
open CCM24FiniteSNormalizedCoframe
open CCM24FiniteSNormalizedCausalCoframe
open CCM24FiniteSForwardRenewal

noncomputable local instance targetTransportedSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    CompleteSpace (targetTransportedSoninCarrier lambda family) :=
  (transportedClosedSubmodule
    (ccm24FiniteEulerTransportEquiv family.visiblePrimes)
    (ccm24ArchimedeanSoninClosedSubspace lambda)).isClosed.completeSpace_coe

/-- The positive-displacement adjoint of one normalized inverse renewal
atom. -/
noncomputable def finiteEulerRenewalAdjointOperatorTerm
    (S : List CCM24VisiblePrime) (index : FiniteEulerRenewalIndex S) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  (finiteEulerRenewalWeight S index : ℂ) •
    (cc20GlobalLogTranslation
      (finiteEulerRenewalDisplacement S index)).toContinuousLinearMap

theorem norm_finiteEulerRenewalAdjointOperatorTerm_le
    (S : List CCM24VisiblePrime) (index : FiniteEulerRenewalIndex S) :
    ‖finiteEulerRenewalAdjointOperatorTerm S index‖ ≤
      finiteEulerRenewalWeight S index := by
  rw [finiteEulerRenewalAdjointOperatorTerm, norm_smul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (finiteEulerRenewalWeight_nonneg S index)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (cc20GlobalLogTranslation
      (finiteEulerRenewalDisplacement S index)).norm_toContinuousLinearMap_le
    (finiteEulerRenewalWeight_nonneg S index)

theorem summable_finiteEulerRenewalAdjointOperatorTerm
    (S : List CCM24VisiblePrime) :
    Summable (finiteEulerRenewalAdjointOperatorTerm S) := by
  exact Summable.of_norm_bounded
    (summable_finiteEulerRenewalWeight S)
    (norm_finiteEulerRenewalAdjointOperatorTerm_le S)

theorem normalizedFiniteEulerInverse_adjoint_eq_adjointTerms
    (family : FinitePrimePowerFamily) :
    (normalizedFiniteEulerInverse family)† =
      ∑' index : FiniteEulerRenewalIndex family.visiblePrimes,
        finiteEulerRenewalAdjointOperatorTerm family.visiblePrimes index := by
  exact normalizedFiniteEulerInverse_adjoint_eq_multiRenewalOperator family

theorem normalizedFiniteEulerInverse_adjoint_eq_lowerFactor
    (family : FinitePrimePowerFamily) :
    (normalizedFiniteEulerInverse family)† =
      (finiteEulerLowerFactor family.visiblePrimes : ℂ) •
        (finiteEulerInverseOperator family)† := by
  rw [normalizedFiniteEulerInverse]
  simp only [map_smulₛₗ, starRingEnd_apply]
  have hstar :
      star (finiteEulerLowerFactor family.visiblePrimes : ℂ) =
        (finiteEulerLowerFactor family.visiblePrimes : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  rw [hstar]

/-- The actual orthogonal projection onto the transported Sonin subspace. -/
noncomputable def transportedSoninProjection
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  targetTransportedSoninInclusion lambda family ∘L
    (targetTransportedSoninInclusion lambda family)†

/-- One exact two-sided sandwich atom. -/
noncomputable def finiteEulerProjectionSandwichTerm
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (forwardIndex : FiniteEulerForwardIndex family.visiblePrimes)
    (renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  finiteEulerForwardOperatorTerm family.visiblePrimes forwardIndex ∘L
    transportedSoninProjection lambda family ∘L
      finiteEulerRenewalAdjointOperatorTerm family.visiblePrimes renewalIndex

/-- For each fixed signed forward choice, the inverse-side sandwich series is
absolutely summable in operator norm. -/
theorem summable_finiteEulerProjectionSandwichTerm
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (forwardIndex : FiniteEulerForwardIndex family.visiblePrimes) :
    Summable (finiteEulerProjectionSandwichTerm lambda family forwardIndex) := by
  let C := ‖finiteEulerForwardOperatorTerm family.visiblePrimes forwardIndex‖ *
    ‖transportedSoninProjection lambda family‖
  apply Summable.of_norm_bounded
    ((summable_finiteEulerRenewalWeight family.visiblePrimes).mul_left C)
  intro renewalIndex
  calc
    ‖finiteEulerProjectionSandwichTerm lambda family forwardIndex
        renewalIndex‖ ≤
        ‖finiteEulerForwardOperatorTerm family.visiblePrimes forwardIndex‖ *
          ‖transportedSoninProjection lambda family ∘L
            finiteEulerRenewalAdjointOperatorTerm family.visiblePrimes
              renewalIndex‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖finiteEulerForwardOperatorTerm family.visiblePrimes forwardIndex‖ *
          (‖transportedSoninProjection lambda family‖ *
            ‖finiteEulerRenewalAdjointOperatorTerm family.visiblePrimes
              renewalIndex‖) := by
      exact mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ ≤ C * finiteEulerRenewalWeight family.visiblePrimes renewalIndex := by
      dsimp [C]
      calc
        _ ≤ ‖finiteEulerForwardOperatorTerm family.visiblePrimes
              forwardIndex‖ *
            (‖transportedSoninProjection lambda family‖ *
              finiteEulerRenewalWeight family.visiblePrimes renewalIndex) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (norm_finiteEulerRenewalAdjointOperatorTerm_le _ _)
              (norm_nonneg (transportedSoninProjection lambda family)))
            (norm_nonneg (finiteEulerForwardOperatorTerm
              family.visiblePrimes forwardIndex))
        _ = _ := by ring

/-- The normalized transported-Sonin covariance before source inclusion. -/
noncomputable def normalizedTransportedSoninCovariance
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  ((finiteEulerLowerFactor family.visiblePrimes : ℂ) •
      (finiteEulerTransportOperator family)†) ∘L
    transportedSoninProjection lambda family ∘L
      (normalizedFiniteEulerInverse family)†

set_option maxHeartbeats 800000 in
-- Elaborating the nested finite operator sum and Banach-space `tsum` requires
-- more than the default budget; the proof itself remains a direct continuity
-- argument with no automation search.
/-- Exact operator-norm expansion with the transported projection kept between
the left and right translations. -/
theorem normalizedTransportedSoninCovariance_eq_sum_tsum
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    normalizedTransportedSoninCovariance lambda family =
      ∑ forwardIndex : FiniteEulerForwardIndex family.visiblePrimes,
        ∑' renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes,
          finiteEulerProjectionSandwichTerm lambda family forwardIndex
            renewalIndex := by
  rw [normalizedTransportedSoninCovariance,
    normalizedFiniteEulerTransportAdjoint_eq_sum,
    normalizedFiniteEulerInverse_adjoint_eq_adjointTerms]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_sum', Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro forwardIndex _
  let F := finiteEulerForwardOperatorTerm family.visiblePrimes forwardIndex
  let P := transportedSoninProjection lambda family
  let R := finiteEulerRenewalAdjointOperatorTerm family.visiblePrimes
  have hR : Summable R :=
    summable_finiteEulerRenewalAdjointOperatorTerm family.visiblePrimes
  have hRu : Summable (fun index => R index u) :=
    (ContinuousLinearMap.apply ℂ finiteSCarrier u).summable hR
  have hPR : Summable (fun index => P (R index u)) :=
    P.summable hRu
  have hFPR : Summable (fun index => F (P (R index u))) :=
    F.summable hPR
  calc
    F (P ((∑' index, R index) u)) =
        F (P (∑' index, R index u)) := by
      change F (P ((ContinuousLinearMap.apply ℂ finiteSCarrier u)
        (∑' index, R index))) = _
      rw [(ContinuousLinearMap.apply ℂ finiteSCarrier u).map_tsum hR]
      apply congrArg F
      apply congrArg P
      apply tsum_congr
      intro index
      rfl
    _ = F (∑' index, P (R index u)) := by
      rw [P.map_tsum hRu]
    _ = ∑' index, F (P (R index u)) := by
      rw [F.map_tsum hPR]
    _ = (∑' renewalIndex,
          finiteEulerProjectionSandwichTerm lambda family forwardIndex
            renewalIndex) u := by
      change _ = (ContinuousLinearMap.apply ℂ finiteSCarrier u)
        (∑' renewalIndex,
          finiteEulerProjectionSandwichTerm lambda family forwardIndex
            renewalIndex)
      rw [(ContinuousLinearMap.apply ℂ finiteSCarrier u).map_tsum
        (summable_finiteEulerProjectionSandwichTerm lambda family
          forwardIndex)]
      apply tsum_congr
      intro renewalIndex
      rfl

/-- Read the operator expansion back as the normalized metric coframe. -/
theorem normalizedMetricCoframe_eq_projectionSandwichExpansion
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    CCM24FiniteSNormalizedCoframe.normalizedFiniteEulerMetricCoframe
        lambda family =
      (∑ forwardIndex : FiniteEulerForwardIndex family.visiblePrimes,
        ∑' renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes,
          finiteEulerProjectionSandwichTerm lambda family forwardIndex
            renewalIndex) ∘L sourceInclusion lambda := by
  rw [normalizedMetricCoframe_eq_causal_covariance,
    ← normalizedTransportedSoninCovariance_eq_sum_tsum]
  rw [normalizedTransportedSoninCovariance, transportedSoninProjection,
    normalizedFiniteEulerInverse_adjoint_eq_lowerFactor]
  apply ContinuousLinearMap.ext
  intro u
  rfl

end CCM24FiniteSTwoSidedOperatorExpansion
end CCM25Concrete
end Source
end ConnesWeilRH
