/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSMultiRenewal

/-!
# Causal covariance factorization of the normalized finite-S coframe

The normalized metric coframe is factored through the actual orthogonal
projection onto the transported Sonin space and the adjoint of the normalized
causal inverse.  This connects the multi-prime renewal law to the completed
physical leakage without replacing the bounded-invertible transport by an
oblique projection.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSNormalizedCausalCoframe

open scoped InnerProduct

open CC20Concrete
open _root_.ConnesWeilRH.CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSCoframeResponse
open CCM24FiniteSPhysicalLeakage
open CCM24FiniteSInverseMetric
open CCM24FiniteSCausalSupport
open CCM24FiniteSNormalizedCoframe
open CCM24FiniteSNormalizedPhysicalResponse
open CCM24FiniteSCausalMarkov
open CCM24FiniteSMultiRenewal

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

noncomputable local instance targetTransportedSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    CompleteSpace (targetTransportedSoninCarrier lambda family) :=
  (transportedClosedSubmodule
    (ccm24FiniteEulerTransportEquiv family.visiblePrimes)
    (ccm24ArchimedeanSoninClosedSubspace lambda)).isClosed.completeSpace_coe

/-- The restricted inverse is literally the ambient inverse between the two
isometric inclusions. -/
theorem sourceInclusion_comp_restrictedInverse
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceInclusion lambda ∘L finiteEulerRestrictedInverse lambda family =
      finiteEulerInverseOperator family ∘L
        targetTransportedSoninInclusion lambda family := by
  let T := ccm24FiniteEulerTransportEquiv family.visiblePrimes
  let S := ccm24ArchimedeanSoninClosedSubspace lambda
  apply ContinuousLinearMap.ext
  intro u
  change (((restrictedClosedTransportEquiv T S).symm u :
      sourceSoninCarrier lambda) : finiteSCarrier) = T.symm u
  exact restrictedClosedTransportEquiv_symm_apply_coe T S u

/-- Adjoint readback of the exact restricted/ambient inverse square. -/
theorem restrictedInverseAdjoint_comp_sourceInclusionAdjoint
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (finiteEulerRestrictedInverse lambda family)† ∘L
        (sourceInclusion lambda)† =
      (targetTransportedSoninInclusion lambda family)† ∘L
        (finiteEulerInverseOperator family)† := by
  have h := congrArg ContinuousLinearMap.adjoint
    (sourceInclusion_comp_restrictedInverse lambda family)
  simpa only [ContinuousLinearMap.adjoint_comp] using h

/-- The restricted inverse adjoint is the ambient inverse adjoint, compressed
between the genuine source and transported Sonin inclusions. -/
theorem restrictedInverseAdjoint_eq_compressed_ambient
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (finiteEulerRestrictedInverse lambda family)† =
      (targetTransportedSoninInclusion lambda family)† ∘L
        (finiteEulerInverseOperator family)† ∘L sourceInclusion lambda := by
  calc
    (finiteEulerRestrictedInverse lambda family)† =
        (finiteEulerRestrictedInverse lambda family)† ∘L
          ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
      apply ContinuousLinearMap.ext
      intro u
      rfl
    _ = (finiteEulerRestrictedInverse lambda family)† ∘L
          ((sourceInclusion lambda)† ∘L sourceInclusion lambda) := by
      rw [sourceInclusion_adjoint_comp_self]
    _ = ((finiteEulerRestrictedInverse lambda family)† ∘L
          (sourceInclusion lambda)†) ∘L sourceInclusion lambda := by
      apply ContinuousLinearMap.ext
      intro u
      rfl
    _ = _ := by
      rw [restrictedInverseAdjoint_comp_sourceInclusionAdjoint]
      apply ContinuousLinearMap.ext
      intro u
      rfl

/-- The canonical dual frame is a transported-space orthogonal compression
of the ambient inverse adjoint. -/
theorem finiteEulerDualFrame_eq_transportProjection_comp_inverseAdjoint
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerDualFrame lambda family =
      targetTransportedSoninInclusion lambda family ∘L
        (targetTransportedSoninInclusion lambda family)† ∘L
          (finiteEulerInverseOperator family)† ∘L sourceInclusion lambda := by
  rw [finiteEulerDualFrame_eq_targetInclusion_comp_inverseAdjoint,
    restrictedInverseAdjoint_eq_compressed_ambient]

/-- Insert both lower factors into the exact causal covariance factorization.
No inverse lower factor appears. -/
theorem normalizedMetricCoframe_eq_causal_covariance
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    normalizedFiniteEulerMetricCoframe lambda family =
      ((finiteEulerLowerFactor family.visiblePrimes : ℂ) •
          (finiteEulerTransportOperator family)†) ∘L
        targetTransportedSoninInclusion lambda family ∘L
          (targetTransportedSoninInclusion lambda family)† ∘L
            ((finiteEulerLowerFactor family.visiblePrimes : ℂ) •
              (finiteEulerInverseOperator family)†) ∘L
                sourceInclusion lambda := by
  rw [normalizedFiniteEulerMetricCoframe,
    finiteEulerMetricCoframe_eq_transportAdjoint_comp_dualFrame,
    finiteEulerDualFrame_eq_transportProjection_comp_inverseAdjoint]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, map_smul, smul_smul]
  rw [pow_two]

/-- The completed physical leakage with the multi-renewal inverse adjoint kept
inside the transported Sonin covariance. -/
theorem normalizedPhysicalLeakage_eq_causal_covariance
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    normalizedSourcePhysicalCoframeLeakage lambda family =
      (ContinuousLinearMap.id ℂ finiteSCarrier -
          sourceSoninProjection lambda) ∘L
        ((finiteEulerLowerFactor family.visiblePrimes : ℂ) •
          (finiteEulerTransportOperator family)†) ∘L
        targetTransportedSoninInclusion lambda family ∘L
          (targetTransportedSoninInclusion lambda family)† ∘L
            ((finiteEulerLowerFactor family.visiblePrimes : ℂ) •
              (finiteEulerInverseOperator family)†) ∘L
                sourceInclusion lambda := by
  rw [normalizedSourcePhysicalCoframeLeakage_eq_complement_comp,
    normalizedMetricCoframe_eq_causal_covariance]

end CCM24FiniteSNormalizedCausalCoframe
end CCM25Concrete
end Source
end ConnesWeilRH
