/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSPhysicalLeakage
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSTransportBounds

/-!
# Uniformly normalized finite-S dual frame and metric coframe

The restricted Gram inverse is not estimated as an opaque operator.  It is
read back as `B B†`, where `B` is the inverse of the exact restricted Euler
equivalence.  This identifies the dual frame with the transported-subspace
inclusion followed by `B†`, and yields a condition-number-free coframe after
the scalar normalization is inserted before taking norms.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSNormalizedCoframe

open scoped InnerProduct

open CC20Concrete
open _root_.ConnesWeilRH.CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSCoframeResponse
open CCM24FiniteSCausalSupport
open CCM24FiniteSTransportBounds

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

noncomputable abbrev targetTransportedSoninCarrier
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :=
  (transportedClosedSubmodule
    (ccm24FiniteEulerTransportEquiv family.visiblePrimes)
    (ccm24ArchimedeanSoninClosedSubspace lambda)).toSubmodule

noncomputable local instance targetTransportedSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    CompleteSpace (targetTransportedSoninCarrier lambda family) :=
  (transportedClosedSubmodule
    (ccm24FiniteEulerTransportEquiv family.visiblePrimes)
    (ccm24ArchimedeanSoninClosedSubspace lambda)).isClosed.completeSpace_coe

/-- Inclusion of the exact transported Sonin subspace into the ambient
common-log carrier. -/
noncomputable def targetTransportedSoninInclusion
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    targetTransportedSoninCarrier lambda family →L[ℂ] finiteSCarrier :=
  (transportedClosedSubmodule
    (ccm24FiniteEulerTransportEquiv family.visiblePrimes)
    (ccm24ArchimedeanSoninClosedSubspace lambda)).toSubmodule.subtypeL

/-- Inverse of the exact restricted Euler equivalence. -/
noncomputable def finiteEulerRestrictedInverse
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    targetTransportedSoninCarrier lambda family →L[ℂ]
      sourceSoninCarrier lambda :=
  restrictedClosedTransportInverse
    (ccm24FiniteEulerTransportEquiv family.visiblePrimes)
    (ccm24ArchimedeanSoninClosedSubspace lambda)

/-- The dual frame is the transported-subspace inclusion followed by the
adjoint restricted inverse. -/
theorem finiteEulerDualFrame_eq_targetInclusion_comp_inverseAdjoint
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteEulerDualFrame lambda family =
      targetTransportedSoninInclusion lambda family ∘L
        (finiteEulerRestrictedInverse lambda family)† := by
  let T := ccm24FiniteEulerTransportEquiv family.visiblePrimes
  let S := ccm24ArchimedeanSoninClosedSubspace lambda
  let E := (restrictedClosedTransportEquiv T S).toContinuousLinearMap
  let B := restrictedClosedTransportInverse T S
  let J := (transportedClosedSubmodule T S).toSubmodule.subtypeL
  change restrictedClosedTransport T S ∘L
      (B ∘L B†) = J ∘L B†
  rw [restrictedClosedTransport_eq_subtype_comp_equiv]
  apply ContinuousLinearMap.ext
  intro u
  change J (E (B ((B†) u))) = J ((B†) u)
  exact congrArg J (by
    simp [E, B, restrictedClosedTransportInverse])

/-- The normalized restricted inverse is a contraction. -/
theorem norm_lowerFactor_smul_restrictedInverse_le_one
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    ‖(finiteEulerLowerFactor family.visiblePrimes : ℂ) •
        finiteEulerRestrictedInverse lambda family‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  have h := norm_lowerFactor_smul_finiteEulerInverse_le
    family.visiblePrimes (u : finiteSCarrier)
  simpa [finiteEulerRestrictedInverse, restrictedClosedTransportInverse] using h

theorem norm_lowerFactor_smul_restrictedInverseAdjoint_le_one
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    ‖(finiteEulerLowerFactor family.visiblePrimes : ℂ) •
        (finiteEulerRestrictedInverse lambda family)†‖ ≤ 1 := by
  have hadj : ‖(finiteEulerRestrictedInverse lambda family)†‖ =
      ‖finiteEulerRestrictedInverse lambda family‖ :=
    ContinuousLinearMap.adjoint.norm_map _
  calc
    _ = ‖(finiteEulerLowerFactor family.visiblePrimes : ℂ) •
        finiteEulerRestrictedInverse lambda family‖ := by
      rw [norm_smul, norm_smul, hadj]
    _ ≤ 1 := norm_lowerFactor_smul_restrictedInverse_le_one lambda family

/-- The lower-factor-normalized canonical dual frame is a contraction. -/
theorem norm_lowerFactor_smul_finiteEulerDualFrame_le_one
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    ‖(finiteEulerLowerFactor family.visiblePrimes : ℂ) •
        finiteEulerDualFrame lambda family‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [finiteEulerDualFrame_eq_targetInclusion_comp_inverseAdjoint]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
  have hinclude (v : targetTransportedSoninCarrier lambda family) :
      ‖targetTransportedSoninInclusion lambda family v‖ = ‖v‖ := rfl
  rw [norm_smul, hinclude]
  calc
    _ = ‖((finiteEulerLowerFactor family.visiblePrimes : ℂ) •
        (finiteEulerRestrictedInverse lambda family)†) u‖ := by
      rw [ContinuousLinearMap.smul_apply, norm_smul]
    _ ≤ ‖(finiteEulerLowerFactor family.visiblePrimes : ℂ) •
          (finiteEulerRestrictedInverse lambda family)†‖ * ‖u‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖u‖ := by
      exact mul_le_mul_of_nonneg_right
        (norm_lowerFactor_smul_restrictedInverseAdjoint_le_one lambda family)
        (norm_nonneg u)

/-!
The same lower-factor normalization is a contraction on the forward frame.
This is the frame-side half of the paired gauge; it is not a bound on the
completed response and is never used to split its signed crossings.
-/
theorem norm_lowerFactor_smul_finiteEulerFrame_le_one
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    ‖(finiteEulerLowerFactor family.visiblePrimes : ℂ) •
        finiteEulerFrame lambda family‖ ≤ 1 := by
  have htransport :
      ‖(finiteEulerLowerFactor family.visiblePrimes : ℂ) •
          finiteEulerTransportOperator family‖ ≤ 1 := by
    have hnorm :
        ‖(finiteEulerLowerFactor family.visiblePrimes : ℂ) •
            finiteEulerTransportOperator family‖ =
          ‖(finiteEulerLowerFactor family.visiblePrimes : ℂ) •
            (finiteEulerTransportOperator family)†‖ := by
      rw [norm_smul, norm_smul, ContinuousLinearMap.adjoint.norm_map]
    rw [hnorm]
    exact norm_lowerFactor_smul_finiteEulerTransportAdjoint_le_one
      family.visiblePrimes
  have hinclusion : ‖sourceInclusion lambda‖ ≤ 1 := by
    exact Submodule.norm_subtypeL_le _
  have hfactor :
      (finiteEulerLowerFactor family.visiblePrimes : ℂ) •
          finiteEulerFrame lambda family =
        ((finiteEulerLowerFactor family.visiblePrimes : ℂ) •
          finiteEulerTransportOperator family) ∘L
            sourceInclusion lambda := by
    rw [finiteEulerFrame_eq_transport_comp_inclusion]
    apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, map_smul]
    rfl
  rw [hfactor]
  calc
    _ ≤ ‖(finiteEulerLowerFactor family.visiblePrimes : ℂ) •
          finiteEulerTransportOperator family‖ *
        ‖sourceInclusion lambda‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul htransport hinclusion
      (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- Insert both lower factors before estimating the metric coframe. -/
noncomputable def normalizedFiniteEulerMetricCoframe
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  ((finiteEulerLowerFactor family.visiblePrimes : ℂ) ^ 2) •
    finiteEulerMetricCoframe lambda family

theorem normalizedMetricCoframe_eq_normalized_factors
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    normalizedFiniteEulerMetricCoframe lambda family =
      ((finiteEulerLowerFactor family.visiblePrimes : ℂ) •
          (finiteEulerTransportOperator family)†) ∘L
        ((finiteEulerLowerFactor family.visiblePrimes : ℂ) •
          finiteEulerDualFrame lambda family) := by
  rw [normalizedFiniteEulerMetricCoframe,
    finiteEulerMetricCoframe_eq_transportAdjoint_comp_dualFrame]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    map_smul]
  module

/-- The fully normalized metric coframe has an operator norm bound independent
of the visible finite set. -/
theorem norm_normalizedFiniteEulerMetricCoframe_le_one
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    ‖normalizedFiniteEulerMetricCoframe lambda family‖ ≤ 1 := by
  rw [normalizedMetricCoframe_eq_normalized_factors]
  calc
    _ ≤ ‖(finiteEulerLowerFactor family.visiblePrimes : ℂ) •
          (finiteEulerTransportOperator family)†‖ *
        ‖(finiteEulerLowerFactor family.visiblePrimes : ℂ) •
          finiteEulerDualFrame lambda family‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul
      (norm_lowerFactor_smul_finiteEulerTransportAdjoint_le_one
        family.visiblePrimes)
      (norm_lowerFactor_smul_finiteEulerDualFrame_le_one lambda family)
      (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

end CCM24FiniteSNormalizedCoframe
end CCM25Concrete
end Source
end ConnesWeilRH
