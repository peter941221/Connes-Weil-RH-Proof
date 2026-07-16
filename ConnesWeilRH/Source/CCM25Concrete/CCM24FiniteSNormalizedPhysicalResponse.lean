/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSNormalizedCoframe

/-!
# Normalized completed physical finite-S response

The two Euler lower factors are inserted into the completed
outer/second-support/prolate leakage before any norm is taken.  This gives a
uniform contraction for the normalized physical coframe and a uniform bound
for the correspondingly normalized source response.  It deliberately does
not divide by the lower factor and therefore does not assert Gate 3U.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSNormalizedPhysicalResponse

open scoped InnerProduct

open CC20Concrete
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSBandTrace
open CCM24FiniteSCoframeResponse
open CCM24FiniteSPhysicalLeakage
open CCM24FiniteSNormalizedCoframe

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The complete physical leakage after both Euler lower factors have been
inserted.  The three physical branches remain recombined. -/
noncomputable def normalizedSourcePhysicalCoframeLeakage
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  ((finiteEulerLowerFactor family.visiblePrimes : ℂ) ^ 2) •
    sourcePhysicalCoframeLeakage lambda family

theorem normalizedSourcePhysicalCoframeLeakage_eq_complement_comp
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    normalizedSourcePhysicalCoframeLeakage lambda family =
      (ContinuousLinearMap.id ℂ finiteSCarrier -
        sourceSoninProjection lambda) ∘L
          normalizedFiniteEulerMetricCoframe lambda family := by
  rw [normalizedSourcePhysicalCoframeLeakage,
    ← sourceSoninCoframeLeakage_eq_physical]
  apply ContinuousLinearMap.ext
  intro u
  simp only [sourceSoninCoframeLeakage,
    normalizedFiniteEulerMetricCoframe,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_smul]

theorem norm_sourceSoninComplement_le_one (lambda : CCM24SoninScale) :
    ‖ContinuousLinearMap.id ℂ finiteSCarrier -
        sourceSoninProjection lambda‖ ≤ 1 := by
  rw [sourceSoninProjection,
    ← Submodule.starProjection_orthogonal]
  exact Submodule.starProjection_norm_le _

/-- The normalized completed physical leakage is a contraction uniformly in
the visible finite set.  This is a bound on the recombined leakage, not on
its three summands. -/
theorem norm_normalizedSourcePhysicalCoframeLeakage_le_one
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    ‖normalizedSourcePhysicalCoframeLeakage lambda family‖ ≤ 1 := by
  rw [normalizedSourcePhysicalCoframeLeakage_eq_complement_comp]
  calc
    _ ≤ ‖ContinuousLinearMap.id ℂ finiteSCarrier -
          sourceSoninProjection lambda‖ *
        ‖normalizedFiniteEulerMetricCoframe lambda family‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul
      (norm_sourceSoninComplement_le_one lambda)
      (norm_normalizedFiniteEulerMetricCoframe_le_one lambda family)
      (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- The source response with both lower factors inserted before the physical
boundary pairing. -/
noncomputable def normalizedSourceBandGramResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  ((finiteEulerLowerFactor family.visiblePrimes : ℂ) ^ 2) •
    sourceBandGramResponse owner lambda family

theorem normalizedSourceBandGramResponse_eq_neg_physical_leakage
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    normalizedSourceBandGramResponse owner lambda family =
      -((sourceInclusion lambda)†) ∘L detectorOperator owner ∘L
        normalizedSourcePhysicalCoframeLeakage lambda family := by
  rw [normalizedSourceBandGramResponse,
    sourceBandGramResponse_eq_neg_physical_leakage]
  apply ContinuousLinearMap.ext
  intro u
  simp only [normalizedSourcePhysicalCoframeLeakage,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.neg_apply, map_smul, smul_neg]

/-- A uniform operator bound for the normalized completed response.  The
unnormalized Gate 3U response is not obtained by dividing this inequality by
the lower factor. -/
theorem norm_normalizedSourceBandGramResponse_le_detector
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    ‖normalizedSourceBandGramResponse owner lambda family‖ ≤
      ‖detectorOperator owner‖ := by
  rw [normalizedSourceBandGramResponse_eq_neg_physical_leakage]
  have hinclusion : ‖(sourceInclusion lambda)†‖ ≤ 1 := by
    have hadj : ‖(sourceInclusion lambda)†‖ = ‖sourceInclusion lambda‖ :=
      ContinuousLinearMap.adjoint.norm_map _
    rw [hadj]
    exact Submodule.norm_subtypeL_le _
  calc
    _ = ‖(sourceInclusion lambda)† ∘L detectorOperator owner ∘L
        normalizedSourcePhysicalCoframeLeakage lambda family‖ := by
      rw [norm_neg]
    _ ≤ ‖(sourceInclusion lambda)†‖ *
        ‖detectorOperator owner ∘L
          normalizedSourcePhysicalCoframeLeakage lambda family‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (‖detectorOperator owner‖ *
        ‖normalizedSourcePhysicalCoframeLeakage lambda family‖) := by
      exact mul_le_mul hinclusion
        (ContinuousLinearMap.opNorm_comp_le _ _)
        (norm_nonneg _) zero_le_one
    _ ≤ 1 * (‖detectorOperator owner‖ * 1) := by
      gcongr
      exact norm_normalizedSourcePhysicalCoframeLeakage_le_one lambda family
    _ = ‖detectorOperator owner‖ := by ring

end CCM24FiniteSNormalizedPhysicalResponse
end CCM25Concrete
end Source
end ConnesWeilRH
