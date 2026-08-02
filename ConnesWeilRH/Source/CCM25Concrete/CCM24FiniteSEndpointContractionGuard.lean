/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCombinedCoframeGuard
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSEmptyPhysicalReadout
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSPhysicalLeakage

/-!
# Lower bound forced by endpoint biorthogonality

The combined endpoint coframe is a right inverse to the source inclusion
adjoint. Consequently its operator norm cannot be below one.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSEndpointContractionGuard

open CC20Concrete
open CCM24FiniteSCombinedCoframeGuard
open CCM24FiniteSGramResponse
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawRemainderCommonPair
open CCM24FiniteSEmptyPhysicalReadout
open CCM24FiniteSPhysicalLeakage

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (CCM24FiniteSGramResponse.sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

theorem one_le_norm_sourceActualBandForwardEndpointCoframe
    (lambda : CCM24SoninScale)
    (family : CCM24FiniteSProjectionTrace.FinitePrimePowerFamily)
    [Nontrivial (CCM24FiniteSGramResponse.sourceSoninCarrier lambda)] :
    1 ≤ ‖sourceActualBandForwardEndpointCoframe lambda family‖ := by
  have hright :=
    sourceInclusionAdjoint_comp_sourceActualBandForwardEndpointCoframe
      lambda family
  have hid : ‖(ContinuousLinearMap.id ℂ
      (CCM24FiniteSGramResponse.sourceSoninCarrier lambda))‖ = 1 := by
    exact ContinuousLinearMap.norm_id
  have hadj : ‖ContinuousLinearMap.adjoint
      (CCM24FiniteSGramResponse.sourceInclusion lambda)‖ ≤ 1 := by
    calc
      ‖ContinuousLinearMap.adjoint
          (CCM24FiniteSGramResponse.sourceInclusion lambda)‖ =
          ‖CCM24FiniteSGramResponse.sourceInclusion lambda‖ :=
        ContinuousLinearMap.adjoint.norm_map _
      _ ≤ 1 := Submodule.norm_subtypeL_le _
  have hcomp :
      ‖(ContinuousLinearMap.id ℂ
          (CCM24FiniteSGramResponse.sourceSoninCarrier lambda))‖ ≤
        ‖ContinuousLinearMap.adjoint
            (CCM24FiniteSGramResponse.sourceInclusion lambda)‖ *
          ‖sourceActualBandForwardEndpointCoframe lambda family‖ := by
    rw [← hright]
    exact ContinuousLinearMap.opNorm_comp_le _ _
  rw [hid] at hcomp
  nlinarith [mul_le_mul_of_nonneg_right hadj
    (norm_nonneg (sourceActualBandForwardEndpointCoframe lambda family))]

theorem norm_sourceActualBandForwardEndpointCoframe_eq_one_of_visiblePrimes_nil
    (lambda : CCM24SoninScale)
    (family : CCM24FiniteSProjectionTrace.FinitePrimePowerFamily)
    (hfamily : family.visiblePrimes = [])
    [Nontrivial (CCM24FiniteSGramResponse.sourceSoninCarrier lambda)] :
    ‖sourceActualBandForwardEndpointCoframe lambda family‖ = 1 := by
  rw [sourceActualBandForwardEndpointCoframe,
    sourceActualBandForwardCoframe_eq_zero_of_visiblePrimes_nil lambda family
      hfamily,
    finiteEulerMetricCoframe_eq_sourceInclusion_of_visiblePrimes_nil lambda
      family hfamily,
    zero_add]
  exact Submodule.norm_subtypeL
    (ccm24ArchimedeanSoninClosedSubspace lambda).toSubmodule

/-! ## The sharp endpoint obstruction -/

/- The endpoint is a right inverse to the adjoint inclusion.  Therefore a
   contraction bound would force equality with the inclusion itself.  This is
   stronger than a generic norm estimate: it kills the complete off-Sonin
   leakage. -/
theorem sourceActualBandForwardEndpointCoframe_eq_inclusion_of_norm_le_one
    (lambda : CCM24SoninScale)
    (family : CCM24FiniteSProjectionTrace.FinitePrimePowerFamily)
    (hendpoint :
      ‖sourceActualBandForwardEndpointCoframe lambda family‖ ≤ 1) :
    sourceActualBandForwardEndpointCoframe lambda family =
      CCM24FiniteSGramResponse.sourceInclusion lambda := by
  apply ContinuousLinearMap.ext
  intro u
  have hright :=
    congrArg
      (fun operator : CCM24FiniteSGramResponse.sourceSoninCarrier lambda →L[ℂ]
          CCM24FiniteSGramResponse.sourceSoninCarrier lambda => operator u)
      (sourceInclusionAdjoint_comp_sourceActualBandForwardEndpointCoframe
        lambda family)
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] at hright
  have hadj : ‖ContinuousLinearMap.adjoint
      (CCM24FiniteSGramResponse.sourceInclusion lambda)‖ ≤ 1 := by
    calc
      ‖ContinuousLinearMap.adjoint
          (CCM24FiniteSGramResponse.sourceInclusion lambda)‖ =
          ‖CCM24FiniteSGramResponse.sourceInclusion lambda‖ :=
        ContinuousLinearMap.adjoint.norm_map _
      _ ≤ 1 := Submodule.norm_subtypeL_le _
  have hlower : ‖u‖ ≤
      ‖sourceActualBandForwardEndpointCoframe lambda family u‖ := by
    calc
      ‖u‖ = ‖ContinuousLinearMap.adjoint
          (CCM24FiniteSGramResponse.sourceInclusion lambda)
          (sourceActualBandForwardEndpointCoframe lambda family u)‖ := by
        rw [hright]
      _ ≤ ‖ContinuousLinearMap.adjoint
          (CCM24FiniteSGramResponse.sourceInclusion lambda)‖ *
          ‖sourceActualBandForwardEndpointCoframe lambda family u‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 *
          ‖sourceActualBandForwardEndpointCoframe lambda family u‖ := by
        exact mul_le_mul_of_nonneg_right hadj (norm_nonneg _)
      _ = ‖sourceActualBandForwardEndpointCoframe lambda family u‖ :=
        one_mul _
  have hupper :
      ‖sourceActualBandForwardEndpointCoframe lambda family u‖ ≤ ‖u‖ := by
    calc
      ‖sourceActualBandForwardEndpointCoframe lambda family u‖ ≤
          ‖sourceActualBandForwardEndpointCoframe lambda family‖ * ‖u‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖u‖ := by
        exact mul_le_mul_of_nonneg_right hendpoint (norm_nonneg _)
      _ = ‖u‖ := one_mul _
  have hnorm :
      ‖sourceActualBandForwardEndpointCoframe lambda family u‖ = ‖u‖ :=
    le_antisymm hupper hlower
  have hprojection :
      sourceSoninProjection lambda
          (sourceActualBandForwardEndpointCoframe lambda family u) =
        CCM24FiniteSGramResponse.sourceInclusion lambda u := by
    have h := congrArg
      (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier =>
        operator (sourceActualBandForwardEndpointCoframe lambda family u))
      (sourceInclusion_comp_adjoint lambda)
    simpa only [ContinuousLinearMap.comp_apply] using h.symm.trans
      (congrArg
        (fun x : CCM24FiniteSGramResponse.sourceSoninCarrier lambda =>
          CCM24FiniteSGramResponse.sourceInclusion lambda x)
        hright)
  have hprojectionNorm :
      ‖sourceSoninProjection lambda
          (sourceActualBandForwardEndpointCoframe lambda family u)‖ =
        ‖sourceActualBandForwardEndpointCoframe lambda family u‖ := by
    rw [hprojection]
    have hJnorm :
        ‖CCM24FiniteSGramResponse.sourceInclusion lambda u‖ = ‖u‖ := by
      change ‖(u : finiteSCarrier)‖ = ‖u‖
      rfl
    exact hJnorm.trans hnorm.symm
  have hmem :
      sourceActualBandForwardEndpointCoframe lambda family u ∈
        (ccm24ArchimedeanSoninClosedSubspace lambda).toSubmodule := by
    apply (Submodule.mem_iff_norm_starProjection
      (ccm24ArchimedeanSoninClosedSubspace lambda).toSubmodule
      (sourceActualBandForwardEndpointCoframe lambda family u)).mpr
    exact hprojectionNorm
  have hprojectionSelf :
      sourceSoninProjection lambda
          (sourceActualBandForwardEndpointCoframe lambda family u) =
        sourceActualBandForwardEndpointCoframe lambda family u := by
    change (ccm24ArchimedeanSoninClosedSubspace lambda).toSubmodule.starProjection
        (sourceActualBandForwardEndpointCoframe lambda family u) = _
    exact Submodule.starProjection_eq_self_iff.mpr hmem
  exact hprojectionSelf.symm.trans hprojection

theorem sourceActualBandCombinedCoframeLeakage_eq_zero_of_norm_endpoint_le_one
    (lambda : CCM24SoninScale)
    (family : CCM24FiniteSProjectionTrace.FinitePrimePowerFamily)
    (hendpoint :
      ‖sourceActualBandForwardEndpointCoframe lambda family‖ ≤ 1) :
    sourceActualBandCombinedCoframeLeakage lambda family = 0 := by
  rw [sourceActualBandCombinedCoframeLeakage_eq_combined_sub_inclusion,
    sourceActualBandForwardEndpointCoframe_eq_inclusion_of_norm_le_one
      lambda family hendpoint]
  exact sub_self _

/-- Zero complete leakage is exactly the statement that the endpoint has
collapsed back to the source inclusion. -/
theorem sourceActualBandForwardEndpointCoframe_eq_inclusion_of_combined_leakage_eq_zero
    (lambda : CCM24SoninScale)
    (family : CCM24FiniteSProjectionTrace.FinitePrimePowerFamily)
    (hleakage : sourceActualBandCombinedCoframeLeakage lambda family = 0) :
    sourceActualBandForwardEndpointCoframe lambda family =
      CCM24FiniteSGramResponse.sourceInclusion lambda := by
  rw [sourceActualBandForwardEndpointCoframe_eq_inclusion_add_leakage,
    hleakage, add_zero]

/-- The endpoint is contractive if and only if its complete off-Sonin leakage
vanishes.  This keeps the Proof 717 producer target as one coherent object. -/
theorem norm_sourceActualBandForwardEndpointCoframe_le_one_iff_combined_leakage_eq_zero
    (lambda : CCM24SoninScale)
    (family : CCM24FiniteSProjectionTrace.FinitePrimePowerFamily) :
    ‖sourceActualBandForwardEndpointCoframe lambda family‖ ≤ 1 ↔
      sourceActualBandCombinedCoframeLeakage lambda family = 0 := by
  constructor
  · exact sourceActualBandCombinedCoframeLeakage_eq_zero_of_norm_endpoint_le_one
      lambda family
  · intro hleakage
    rw [sourceActualBandForwardEndpointCoframe_eq_inclusion_of_combined_leakage_eq_zero
      lambda family hleakage]
    exact Submodule.norm_subtypeL_le _

/-- In a nonzero source carrier, zero complete leakage makes the endpoint norm
exactly one, not merely at most one. -/
theorem norm_sourceActualBandForwardEndpointCoframe_eq_one_of_combined_leakage_eq_zero
    (lambda : CCM24SoninScale)
    (family : CCM24FiniteSProjectionTrace.FinitePrimePowerFamily)
    [Nontrivial (CCM24FiniteSGramResponse.sourceSoninCarrier lambda)]
    (hleakage : sourceActualBandCombinedCoframeLeakage lambda family = 0) :
    ‖sourceActualBandForwardEndpointCoframe lambda family‖ = 1 := by
  rw [sourceActualBandForwardEndpointCoframe_eq_inclusion_of_combined_leakage_eq_zero
    lambda family hleakage]
  exact Submodule.norm_subtypeL
    (ccm24ArchimedeanSoninClosedSubspace lambda).toSubmodule

/-! ## Physical same-object normal form -/

/-- The complete endpoint leakage is exactly the raw forward coframe plus the
physical outer/second-support/prolate leakage.  This is an identity of the
whole operator; no branchwise norm or trace estimate is introduced. -/
theorem sourceActualBandCombinedCoframeLeakage_eq_forward_add_physicalLeakage
    (lambda : CCM24SoninScale)
    (family : CCM24FiniteSProjectionTrace.FinitePrimePowerFamily) :
    sourceActualBandCombinedCoframeLeakage lambda family =
      sourceActualBandForwardCoframe lambda family +
        sourcePhysicalCoframeLeakage lambda family := by
  rw [sourceActualBandCombinedCoframeLeakage_eq_forward_add_metricLeakage,
    sourceSoninCoframeLeakage_eq_physical]

/-- The endpoint contraction target in Proof 717 is equivalently a single
same-object cancellation equation on the forward plus physical leakage. -/
theorem norm_sourceActualBandForwardEndpointCoframe_le_one_iff_forward_add_physicalLeakage_eq_zero
    (lambda : CCM24SoninScale)
    (family : CCM24FiniteSProjectionTrace.FinitePrimePowerFamily) :
    ‖sourceActualBandForwardEndpointCoframe lambda family‖ ≤ 1 ↔
      sourceActualBandForwardCoframe lambda family +
          sourcePhysicalCoframeLeakage lambda family = 0 := by
  rw [norm_sourceActualBandForwardEndpointCoframe_le_one_iff_combined_leakage_eq_zero,
    sourceActualBandCombinedCoframeLeakage_eq_forward_add_physicalLeakage]

/-! ## Exact pointwise energy ledger -/

/-- The endpoint carries the source energy and the complete off-Sonin energy
in orthogonal channels.  No branchwise triangle estimate is used. -/
theorem norm_sq_sourceActualBandForwardEndpointCoframe_apply_eq_source_add_leakage
    (lambda : CCM24SoninScale)
    (family : CCM24FiniteSProjectionTrace.FinitePrimePowerFamily)
    (u : CCM24FiniteSGramResponse.sourceSoninCarrier lambda) :
    ‖sourceActualBandForwardEndpointCoframe lambda family u‖ ^ 2 =
      ‖u‖ ^ 2 +
        ‖sourceActualBandCombinedCoframeLeakage lambda family u‖ ^ 2 := by
  let S := (ccm24ArchimedeanSoninClosedSubspace lambda).toSubmodule
  have hpyth := S.norm_sq_eq_add_norm_sq_starProjection
    (sourceActualBandForwardEndpointCoframe lambda family u)
  rw [Submodule.starProjection_orthogonal] at hpyth
  have hprojection := congrArg
    (fun T : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier => T u)
    (sourceSoninProjection_comp_sourceActualBandForwardEndpointCoframe
      lambda family)
  have hleakage :
      (ContinuousLinearMap.id ℂ finiteSCarrier - sourceSoninProjection lambda)
          (sourceActualBandForwardEndpointCoframe lambda family u) =
        sourceActualBandCombinedCoframeLeakage lambda family u := by
    rfl
  have hprojection' :
      S.starProjection
          (sourceActualBandForwardEndpointCoframe lambda family u) =
        sourceInclusion lambda u := by
    simpa only [ContinuousLinearMap.comp_apply] using hprojection
  have hleakage' :
      (ContinuousLinearMap.id ℂ finiteSCarrier - S.starProjection)
          (sourceActualBandForwardEndpointCoframe lambda family u) =
        sourceActualBandCombinedCoframeLeakage lambda family u := by
    simpa only [S, sourceSoninProjection] using hleakage
  rw [hprojection', hleakage'] at hpyth
  have hJnorm :
      ‖CCM24FiniteSGramResponse.sourceInclusion lambda u‖ = ‖u‖ := by
    change ‖(u : finiteSCarrier)‖ = ‖u‖
    rfl
  rw [hJnorm] at hpyth
  exact hpyth

/-- Operator-level Gram form of the pointwise ledger.  The leakage is a
positive correction to the identity; it is kept as one complete object. -/
theorem sourceActualBandForwardEndpointCoframe_adjoint_comp_self_eq_id_add_leakage
    (lambda : CCM24SoninScale)
    (family : CCM24FiniteSProjectionTrace.FinitePrimePowerFamily) :
    ContinuousLinearMap.adjoint
        (sourceActualBandForwardEndpointCoframe lambda family) ∘L
        sourceActualBandForwardEndpointCoframe lambda family =
      ContinuousLinearMap.id ℂ (CCM24FiniteSGramResponse.sourceSoninCarrier lambda) +
        ContinuousLinearMap.adjoint
          (sourceActualBandCombinedCoframeLeakage lambda family) ∘L
          sourceActualBandCombinedCoframeLeakage lambda family := by
  let J := CCM24FiniteSGramResponse.sourceInclusion lambda
  let D := sourceActualBandForwardEndpointCoframe lambda family
  let L := sourceActualBandCombinedCoframeLeakage lambda family
  have hD : D = J + L := by
    simpa only [D, J, L] using
      sourceActualBandForwardEndpointCoframe_eq_inclusion_add_leakage
        lambda family
  have hcross : ContinuousLinearMap.adjoint J ∘L L = 0 := by
    simpa only [J, L] using
      sourceInclusionAdjoint_comp_sourceActualBandCombinedCoframeLeakage_eq_zero
        lambda family
  have hadjoint_add (A B : CCM24FiniteSGramResponse.sourceSoninCarrier lambda →L[ℂ]
      finiteSCarrier) :
      ContinuousLinearMap.adjoint (A + B) =
        ContinuousLinearMap.adjoint A + ContinuousLinearMap.adjoint B := by
    apply ContinuousLinearMap.ext
    intro y
    exact ext_inner_right ℂ fun z => by
      simp only [ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.add_apply, inner_add_left, inner_add_right]
  have hcrossAdj : ContinuousLinearMap.adjoint L ∘L J = 0 := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_right ℂ
    intro y
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.zero_apply]
    rw [ContinuousLinearMap.adjoint_inner_left]
    rw [← ContinuousLinearMap.adjoint_inner_right]
    have hz := congrArg (fun T :
        CCM24FiniteSGramResponse.sourceSoninCarrier lambda →L[ℂ]
          CCM24FiniteSGramResponse.sourceSoninCarrier lambda => T y) hcross
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.zero_apply] at hz
    rw [hz]
    simp
  change ContinuousLinearMap.adjoint D ∘L D =
    ContinuousLinearMap.id ℂ (CCM24FiniteSGramResponse.sourceSoninCarrier lambda) +
      ContinuousLinearMap.adjoint L ∘L L
  rw [hD, hadjoint_add]
  simp only [ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp]
  rw [hcross, hcrossAdj,
    CCM24FiniteSGramResponse.sourceInclusion_adjoint_comp_self]
  simp only [zero_add, add_zero]

end CCM24FiniteSEndpointContractionGuard
end CCM25Concrete
end Source
end ConnesWeilRH
