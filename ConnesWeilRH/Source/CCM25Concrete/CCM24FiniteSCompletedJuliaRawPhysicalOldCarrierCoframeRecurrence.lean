/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierLeakageExpansion
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSSchurPolarTelescoping

/-!
# Literal-list metric coframe recurrence

Proof 595 records the exact list-level polar readback needed by the Bone 1
survivor calculation.  It separates the scalar upper Euler factor, the
normalized ambient suffix product, the current polar frame, and the terminal
inverse-Gram square root.  The adjacent formula is algebraic; it is not a
uniform estimate of the physical signed row.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeRecurrence

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCausalMarkov
open CCM24FiniteSFixedSourcePolar
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSGramInverseCalculus
open CCM24FiniteSGramResponse
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawLocalTraceFactorization
open CCM24FiniteSSchurPolarTelescoping
open CCM24FiniteSTransportBounds

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Exact terminal polar readback on a literal list -/

noncomputable def suffixActualBandMetricCoframeSqrt
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda →L[ℂ]
      CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda :=
  parameterizedSoninGramInvSqrt lambda 1 S (by norm_num)

theorem suffixActualBandMetricCoframe_eq_transportAdjoint_comp_frame_inv
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixActualBandMetricCoframe lambda S =
      (suffixActualBandTransportOperator S)† ∘L
        suffixActualBandFrame lambda S ∘L
          suffixActualBandGramInv lambda S := by
  unfold suffixActualBandMetricCoframe suffixActualBandAmbientGram
  rw [suffixActualBandFrame_eq_transport_comp_inclusion]
  apply ContinuousLinearMap.ext
  intro x
  rfl

theorem suffixActualBandFrame_comp_metricCoframeSqrt_eq_newSuffixFrame
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixActualBandFrame lambda S ∘L
        suffixActualBandMetricCoframeSqrt lambda S =
      newSuffixFrame lambda S := by
  apply ContinuousLinearMap.ext
  intro x
  rfl

theorem suffixActualBandFrame_comp_gramInv_eq_newFrame_comp_metricCoframeSqrt
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixActualBandFrame lambda S ∘L suffixActualBandGramInv lambda S =
      newSuffixFrame lambda S ∘L
        suffixActualBandMetricCoframeSqrt lambda S := by
  apply ContinuousLinearMap.ext
  intro x
  have hsqrt := parameterizedSoninGramInvSqrt_mul_self
    lambda 1 S (by norm_num)
  have hsqrtPoint := congrArg
    (fun operator :
      CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda →L[ℂ]
        CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda => operator x) hsqrt
  simp only [ContinuousLinearMap.comp_apply] at hsqrtPoint
  change suffixActualBandFrame lambda S
      (parameterizedSoninGramInv lambda 1 S (by norm_num) x) =
    newSuffixFrame lambda S
      (suffixActualBandMetricCoframeSqrt lambda S x)
  rw [← hsqrtPoint]
  have hpolarPoint := congrArg
    (fun operator :
      CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda →L[ℂ]
        finiteSCarrier =>
      operator (suffixActualBandMetricCoframeSqrt lambda S x))
    (suffixActualBandFrame_comp_metricCoframeSqrt_eq_newSuffixFrame
      lambda S)
  simpa only [ContinuousLinearMap.comp_apply] using hpolarPoint

theorem suffixActualBandMetricCoframe_eq_upperFactor_schurPolarProduct
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    suffixActualBandMetricCoframe lambda S =
      (finiteEulerUpperFactor S : ℂ) •
        ((suffixEulerAmbientProduct S)† ∘L
          newSuffixFrame lambda S ∘L
            suffixActualBandMetricCoframeSqrt lambda S) := by
  rw [suffixActualBandMetricCoframe_eq_transportAdjoint_comp_frame_inv,
    suffixActualBandFrame_comp_gramInv_eq_newFrame_comp_metricCoframeSqrt]
  apply ContinuousLinearMap.ext
  intro x
  have hupper := upperFactor_smul_suffixEulerAmbientProduct_adjoint S
  have hpoint := congrArg
    (fun operator : finiteSCarrier →L[ℂ] finiteSCarrier =>
      operator (newSuffixFrame lambda S
        (suffixActualBandMetricCoframeSqrt lambda S x))) hupper
  simpa only [suffixActualBandTransportOperator,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, map_smul] using hpoint.symm

/-! ## Adjacent survivor and genuine boundary terms -/

theorem suffixActualBandMetricCoframe_cons_eq_survivor_add_boundary
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandMetricCoframe lambda (p :: S) =
      (finiteEulerUpperFactor (p :: S) : ℂ) •
        ((suffixEulerAmbientProduct S)† ∘L
          ((suffixEulerFrameSchurStep lambda p S).newFrame ∘L
              (suffixEulerFrameTransition lambda p S)† +
           (suffixEulerFrameSchurStep lambda p S).boundaryDagger) ∘L
          suffixActualBandMetricCoframeSqrt lambda (p :: S)) := by
  rw [suffixActualBandMetricCoframe_eq_upperFactor_schurPolarProduct]
  have hstep :=
    transportAdjoint_comp_oldFrame_eq_newFrame_add_boundaryDagger
      (suffixEulerFrameSchurStep lambda p S)
  have hstep' :
      (normalizedPrimeEulerFrameTransport p)† ∘L
          (suffixEulerFrameSchurStep lambda p S).oldFrame =
        (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
            (suffixEulerFrameTransition lambda p S)† +
          (suffixEulerFrameSchurStep lambda p S).boundaryDagger := by
    simpa only [suffixEulerFrameSchurStep] using hstep
  have hambient :
      suffixEulerAmbientProduct (p :: S) =
        normalizedPrimeEulerFrameTransport p ∘L
          suffixEulerAmbientProduct S := by
    rfl
  rw [hambient, ContinuousLinearMap.adjoint_comp]
  change (finiteEulerUpperFactor (p :: S) : ℂ) •
      ((suffixEulerAmbientProduct S)† ∘L
        (normalizedPrimeEulerFrameTransport p)† ∘L
          (suffixEulerFrameSchurStep lambda p S).oldFrame ∘L
            suffixActualBandMetricCoframeSqrt lambda (p :: S)) = _
  apply ContinuousLinearMap.ext
  intro x
  have hstepPoint := congrArg
    (fun operator :
      CCM24FiniteSFrameGramCalculus.sourceSoninCarrier lambda →L[ℂ]
        finiteSCarrier =>
      operator (suffixActualBandMetricCoframeSqrt lambda (p :: S) x)) hstep'
  have hreadoutPoint := congrArg
    (fun z : finiteSCarrier =>
      (finiteEulerUpperFactor (p :: S) : ℂ) •
        (ContinuousLinearMap.adjoint (suffixEulerAmbientProduct S)) z) hstepPoint
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply] using hreadoutPoint

theorem suffixActualBandForwardCoframe_cons
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    suffixActualBandForwardCoframe lambda (p :: S) =
      sourceBandProjection lambda ∘L
        normalizedFiniteEulerInverseList S ∘L
          normalizedPrimeEulerInverse p ∘L
            sourceInclusion lambda := by
  unfold suffixActualBandForwardCoframe
  rw [normalizedFiniteEulerInverseList_cons]
  simp only [ContinuousLinearMap.comp_assoc]

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeRecurrence
end CCM25Concrete
end Source
end ConnesWeilRH
