/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3CompositeBoundaryEnergy

/-!
# Approximate Hardy-support consumer

The exact wide-Hardy support premise is stronger than what a Hardy transform
normally supplies.  This file replaces it by an exact truncation identity:
the wide-supported part is handled by the existing composite B4 consumer and
the residual Hardy tail is exposed as the only additional square-summability
premise.  No tail estimate is asserted here.
-/

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.CCM24FiniteSSchurPolarTelescoping
open Source.CCM25Concrete.CCM24RadialBoundaryPairTransport
open Source.CCM25Concrete.SelectedWeilSquare
open scoped InnerProduct InnerProductSpace

noncomputable local instance approximateHardySupportCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

set_option maxHeartbeats 20000000 in
theorem compositeGapLeg_sourceColumn_normSq_summable_of_approximateHardySupport
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale) (s : ℝ)
    (hs : 0 ≤ s)
    (A : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier)
    (N : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda)
    {ρ : Type*}
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (htail : Summable fun i : ρ =>
      ‖(((radialSupportProjection lambda - sourceSoninProjection lambda) ∘L
          radialSupportProjection lambda ∘L rootConvolution owner) ∘L
        (A - archimedeanHardyTitchmarshOperator ∘L
          radialSupportProjection (wideRadialScale lambda s) ∘L
          archimedeanHardyTitchmarshOperator ∘L A) ∘L N)
        (sourceBasis i)‖ ^ 2) :
    Summable fun i : ρ =>
      ‖(((radialSupportProjection lambda - sourceSoninProjection lambda) ∘L
          radialSupportProjection lambda ∘L rootConvolution owner) ∘L A ∘L N)
        (sourceBasis i)‖ ^ 2 := by
  let Ewide := radialSupportProjection (wideRadialScale lambda s)
  let H := archimedeanHardyTitchmarshOperator
  let A0 := H ∘L Ewide ∘L H ∘L A
  let D := (radialSupportProjection lambda - sourceSoninProjection lambda) ∘L
    radialSupportProjection lambda ∘L rootConvolution owner
  have hH : H ∘L H = ContinuousLinearMap.id ℂ finiteSCarrier := by
    apply ContinuousLinearMap.ext
    intro u
    simp only [H, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply]
    exact archimedeanHardyTitchmarshOperator_involutive u
  have hEwide : Ewide ∘L Ewide = Ewide := by
    simpa only [Ewide, ContinuousLinearMap.mul_def] using
      (radialSupportProjection_isStarProjection
        (wideRadialScale lambda s)).isIdempotentElem
  have hHA0 : H ∘L A0 = Ewide ∘L H ∘L A := by
    apply ContinuousLinearMap.ext
    intro u
    have hHAt := DFunLike.congr_fun hH
      (Ewide (H (A u)))
    simp only [A0, ContinuousLinearMap.comp_apply] at hHAt ⊢
    exact hHAt
  have hwideA0 : Ewide ∘L H ∘L A0 = H ∘L A0 := by
    apply ContinuousLinearMap.ext
    intro u
    have hAt := DFunLike.congr_fun hHA0 u
    have hEAt := DFunLike.congr_fun hEwide (H (A u))
    simp only [ContinuousLinearMap.comp_apply] at hAt hEAt ⊢
    rw [hAt, hEAt]
  have hgood : Summable fun i : ρ =>
      ‖(D ∘L A0 ∘L N) (sourceBasis i)‖ ^ 2 := by
    exact compositeGapLeg_sourceColumn_normSq_summable
      owner lambda s hs A0 N sourceBasis hwideA0
  have htail' : Summable fun i : ρ =>
      ‖(D ∘L (A - A0) ∘L N) (sourceBasis i)‖ ^ 2 := by
    simpa only [D, A0, Ewide, H, sub_eq_add_neg,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.comp_apply, map_neg] using htail
  have hsum := PositiveTrace.summable_normSq_add sourceBasis
    (D ∘L A0 ∘L N) (D ∘L (A - A0) ∘L N) hgood htail'
  refine hsum.congr ?_
  intro i
  have hsplit : A0 (N (sourceBasis i)) +
      (A - A0) (N (sourceBasis i)) = A (N (sourceBasis i)) := by
    simp only [ContinuousLinearMap.sub_apply]
    abel
  have hD := congrArg D hsplit
  rw [map_add] at hD
  simpa only [D, ContinuousLinearMap.comp_apply] using
    congrArg (fun z : finiteSCarrier => ‖z‖ ^ 2) hD

end Dev
end ConnesWeilRH
