/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualSchurRowBoundaryMoment

/-!
# Row transition orientation ledger

The ambient physical analysis controls the non-adjoint gap
`EulerTransition - actualSchurTransition†`.  The raw row uses
`EulerTransition† - actualSchurTransition†` instead.  This module records the
exact conversion: the row gap is the adjoint transport gap plus the genuine
skew part of the actual Schur transition.  No self-adjointness shortcut is
introduced.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSActualSchurTransitionOrientation

open scoped InnerProduct

open CC20Concrete
open CCM24FiniteSActualJuliaInput
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSActualSchurRowBoundaryMoment
open CCM24FiniteSFrameGramCalculus

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

local notation "SourceOp" lambda =>
  sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda

noncomputable def suffixActualBandNamedSchurTransportAdjointGapRow
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) : SourceOp lambda :=
  suffixActualBandNamedSchurBoundaryMomentRow owner lambda stepData S ∘L
      ((suffixEulerFrameTransition lambda p S -
        (suffixActualSchurFrameStep lambda stepData p S).transition†)†) -
    ((suffixEulerFrameTransition lambda p S -
        (suffixActualSchurFrameStep lambda stepData p S).transition†)†) ∘L
      suffixActualBandNamedSchurBoundaryMomentRow owner lambda stepData (p :: S)

noncomputable def suffixActualBandNamedSchurTransitionSkewRow
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) : SourceOp lambda :=
  suffixActualBandNamedSchurBoundaryMomentRow owner lambda stepData S ∘L
      ((suffixActualSchurFrameStep lambda stepData p S).transition -
        (suffixActualSchurFrameStep lambda stepData p S).transition†) -
    ((suffixActualSchurFrameStep lambda stepData p S).transition -
        (suffixActualSchurFrameStep lambda stepData p S).transition†) ∘L
      suffixActualBandNamedSchurBoundaryMomentRow owner lambda stepData (p :: S)

theorem
    suffixEulerFrameTransitionAdjoint_sub_actualSchurTransitionAdjoint_eq_transportGapAdjoint_add_transitionSkew
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    (suffixEulerFrameTransition lambda p S)† -
        (suffixActualSchurFrameStep lambda stepData p S).transition† =
      ((oldSuffixFrame lambda p S)† ∘L
          (normalizedPrimeEulerFrameTransport p -
            (suffixActualSchurFrameStep lambda stepData p S).transport†) ∘L
        newSuffixFrame lambda S)† +
        ((suffixActualSchurFrameStep lambda stepData p S).transition -
          (suffixActualSchurFrameStep lambda stepData p S).transition†) := by
  have hadjoint_sub (A B : SourceOp lambda) :
      (A - B)† = A† - B† := by
    apply ContinuousLinearMap.ext
    intro y
    exact ext_inner_right ℂ fun z => by
      simp only [ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right]
  have hgap := congrArg ContinuousLinearMap.adjoint
    (suffixEulerFrameTransition_sub_actualSchurTransitionAdjoint_eq_transportAdjointGap
      lambda stepData p S)
  rw [hadjoint_sub] at hgap
  simp only [ContinuousLinearMap.adjoint_adjoint] at hgap
  apply ContinuousLinearMap.ext
  intro x
  have hgapPoint := congrArg
    (fun operator : SourceOp lambda => operator x) hgap
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply]
    at hgapPoint ⊢
  rw [← hgapPoint]
  abel

theorem suffixActualBandNamedSchurTransitionGapRow_eq_transportAdjointGapRow_add_transitionSkewRow
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    suffixActualBandNamedSchurTransitionGapRow owner lambda stepData p S =
      suffixActualBandNamedSchurTransportAdjointGapRow owner lambda stepData p S +
        suffixActualBandNamedSchurTransitionSkewRow owner lambda stepData p S := by
  have horientation :=
    suffixEulerFrameTransitionAdjoint_sub_actualSchurTransitionAdjoint_eq_transportGapAdjoint_add_transitionSkew
      lambda stepData p S
  have hgap :=
    suffixEulerFrameTransition_sub_actualSchurTransitionAdjoint_eq_transportAdjointGap
      lambda stepData p S
  have hgapAdjoint := congrArg ContinuousLinearMap.adjoint hgap
  rw [← hgapAdjoint] at horientation
  unfold suffixActualBandNamedSchurTransitionGapRow
    suffixActualBandNamedSchurTransportAdjointGapRow
    suffixActualBandNamedSchurTransitionSkewRow
  simp_rw [horientation]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, map_sub, map_add]
  abel

end CCM24FiniteSActualSchurTransitionOrientation
end CCM25Concrete
end Source
end ConnesWeilRH
