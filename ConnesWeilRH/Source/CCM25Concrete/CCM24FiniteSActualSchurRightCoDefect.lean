/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualSchurTransitionOrientation

/-!
# The right co-defect of an actual rectangular Schur step

The existing adjacent Julia ledger controls the left co-defect
`I - T T†` of the source transition `T`.  The reversed row orientation
exposes the other positive defect `I - T† T`.  This module derives its exact
rectangular decomposition from the genuine frame maps; it does not identify
the two defects and does not estimate the transition skew.

For an old frame `F₀`, a new frame `F₁`, and an ambient transport `Z`, the
reverse boundary channel is

```text
Rᵣ = (I - F₀ F₀†) Z F₁
```

and the exact Gram identity is

```text
I - T† T
  = F₁† (I - Z† Z) F₁ + Rᵣ† Rᵣ.
```

The second summand is the range leakage which prevents a reverse step from
being an ordinary Schur step with the same frame intertwining.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSActualSchurRightCoDefect

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open RCLike
open CCM24FiniteSJuliaCoDefect
open CCM24FiniteSJuliaBessel
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSActualJuliaInput
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Generic rectangular identity -/

noncomputable def rectangularRightBoundaryCompression
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K]
    (oldFrame : H →L[ℂ] K) (transport : K →L[ℂ] K)
    (newFrame : H →L[ℂ] K) : H →L[ℂ] K :=
  (ContinuousLinearMap.id ℂ K -
      oldFrame ∘L ContinuousLinearMap.adjoint oldFrame) ∘L
    transport ∘L newFrame

noncomputable def rectangularTransitionRightCoDefect
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (transition : H →L[ℂ] H) : H →L[ℂ] H :=
  ContinuousLinearMap.id ℂ H -
    ContinuousLinearMap.adjoint transition ∘L transition

theorem rectangularTransition_eq_oldFrameAdjoint_transport_newFrame
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K]
    (data : RectangularSchurCoDefectStepData H K) :
    data.transition =
      ContinuousLinearMap.adjoint data.oldFrame ∘L data.transport ∘L
        data.newFrame := by
  have hleft :
      ContinuousLinearMap.adjoint data.oldFrame ∘L data.transport ∘L
          data.newFrame = data.transition := by
    calc
      ContinuousLinearMap.adjoint data.oldFrame ∘L data.transport ∘L
          data.newFrame =
          ContinuousLinearMap.adjoint data.oldFrame ∘L
            (data.transport ∘L data.newFrame) := by
              rfl
      _ = ContinuousLinearMap.adjoint data.oldFrame ∘L
            (data.oldFrame ∘L data.transition) := by
              rw [data.transport_intertwining]
      _ = (ContinuousLinearMap.adjoint data.oldFrame ∘L data.oldFrame) ∘L
            data.transition := by
              rw [ContinuousLinearMap.comp_assoc]
      _ = data.transition := by
              rw [data.oldFrame_isometry, ContinuousLinearMap.id_comp]
  exact hleft.symm

theorem rectangularTransitionRightCoDefect_eq_ambient_add_boundary
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K]
    (data : RectangularSchurCoDefectStepData H K) :
    rectangularTransitionRightCoDefect data.transition =
      ContinuousLinearMap.adjoint data.newFrame ∘L
          (ContinuousLinearMap.id ℂ K -
            ContinuousLinearMap.adjoint data.transport ∘L data.transport) ∘L
        data.newFrame +
      (rectangularRightBoundaryCompression data.oldFrame data.transport
        data.newFrame)† ∘L
        rectangularRightBoundaryCompression data.oldFrame data.transport
          data.newFrame := by
  let projection : K →L[ℂ] K :=
    data.oldFrame ∘L ContinuousLinearMap.adjoint data.oldFrame
  let complement : K →L[ℂ] K :=
    ContinuousLinearMap.id ℂ K - projection
  have hprojection_sq : projection ∘L projection = projection := by
    calc
      projection ∘L projection =
          data.oldFrame ∘L
            (ContinuousLinearMap.adjoint data.oldFrame ∘L
              data.oldFrame) ∘L
            ContinuousLinearMap.adjoint data.oldFrame := by
        simp only [projection, ContinuousLinearMap.comp_assoc]
      _ = data.oldFrame ∘L
            (ContinuousLinearMap.id ℂ H) ∘L
            ContinuousLinearMap.adjoint data.oldFrame := by
        rw [data.oldFrame_isometry]
      _ = projection := by
        simp only [projection, ContinuousLinearMap.id_comp]
  have hcomplement_sq : complement ∘L complement = complement := by
    apply ContinuousLinearMap.ext
    intro x
    have h := congrArg (fun T : K →L[ℂ] K => T x) hprojection_sq
    simp only [complement, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
      map_sub] at h ⊢
    rw [h]
    abel
  have hprojection_adjoint : projection† = projection := by
    simp only [projection, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint]
  have hcomplement_adjoint : complement† = complement := by
    apply ContinuousLinearMap.ext
    intro x
    simp only [complement, map_sub, ContinuousLinearMap.adjoint_id,
      hprojection_adjoint]
  have htransition :=
    rectangularTransition_eq_oldFrameAdjoint_transport_newFrame data
  have htransition_adjoint :
      data.transition† =
        ContinuousLinearMap.adjoint data.newFrame ∘L
          ContinuousLinearMap.adjoint data.transport ∘L data.oldFrame := by
    rw [htransition]
    simp only [ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc]
  unfold rectangularTransitionRightCoDefect
  rw [htransition_adjoint, htransition]
  unfold rectangularRightBoundaryCompression
  rw [show
      (ContinuousLinearMap.id ℂ K -
          data.oldFrame ∘L ContinuousLinearMap.adjoint data.oldFrame) =
        complement by
    rfl]
  simp only [ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, hcomplement_adjoint]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.id_apply, map_sub]
  have hnew :
      ContinuousLinearMap.adjoint data.newFrame (data.newFrame x) = x := by
    have h := congrArg
      (fun T : H →L[ℂ] H => T x) data.newFrame_isometry
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using h
  rw [hnew]
  have hsplit :
      data.transport (data.newFrame x) =
        projection (data.transport (data.newFrame x)) +
          complement (data.transport (data.newFrame x)) := by
    change data.transport (data.newFrame x) =
      projection (data.transport (data.newFrame x)) +
        (data.transport (data.newFrame x) -
          projection (data.transport (data.newFrame x)))
    abel
  have hsplit' := congrArg
    (fun z : K => ContinuousLinearMap.adjoint data.transport z) hsplit
  simp only [ContinuousLinearMap.add_apply, map_add] at hsplit'
  have hcomplement_point :
      complement (complement (data.transport (data.newFrame x))) =
        complement (data.transport (data.newFrame x)) := by
    have h := congrArg
      (fun T : K →L[ℂ] K => T (data.transport (data.newFrame x)))
      hcomplement_sq
    simpa only [ContinuousLinearMap.comp_apply] using h
  rw [hsplit']
  rw [hcomplement_point]
  simp only [map_add]
  abel

theorem rectangularRightBoundaryCompression_eq_zero_of_intertwining
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K]
    (data : RectangularSchurCoDefectStepData H K) :
    rectangularRightBoundaryCompression data.oldFrame data.transport
        data.newFrame = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  have htransport :
    data.transport (data.newFrame x) = data.oldFrame (data.transition x) := by
    simpa only [ContinuousLinearMap.comp_apply] using congrArg
      (fun T : H →L[ℂ] K => T x)
      data.transport_intertwining
  have hframe :
      data.oldFrame
          (ContinuousLinearMap.adjoint data.oldFrame
            (data.oldFrame (data.transition x))) =
        data.oldFrame (data.transition x) := by
    have h := congrArg
      (fun T : H →L[ℂ] H => data.oldFrame (T (data.transition x)))
      data.oldFrame_isometry
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using h
  simp only [rectangularRightBoundaryCompression,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply]
  rw [htransport, hframe]
  simp

theorem rectangularTransitionRightCoDefect_eq_frameAdjoint_canonicalJuliaDefect
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K]
    (data : RectangularSchurCoDefectStepData H K)
    (hcontract :
      (ContinuousLinearMap.adjoint data.transport) ∘L data.transport ≤
        ContinuousLinearMap.id ℂ K) :
    rectangularTransitionRightCoDefect data.transition =
      (ContinuousLinearMap.adjoint data.newFrame) ∘L
          (canonicalJuliaDefect data.transport hcontract)† ∘L
            canonicalJuliaDefect data.transport hcontract ∘L data.newFrame := by
  rw [rectangularTransitionRightCoDefect_eq_ambient_add_boundary data,
    rectangularRightBoundaryCompression_eq_zero_of_intertwining data]
  simp only [map_zero, ContinuousLinearMap.zero_comp,
    ContinuousLinearMap.comp_zero, add_zero]
  rw [← canonicalJuliaDefect_adjoint_comp_self data.transport hcontract]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply]

theorem rectangularTransitionRightCoDefect_inner_eq_canonicalJuliaDefect_normSq
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K]
    (data : RectangularSchurCoDefectStepData H K)
    (hcontract :
      (ContinuousLinearMap.adjoint data.transport) ∘L data.transport ≤
        ContinuousLinearMap.id ℂ K)
    (x : H) :
    ‖canonicalJuliaDefect data.transport hcontract (data.newFrame x)‖ ^ 2 =
      (⟪(rectangularTransitionRightCoDefect data.transition) x, x⟫_ℂ).re := by
  have hgram :
      (canonicalJuliaDefect data.transport hcontract ∘L data.newFrame)† ∘L
          (canonicalJuliaDefect data.transport hcontract ∘L data.newFrame) =
        rectangularTransitionRightCoDefect data.transition := by
    rw [ContinuousLinearMap.adjoint_comp,
      rectangularTransitionRightCoDefect_eq_frameAdjoint_canonicalJuliaDefect
        data hcontract]
    simp only [ContinuousLinearMap.comp_assoc]
  calc
    ‖canonicalJuliaDefect data.transport hcontract (data.newFrame x)‖ ^ 2 =
        ‖(canonicalJuliaDefect data.transport hcontract ∘L
          data.newFrame) x‖ ^ 2 := by rfl
    _ = RCLike.re (⟪((canonicalJuliaDefect data.transport hcontract ∘L
          data.newFrame)† ∘L
          (canonicalJuliaDefect data.transport hcontract ∘L
            data.newFrame)) x, x⟫_ℂ) := by
      rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left]
    _ = (⟪(rectangularTransitionRightCoDefect data.transition) x, x⟫_ℂ).re := by
      rw [hgram]
      simpa only [RCLike.re_eq_complex_re]

/-! ## Actual source-step specialization -/

noncomputable def suffixActualSchurRightBoundary
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  rectangularRightBoundaryCompression
    (suffixActualSchurFrameStep lambda stepData p S).oldFrame
    (suffixActualSchurFrameStep lambda stepData p S).transport
    (suffixActualSchurFrameStep lambda stepData p S).newFrame

theorem suffixActualSchurRightBoundary_eq_zero
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    suffixActualSchurRightBoundary lambda stepData p S = 0 := by
  simpa only [suffixActualSchurRightBoundary] using
    rectangularRightBoundaryCompression_eq_zero_of_intertwining
      (suffixActualSchurFrameStep lambda stepData p S)

theorem suffixActualSchurTransitionRightCoDefect_eq_ambient_add_boundary
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    rectangularTransitionRightCoDefect
        (suffixActualSchurFrameStep lambda stepData p S).transition =
      ContinuousLinearMap.adjoint
          (suffixActualSchurFrameStep lambda stepData p S).newFrame ∘L
          (ContinuousLinearMap.id ℂ finiteSCarrier -
            ContinuousLinearMap.adjoint
              (suffixActualSchurFrameStep lambda stepData p S).transport ∘L
              (suffixActualSchurFrameStep lambda stepData p S).transport) ∘L
        (suffixActualSchurFrameStep lambda stepData p S).newFrame +
      (suffixActualSchurRightBoundary lambda stepData p S)† ∘L
        suffixActualSchurRightBoundary lambda stepData p S := by
  simpa only [suffixActualSchurRightBoundary] using
    rectangularTransitionRightCoDefect_eq_ambient_add_boundary
      (suffixActualSchurFrameStep lambda stepData p S)

theorem suffixActualSchurTransitionRightCoDefect_eq_compressed_ambient
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    rectangularTransitionRightCoDefect
        (suffixActualSchurFrameStep lambda stepData p S).transition =
      ContinuousLinearMap.adjoint
          (suffixActualSchurFrameStep lambda stepData p S).newFrame ∘L
          (ContinuousLinearMap.id ℂ finiteSCarrier -
            ContinuousLinearMap.adjoint
              (suffixActualSchurFrameStep lambda stepData p S).transport ∘L
              (suffixActualSchurFrameStep lambda stepData p S).transport) ∘L
        (suffixActualSchurFrameStep lambda stepData p S).newFrame := by
  have hboundary :
      (suffixActualSchurRightBoundary lambda stepData p S)† ∘L
          suffixActualSchurRightBoundary lambda stepData p S = 0 := by
    have hright := suffixActualSchurRightBoundary_eq_zero
      lambda stepData p S
    calc
      (suffixActualSchurRightBoundary lambda stepData p S)† ∘L
          suffixActualSchurRightBoundary lambda stepData p S =
        (suffixActualSchurRightBoundary lambda stepData p S)† ∘L
          (0 : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier) := by
            exact congrArg
              (fun q : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
                (suffixActualSchurRightBoundary lambda stepData p S)† ∘L q)
              hright
      _ = 0 := ContinuousLinearMap.comp_zero _
  rw [suffixActualSchurTransitionRightCoDefect_eq_ambient_add_boundary
    lambda stepData p S, hboundary]
  simp only [add_zero]

end CCM24FiniteSActualSchurRightCoDefect
end CCM25Concrete
end Source
end ConnesWeilRH
