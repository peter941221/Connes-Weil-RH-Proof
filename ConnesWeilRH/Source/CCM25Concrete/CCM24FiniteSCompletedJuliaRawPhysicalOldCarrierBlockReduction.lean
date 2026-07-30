/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierReduction

/-!
# Old-carrier block reduction for the raw physical row

The old-carrier analysis is not an arbitrary injective map.  Its Gram operator
is block diagonal for the orthogonal decomposition induced by the old suffix
frame.  The transported new-frame projection lives entirely in that old-frame
range, while the reduced raw row vanishes on the orthogonal complement.

Consequently the all-vector old-carrier Douglas inequality is equivalent to
the original source-side signed raw inequality.  This removes the spurious
need for a uniform spectral gap on the full global-log carrier; it does not
prove the remaining signed source estimate.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierBlockReduction

open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CCM24FiniteSActualSchurCascade
open CCM24FiniteSCompletedJuliaRawPhysicalFactorization
open CCM24FiniteSCompletedJuliaRawDouglasReadout
open CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierReduction
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSCompletedJuliaAmbientDefectFactorization

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) :
      CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Frame projections -/

theorem frame_comp_adjoint_isStarProjection
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (frame : K →L[ℂ] H)
    (hframe : frame† ∘L frame = ContinuousLinearMap.id ℂ K) :
    IsStarProjection (frame ∘L frame†) := by
  refine
    { isIdempotentElem := ?_
      isSelfAdjoint := ?_ }
  · change (frame ∘L frame†) ∘L (frame ∘L frame†) = frame ∘L frame†
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply]
    have hframePoint := congrArg
      (fun T : K →L[ℂ] K => T (ContinuousLinearMap.adjoint frame x)) hframe
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] at hframePoint
    rw [hframePoint]
  · change (frame ∘L frame†)† = frame ∘L frame†
    rw [ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint]

theorem frame_projection_complement_annihilates
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (frame : K →L[ℂ] H)
    (hframe : frame† ∘L frame = ContinuousLinearMap.id ℂ K) :
  (frame ∘L frame†) ∘L
        (ContinuousLinearMap.id ℂ H - frame ∘L frame†) = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
  rw [map_sub]
  have hframePoint := congrArg
    (fun T : K →L[ℂ] K => T (ContinuousLinearMap.adjoint frame x)) hframe
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] at hframePoint
  rw [hframePoint]
  simp

/-! ## The transported new range is an old-frame block -/

theorem suffixEulerFrameTransportNewProjection_eq_oldFrame_block
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    normalizedPrimeEulerFrameTransport p ∘L
        (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
          ContinuousLinearMap.adjoint
            (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
        (ContinuousLinearMap.adjoint
          (normalizedPrimeEulerFrameTransport p)) =
      (suffixEulerFrameSchurStep lambda p S).oldFrame ∘L
        (suffixEulerFrameSchurStep lambda p S).transition ∘L
          ContinuousLinearMap.adjoint
            (suffixEulerFrameSchurStep lambda p S).transition ∘L
        ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).oldFrame := by
  have hintertwining :=
    (suffixEulerFrameSchurStep lambda p S).transport_intertwining
  have hintertwiningAdj := congrArg ContinuousLinearMap.adjoint hintertwining
  simp only [ContinuousLinearMap.adjoint_comp] at hintertwiningAdj
  apply ContinuousLinearMap.ext
  intro y
  simp only [ContinuousLinearMap.comp_apply]
  have hforward := congrArg
    (fun T : finiteSCarrier →L[ℂ] sourceSoninCarrier lambda => T y)
      hintertwiningAdj
  have hforward' := congrArg
    (fun T : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier =>
      T (ContinuousLinearMap.adjoint
        (suffixEulerFrameSchurStep lambda p S).transition
        (ContinuousLinearMap.adjoint
        (suffixEulerFrameSchurStep lambda p S).oldFrame y))) hintertwining
  simp only [ContinuousLinearMap.comp_apply] at hforward hforward'
  change
    (suffixEulerFrameSchurStep lambda p S).transport
        ((suffixEulerFrameSchurStep lambda p S).newFrame
          ((ContinuousLinearMap.adjoint
            (suffixEulerFrameSchurStep lambda p S).newFrame)
            ((ContinuousLinearMap.adjoint
              (suffixEulerFrameSchurStep lambda p S).transport) y))) =
      (suffixEulerFrameSchurStep lambda p S).oldFrame
        ((suffixEulerFrameSchurStep lambda p S).transition
          ((ContinuousLinearMap.adjoint
            (suffixEulerFrameSchurStep lambda p S).transition)
            ((ContinuousLinearMap.adjoint
              (suffixEulerFrameSchurStep lambda p S).oldFrame) y)))
  rw [hforward, hforward']

theorem suffixEulerFrameTransportNewProjection_comp_oldFrameProjection_eq_self
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ((normalizedPrimeEulerFrameTransport p ∘L
        (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
          ContinuousLinearMap.adjoint
            (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
        (ContinuousLinearMap.adjoint
          (normalizedPrimeEulerFrameTransport p))) ∘L
      ((suffixEulerFrameSchurStep lambda p S).oldFrame ∘L
        ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).oldFrame)) =
      normalizedPrimeEulerFrameTransport p ∘L
        (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
          ContinuousLinearMap.adjoint
            (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
        (ContinuousLinearMap.adjoint
          (normalizedPrimeEulerFrameTransport p)) := by
  rw [suffixEulerFrameTransportNewProjection_eq_oldFrame_block]
  apply ContinuousLinearMap.ext
  intro y
  simp only [ContinuousLinearMap.comp_apply]
  have hframe := congrArg
    (fun T : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda =>
      T (ContinuousLinearMap.adjoint
        (suffixEulerFrameSchurStep lambda p S).oldFrame y))
    (suffixEulerFrameSchurStep lambda p S).oldFrame_isometry
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] at hframe
  rw [hframe]

theorem suffixEulerFrameOldFrameProjection_comp_transportNewProjection_eq_self
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ((suffixEulerFrameSchurStep lambda p S).oldFrame ∘L
        ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).oldFrame) ∘L
      (normalizedPrimeEulerFrameTransport p ∘L
        (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
          ContinuousLinearMap.adjoint
            (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
        (ContinuousLinearMap.adjoint
          (normalizedPrimeEulerFrameTransport p))) =
      normalizedPrimeEulerFrameTransport p ∘L
        (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
          ContinuousLinearMap.adjoint
            (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
        (ContinuousLinearMap.adjoint
          (normalizedPrimeEulerFrameTransport p)) := by
  rw [suffixEulerFrameTransportNewProjection_eq_oldFrame_block]
  apply ContinuousLinearMap.ext
  intro y
  simp only [ContinuousLinearMap.comp_apply]
  have hframe := congrArg
    (fun T : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda =>
      T ((suffixEulerFrameSchurStep lambda p S).transition
        (ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).transition
          (ContinuousLinearMap.adjoint
            (suffixEulerFrameSchurStep lambda p S).oldFrame y))))
    (suffixEulerFrameSchurStep lambda p S).oldFrame_isometry
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] at hframe
  rw [hframe]

/-! ## Gram block decomposition -/

theorem suffixEulerFrameOldCarrierGram_commutes_oldFrameProjection
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    (suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S)† ∘L
        suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S ∘L
      ((suffixEulerFrameSchurStep lambda p S).oldFrame ∘L
        ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).oldFrame) =
      ((suffixEulerFrameSchurStep lambda p S).oldFrame ∘L
        ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).oldFrame) ∘L
        (suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S)† ∘L
          suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S := by
  rw [← ContinuousLinearMap.comp_assoc]
  rw [
    suffixEulerFrameAmbientBoundaryOldCarrierAnalysis_adjoint_comp_self_eq_id_sub_transport_newProjection
  ]
  let projection : finiteSCarrier →L[ℂ] finiteSCarrier :=
    (suffixEulerFrameSchurStep lambda p S).oldFrame ∘L
      ContinuousLinearMap.adjoint
        (suffixEulerFrameSchurStep lambda p S).oldFrame
  let transportedProjection : finiteSCarrier →L[ℂ] finiteSCarrier :=
    normalizedPrimeEulerFrameTransport p ∘L
      (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
        ContinuousLinearMap.adjoint
          (suffixEulerFrameSchurStep lambda p S).newFrame ∘L
      (ContinuousLinearMap.adjoint
        (normalizedPrimeEulerFrameTransport p))
  have hleft : projection ∘L transportedProjection = transportedProjection := by
    simpa only [projection, transportedProjection] using
      suffixEulerFrameOldFrameProjection_comp_transportNewProjection_eq_self
        lambda p S
  have hright : transportedProjection ∘L projection = transportedProjection := by
    simpa only [projection, transportedProjection] using
      suffixEulerFrameTransportNewProjection_comp_oldFrameProjection_eq_self
        lambda p S
  have hproj :
      (ContinuousLinearMap.id ℂ finiteSCarrier - transportedProjection) ∘L
          projection =
        projection ∘L
          (ContinuousLinearMap.id ℂ finiteSCarrier - transportedProjection) := by
    apply ContinuousLinearMap.ext
    intro y
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
    have hleftPoint := congrArg
      (fun T : finiteSCarrier →L[ℂ] finiteSCarrier => T y) hleft
    have hrightPoint := congrArg
      (fun T : finiteSCarrier →L[ℂ] finiteSCarrier => T y) hright
    simp only [ContinuousLinearMap.comp_apply] at hleftPoint hrightPoint
    rw [map_sub, hrightPoint, hleftPoint]
  simpa only [projection, transportedProjection] using hproj

/-! ## Pointwise old-carrier energy splitting -/

theorem oldCarrierAnalysis_normSq_eq_oldFrame_part_add_complement_part
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (y : finiteSCarrier) :
    ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S y‖ ^ 2 =
      ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S
          ((suffixEulerFrameSchurStep lambda p S).oldFrame
            (ContinuousLinearMap.adjoint
              (suffixEulerFrameSchurStep lambda p S).oldFrame y))‖ ^ 2 +
      ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S
          ((ContinuousLinearMap.id ℂ finiteSCarrier -
              (suffixEulerFrameSchurStep lambda p S).oldFrame ∘L
                ContinuousLinearMap.adjoint
                  (suffixEulerFrameSchurStep lambda p S).oldFrame) y)‖ ^ 2 := by
  let analysis := suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S
  let projection : finiteSCarrier →L[ℂ] finiteSCarrier :=
    (suffixEulerFrameSchurStep lambda p S).oldFrame ∘L
      ContinuousLinearMap.adjoint
        (suffixEulerFrameSchurStep lambda p S).oldFrame
  let complement : finiteSCarrier →L[ℂ] finiteSCarrier :=
    ContinuousLinearMap.id ℂ finiteSCarrier - projection
  let gram : finiteSCarrier →L[ℂ] finiteSCarrier := analysis† ∘L analysis
  have hcrossLeft : gram ∘L projection = projection ∘L gram := by
    simpa only [gram, projection] using
      suffixEulerFrameOldCarrierGram_commutes_oldFrameProjection lambda p S
  have hcrossRight : gram ∘L complement = complement ∘L gram := by
    dsimp [complement]
    apply ContinuousLinearMap.ext
    intro z
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
    have h := congrArg (fun T : finiteSCarrier →L[ℂ] finiteSCarrier =>
        T z) hcrossLeft
    simp only [ContinuousLinearMap.comp_apply] at h
    calc
      gram (z - projection z) = gram z - gram (projection z) := by
        rw [map_sub]
      _ = gram z - projection (gram z) := by rw [h]
  have hsum : projection + complement =
      ContinuousLinearMap.id ℂ finiteSCarrier := by
    dsimp [complement]
    apply ContinuousLinearMap.ext
    intro z
    simp
  have hzero : projection ∘L complement = 0 := by
    dsimp [complement]
    exact frame_projection_complement_annihilates
      (suffixEulerFrameSchurStep lambda p S).oldFrame
      (suffixEulerFrameSchurStep lambda p S).oldFrame_isometry
  have hzero' : complement ∘L projection = 0 := by
    apply ContinuousLinearMap.ext
    intro z
    simp only [ContinuousLinearMap.comp_apply]
    have hprojection : projection ∘L projection = projection := by
      simpa only [projection] using
        (frame_comp_adjoint_isStarProjection
          (suffixEulerFrameSchurStep lambda p S).oldFrame
          (suffixEulerFrameSchurStep lambda p S).oldFrame_isometry).isIdempotentElem
    have h := congrArg (fun T : finiteSCarrier →L[ℂ] finiteSCarrier => T z)
      hprojection
    simp only [ContinuousLinearMap.comp_apply] at h
    dsimp [complement]
    rw [h]
    simp only [sub_self]
  have hySplit : y = projection y + complement y := by
    have h := congrArg (fun T : finiteSCarrier →L[ℂ] finiteSCarrier => T y)
      hsum
    simpa only [ContinuousLinearMap.add_apply] using h.symm
  have hcrossNorm :
      ⟪analysis (projection y), analysis (complement y)⟫_ℂ = 0 := by
    rw [← ContinuousLinearMap.adjoint_inner_right]
    have hgramPoint := congrArg
      (fun T : finiteSCarrier →L[ℂ] finiteSCarrier => T y) hcrossRight
    simp only [ContinuousLinearMap.comp_apply] at hgramPoint
    change ⟪projection y, gram (complement y)⟫_ℂ = 0
    rw [hgramPoint]
    rw [← ContinuousLinearMap.adjoint_inner_left]
    have hcomplementSelf : complement† = complement := by
      dsimp [projection]
      dsimp [complement]
      rw [map_sub, ContinuousLinearMap.adjoint_id,
        ContinuousLinearMap.adjoint_comp,
        ContinuousLinearMap.adjoint_adjoint]
    rw [hcomplementSelf]
    have hzeroPoint := congrArg
      (fun T : finiteSCarrier →L[ℂ] finiteSCarrier => T y) hzero'
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply]
      at hzeroPoint
    rw [hzeroPoint]
    simp
  calc
    ‖analysis y‖ ^ 2 =
        ‖analysis (projection y + complement y)‖ ^ 2 := by
      exact congrArg (fun z : finiteSCarrier => ‖analysis z‖ ^ 2) hySplit
    _ = ‖analysis (projection y)‖ ^ 2 +
        ‖analysis (complement y)‖ ^ 2 := by
      have hpyth :=
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
          (𝕜 := ℂ) (analysis (projection y)) (analysis (complement y))
          hcrossNorm
      simpa only [map_add, pow_two] using hpyth
    _ = ‖analysis
          ((suffixEulerFrameSchurStep lambda p S).oldFrame
            (ContinuousLinearMap.adjoint
              (suffixEulerFrameSchurStep lambda p S).oldFrame y))‖ ^ 2 +
        ‖analysis
          ((ContinuousLinearMap.id ℂ finiteSCarrier -
              (suffixEulerFrameSchurStep lambda p S).oldFrame ∘L
                ContinuousLinearMap.adjoint
                  (suffixEulerFrameSchurStep lambda p S).oldFrame) y)‖ ^ 2 := by
      rfl

/-! ## Exact equivalence with the source-side signed row -/

theorem suffixRawOldCarrierDomination_iff_rawDomination
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (bound : ℝ) :
    SuffixRawOldCarrierDomination owner lambda p S bound ↔
      SuffixRawAmbientBoundaryDomination owner lambda p S bound := by
  constructor
  · exact suffixRawOldCarrierDomination_implies_rawDomination
      owner lambda p S bound
  · intro hraw
    refine ⟨hraw.1, ?_⟩
    intro y
    let oldFrame := (suffixEulerFrameSchurStep lambda p S).oldFrame
    let oldProjection : finiteSCarrier →L[ℂ] finiteSCarrier :=
      oldFrame ∘L ContinuousLinearMap.adjoint oldFrame
    let oldComplement : finiteSCarrier →L[ℂ] finiteSCarrier :=
      ContinuousLinearMap.id ℂ finiteSCarrier - oldProjection
    have hySplit : y = oldProjection y + oldComplement y := by
      dsimp [oldComplement]
      simp
    have hrowComplement :
        suffixActualBandRawPhysicalReducedRow owner lambda p S
            (oldComplement y) = 0 := by
      dsimp [oldComplement, oldProjection]
      simp only [suffixActualBandRawPhysicalReducedRow,
        ContinuousLinearMap.comp_apply]
      have hzero :=
        (suffixEulerFrameSchurStep lambda p S).oldFrame_isometry
      have hzeroPoint := congrArg
        (fun T : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda =>
          T (ContinuousLinearMap.adjoint
            (suffixEulerFrameSchurStep lambda p S).oldFrame y)) hzero
      simp only [ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply] at hzeroPoint
      rw [map_sub, hzeroPoint]
      simp
    have hrowProjection :
        suffixActualBandRawPhysicalReducedRow owner lambda p S
            (oldProjection y) =
          suffixActualBandRawPhysicalFourTermRow owner lambda p S
            (ContinuousLinearMap.adjoint oldFrame y) := by
      have holdProjectionPoint :
          oldProjection y =
            (suffixEulerFrameSchurStep lambda p S).oldFrame
              ((ContinuousLinearMap.adjoint
                (suffixEulerFrameSchurStep lambda p S).oldFrame) y) := by
        rfl
      rw [holdProjectionPoint]
      have h := congrArg
        (fun T : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda =>
          T ((ContinuousLinearMap.adjoint
            (suffixEulerFrameSchurStep lambda p S).oldFrame) y))
        (suffixActualBandRawPhysicalFourTermRow_eq_reducedRow_comp_oldFrame
          owner lambda p S)
      simpa only [oldFrame, ContinuousLinearMap.comp_apply] using h.symm
    have hrow :
        suffixActualBandRawPhysicalReducedRow owner lambda p S y =
          suffixActualBandRawPhysicalFourTermRow owner lambda p S
            (ContinuousLinearMap.adjoint oldFrame y) := by
      calc
        suffixActualBandRawPhysicalReducedRow owner lambda p S y =
            suffixActualBandRawPhysicalReducedRow owner lambda p S
              (oldProjection y + oldComplement y) := by
          exact congrArg
            (fun z : finiteSCarrier =>
              suffixActualBandRawPhysicalReducedRow owner lambda p S z)
            hySplit
        _ = suffixActualBandRawPhysicalReducedRow owner lambda p S
              (oldProjection y) +
            suffixActualBandRawPhysicalReducedRow owner lambda p S
              (oldComplement y) := by rw [map_add]
        _ = suffixActualBandRawPhysicalFourTermRow owner lambda p S
              (ContinuousLinearMap.adjoint oldFrame y) := by
          rw [hrowProjection, hrowComplement, add_zero]
    have henergy := oldCarrierAnalysis_normSq_eq_oldFrame_part_add_complement_part
      lambda p S y
    have hrawPoint := hraw.2 (ContinuousLinearMap.adjoint oldFrame y)
    have hrowEnergy :
        ‖suffixActualBandRawPhysicalFourTermRow owner lambda p S
            (ContinuousLinearMap.adjoint oldFrame y)‖ ^ 2 ≤
          bound ^ 2 *
            ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S
              (oldFrame (ContinuousLinearMap.adjoint oldFrame y))‖ ^ 2 := by
      rw [← suffixActualBandRawQuadraticIntertwiningDefect_adjoint_eq_fourTermRow
          owner lambda p S]
      rw [suffixEulerFrameAmbientBoundaryOldCarrierAnalysis_oldFrame_normSq_eq_actual_channels]
      exact hrawPoint
    rw [hrow, henergy]
    calc
      ‖suffixActualBandRawPhysicalFourTermRow owner lambda p S
          (ContinuousLinearMap.adjoint oldFrame y)‖ ^ 2 ≤
        bound ^ 2 *
          ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S
            (oldFrame (ContinuousLinearMap.adjoint oldFrame y))‖ ^ 2 := hrowEnergy
      _ ≤ bound ^ 2 *
          (‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S
            (oldFrame (ContinuousLinearMap.adjoint oldFrame y))‖ ^ 2 +
            ‖suffixEulerFrameAmbientBoundaryOldCarrierAnalysis lambda p S
              (oldComplement y)‖ ^ 2) := by
        exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right (sq_nonneg _))
          (sq_nonneg bound)

end CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierBlockReduction
end CCM25Concrete
end Source
end ConnesWeilRH
