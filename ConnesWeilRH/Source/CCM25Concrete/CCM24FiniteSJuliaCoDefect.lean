/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSJuliaCausal
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedSourcePolar
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSDouglasFactor
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Canonical co-defect schedule for the finite-S Schur cascade

The physical Schur step is a contraction `F` on the fixed source carrier.
The left co-defect is the Julia defect of the adjoint transfer `F†`, namely
`(I - F F†)^(1/2)`.  This module creates that row from the already constructed
current-range Schur data.  It does not identify a physical boundary column
with the row; that remains the separate bounded readout/factorization gate.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSJuliaCoDefect

open CC20Concrete
open RCLike
open CCM24FiniteSActualJuliaInput
open CCM24FiniteSFixedSourcePolar
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSJuliaBessel
open CCM24FiniteSJuliaCausal
open CCM24FiniteSProjectionTrace

open scoped InnerProduct InnerProductSpace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-!
The ring-level Schur identity is not directly applicable to a frame
`H -> K`: its frame and supplied dagger have opposite rectangular types.  The
following typed version is the operator identity needed by the source
cascade.  No positivity or norm estimate is hidden in it.
-/
def rectangularTransitionCoDefect
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (transition transitionDagger : H →L[ℂ] H) : H →L[ℂ] H :=
  ContinuousLinearMap.id ℂ H - transition ∘L transitionDagger

def rectangularAmbientCoDefect
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (transport transportDagger : K →L[ℂ] K) : K →L[ℂ] K :=
  ContinuousLinearMap.id ℂ K - transport ∘L transportDagger

def rectangularBoundaryCompression
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (oldFrameDagger : K →L[ℂ] H) (transport : K →L[ℂ] K)
    (newFrame : H →L[ℂ] K) (newFrameDagger : K →L[ℂ] H) :
    K →L[ℂ] H :=
  oldFrameDagger ∘L transport ∘L
    (ContinuousLinearMap.id ℂ K - newFrame ∘L newFrameDagger)

def rectangularBoundaryCompressionDagger
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (oldFrame : H →L[ℂ] K) (transportDagger : K →L[ℂ] K)
    (newFrame : H →L[ℂ] K) (newFrameDagger : K →L[ℂ] H) :
    H →L[ℂ] K :=
  (ContinuousLinearMap.id ℂ K - newFrame ∘L newFrameDagger) ∘L
    transportDagger ∘L oldFrame

theorem rectangularTransitionCoDefect_eq_ambient_add_boundary
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (oldFrame : H →L[ℂ] K) (oldFrameDagger : K →L[ℂ] H)
    (newFrame : H →L[ℂ] K) (newFrameDagger : K →L[ℂ] H)
    (transport transportDagger : K →L[ℂ] K)
    (transition transitionDagger : H →L[ℂ] H)
    (hOldIsometry : oldFrameDagger ∘L oldFrame =
      ContinuousLinearMap.id ℂ H)
    (hNewIsometry : newFrameDagger ∘L newFrame =
      ContinuousLinearMap.id ℂ H)
    (hTransport : transport ∘L newFrame = oldFrame ∘L transition)
    (hTransportDagger : newFrameDagger ∘L transportDagger =
      transitionDagger ∘L oldFrameDagger) :
    rectangularTransitionCoDefect transition transitionDagger =
      oldFrameDagger ∘L
          rectangularAmbientCoDefect transport transportDagger ∘L oldFrame +
        rectangularBoundaryCompression oldFrameDagger transport newFrame
            newFrameDagger ∘L
          rectangularBoundaryCompressionDagger oldFrame transportDagger
            newFrame newFrameDagger := by
  let projection : K →L[ℂ] K := newFrame ∘L newFrameDagger
  have hProjectionSq : projection ∘L projection = projection := by
    apply ContinuousLinearMap.ext
    intro x
    have h := congrArg (fun T : H →L[ℂ] H =>
        T (newFrameDagger x)) hNewIsometry
    have h' := congrArg newFrame h
    simpa only [projection, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using h'
  let complement : K →L[ℂ] K :=
    ContinuousLinearMap.id ℂ K - projection
  have hComplementSq : complement ∘L complement = complement := by
    apply ContinuousLinearMap.ext
    intro x
    have h := congrArg (fun T : K →L[ℂ] K => T x) hProjectionSq
    simp only [projection, complement, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
      map_sub] at h ⊢
    rw [h]
    abel
  have hLeftTransition :
      oldFrameDagger ∘L transport ∘L newFrame = transition := by
    calc
      oldFrameDagger ∘L transport ∘L newFrame =
          oldFrameDagger ∘L (transport ∘L newFrame) := by
            rfl
      _ = oldFrameDagger ∘L (oldFrame ∘L transition) := by
            rw [hTransport]
      _ = (oldFrameDagger ∘L oldFrame) ∘L transition := by
            rw [← ContinuousLinearMap.comp_assoc]
      _ = transition := by
            rw [hOldIsometry, ContinuousLinearMap.id_comp]
  have hRightTransition :
      newFrameDagger ∘L transportDagger ∘L oldFrame = transitionDagger := by
    calc
      newFrameDagger ∘L transportDagger ∘L oldFrame =
          (newFrameDagger ∘L transportDagger) ∘L oldFrame := by
            rfl
      _ = (transitionDagger ∘L oldFrameDagger) ∘L oldFrame := by
            rw [hTransportDagger]
      _ = transitionDagger ∘L (oldFrameDagger ∘L oldFrame) := by
            rw [ContinuousLinearMap.comp_assoc]
      _ = transitionDagger := by
            rw [hOldIsometry, ContinuousLinearMap.comp_id]
  have hBoundarySquare :
      rectangularBoundaryCompression oldFrameDagger transport newFrame
          newFrameDagger ∘L
        rectangularBoundaryCompressionDagger oldFrame transportDagger
          newFrame newFrameDagger =
      oldFrameDagger ∘L transport ∘L complement ∘L
        transportDagger ∘L oldFrame := by
    apply ContinuousLinearMap.ext
    intro x
    change oldFrameDagger
        (transport (complement (complement
          (transportDagger (oldFrame x))))) =
      oldFrameDagger (transport (complement
        (transportDagger (oldFrame x))))
    have h := congrArg (fun T : K →L[ℂ] K =>
        T (transportDagger (oldFrame x))) hComplementSq
    exact congrArg (fun z : K => oldFrameDagger (transport z))
      (by simpa only [ContinuousLinearMap.comp_apply] using h)
  change ContinuousLinearMap.id ℂ H - transition ∘L transitionDagger =
    oldFrameDagger ∘L
        (ContinuousLinearMap.id ℂ K - transport ∘L transportDagger) ∘L
        oldFrame +
      rectangularBoundaryCompression oldFrameDagger transport newFrame
          newFrameDagger ∘L
        rectangularBoundaryCompressionDagger oldFrame transportDagger
          newFrame newFrameDagger
  rw [hBoundarySquare]
  apply ContinuousLinearMap.ext
  intro x
  have hOldPoint : oldFrameDagger (oldFrame x) = x := by
    have h := congrArg (fun T : H →L[ℂ] H => T x) hOldIsometry
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using h
  have hLeftPoint :
      oldFrameDagger (transport (newFrame
        (newFrameDagger (transportDagger (oldFrame x))))) =
        transition (newFrameDagger (transportDagger (oldFrame x))) := by
    have h := congrArg (fun T : H →L[ℂ] H =>
        T (newFrameDagger (transportDagger (oldFrame x))))
      hLeftTransition
    simpa only [ContinuousLinearMap.comp_apply] using h
  have hRightPoint :
      newFrameDagger (transportDagger (oldFrame x)) =
        transitionDagger x := by
    have h := congrArg (fun T : H →L[ℂ] H => T x)
      hRightTransition
    simpa only [ContinuousLinearMap.comp_apply] using h
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    map_sub, projection, complement]
  rw [hOldPoint, hLeftPoint, hRightPoint]
  abel

/-! The rectangular boundary dagger is forced by the Hilbert adjoint. -/

theorem rectangularBoundaryCompressionDagger_eq_adjoint
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (oldFrame : H →L[ℂ] K) (transport : K →L[ℂ] K)
    (newFrame : H →L[ℂ] K) :
    rectangularBoundaryCompressionDagger oldFrame
        (ContinuousLinearMap.adjoint transport) newFrame
        (ContinuousLinearMap.adjoint newFrame) =
      ContinuousLinearMap.adjoint
        (rectangularBoundaryCompression (ContinuousLinearMap.adjoint oldFrame)
          transport newFrame (ContinuousLinearMap.adjoint newFrame)) := by
  simp only [rectangularBoundaryCompressionDagger,
    rectangularBoundaryCompression, ContinuousLinearMap.adjoint_comp,
    map_sub, ContinuousLinearMap.adjoint_id,
    ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc]

/-!
The next package is the typed form of Proof 392's local owner.  Its dagger
fields are actual Hilbert-space adjoints, rather than an independently supplied
ring involution.  The only source-specific input is the consecutive-frame
intertwining equation; the contractive transition and ambient transport are
kept explicit so the positive order argument cannot be bypassed.
-/
structure RectangularSchurCoDefectStepData
    (H K : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] where
  oldFrame : H →L[ℂ] K
  newFrame : H →L[ℂ] K
  transport : K →L[ℂ] K
  transition : H →L[ℂ] H
  oldFrame_isometry : ContinuousLinearMap.adjoint oldFrame ∘L oldFrame =
    ContinuousLinearMap.id ℂ H
  newFrame_isometry : ContinuousLinearMap.adjoint newFrame ∘L newFrame =
    ContinuousLinearMap.id ℂ H
  transport_norm_le_one : ‖transport‖ ≤ 1
  transition_norm_le_one : ‖transition‖ ≤ 1
  transport_intertwining : transport ∘L newFrame =
    oldFrame ∘L transition
  boundaryDagger_eq_adjoint :
    rectangularBoundaryCompressionDagger oldFrame
        (ContinuousLinearMap.adjoint transport) newFrame
        (ContinuousLinearMap.adjoint newFrame) =
      ContinuousLinearMap.adjoint
        (rectangularBoundaryCompression (ContinuousLinearMap.adjoint oldFrame)
          transport newFrame (ContinuousLinearMap.adjoint newFrame))

noncomputable def RectangularSchurCoDefectStepData.boundary
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (data : RectangularSchurCoDefectStepData H K) : K →L[ℂ] H :=
  rectangularBoundaryCompression (ContinuousLinearMap.adjoint data.oldFrame)
    data.transport data.newFrame (ContinuousLinearMap.adjoint data.newFrame)

noncomputable def RectangularSchurCoDefectStepData.boundaryDagger
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (data : RectangularSchurCoDefectStepData H K) : H →L[ℂ] K :=
  rectangularBoundaryCompressionDagger data.oldFrame
    (ContinuousLinearMap.adjoint data.transport) data.newFrame
    (ContinuousLinearMap.adjoint data.newFrame)

noncomputable def RectangularSchurCoDefectStepData.transitionAdjointContract
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (data : RectangularSchurCoDefectStepData H K) :
    ContinuousLinearMap.adjoint (ContinuousLinearMap.adjoint data.transition) ∘L
        ContinuousLinearMap.adjoint data.transition ≤
      ContinuousLinearMap.id ℂ H := by
  have hadjoint_norm : ‖ContinuousLinearMap.adjoint data.transition‖ ≤ 1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact data.transition_norm_le_one
  exact adjoint_comp_self_le_id_of_norm_le_one
    (ContinuousLinearMap.adjoint data.transition) hadjoint_norm

noncomputable def RectangularSchurCoDefectStepData.leftCoDefect
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (data : RectangularSchurCoDefectStepData H K) : H →L[ℂ] H :=
  canonicalJuliaDefect (ContinuousLinearMap.adjoint data.transition)
    data.transitionAdjointContract

theorem RectangularSchurCoDefectStepData.leftCoDefect_adjoint_comp_self
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (data : RectangularSchurCoDefectStepData H K) :
    ContinuousLinearMap.adjoint data.leftCoDefect ∘L data.leftCoDefect =
       rectangularTransitionCoDefect data.transition
         (ContinuousLinearMap.adjoint data.transition) := by
  rw [RectangularSchurCoDefectStepData.leftCoDefect]
  have h := canonicalJuliaDefect_adjoint_comp_self
    (ContinuousLinearMap.adjoint data.transition)
    data.transitionAdjointContract
  simpa only [rectangularTransitionCoDefect,
    ContinuousLinearMap.adjoint_adjoint] using h

theorem RectangularSchurCoDefectStepData.schur_coDefect_eq_ambient_add_boundary
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (data : RectangularSchurCoDefectStepData H K) :
    rectangularTransitionCoDefect data.transition
        (ContinuousLinearMap.adjoint data.transition) =
      ContinuousLinearMap.adjoint data.oldFrame ∘L
          rectangularAmbientCoDefect data.transport
            (ContinuousLinearMap.adjoint data.transport) ∘L
        data.oldFrame +
      data.boundary ∘L ContinuousLinearMap.adjoint data.boundary := by
  have hTransportDagger : ContinuousLinearMap.adjoint data.newFrame ∘L
      (ContinuousLinearMap.adjoint data.transport) =
      ContinuousLinearMap.adjoint data.transition ∘L
        ContinuousLinearMap.adjoint data.oldFrame := by
    have h := congrArg ContinuousLinearMap.adjoint
      data.transport_intertwining
    simpa only [ContinuousLinearMap.adjoint_comp] using h
  have hBoundary :
      rectangularBoundaryCompressionDagger data.oldFrame
          (ContinuousLinearMap.adjoint data.transport) data.newFrame
          (ContinuousLinearMap.adjoint data.newFrame) =
        ContinuousLinearMap.adjoint data.boundary := by
    simpa only [RectangularSchurCoDefectStepData.boundary] using
      data.boundaryDagger_eq_adjoint
  have h := rectangularTransitionCoDefect_eq_ambient_add_boundary
    (H := H) (K := K)
    data.oldFrame (ContinuousLinearMap.adjoint data.oldFrame)
      data.newFrame (ContinuousLinearMap.adjoint data.newFrame)
    data.transport (ContinuousLinearMap.adjoint data.transport)
      data.transition (ContinuousLinearMap.adjoint data.transition)
    data.oldFrame_isometry data.newFrame_isometry
    data.transport_intertwining hTransportDagger
  rw [hBoundary] at h
  exact h

theorem RectangularSchurCoDefectStepData.ambientCoDefect_nonneg
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (data : RectangularSchurCoDefectStepData H K) :
    0 ≤ rectangularAmbientCoDefect data.transport
      (ContinuousLinearMap.adjoint data.transport) := by
  have hadjoint_norm : ‖ContinuousLinearMap.adjoint data.transport‖ ≤ 1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact data.transport_norm_le_one
  have hcontract := adjoint_comp_self_le_id_of_norm_le_one
    (ContinuousLinearMap.adjoint data.transport)
    hadjoint_norm
  have hcontract' : data.transport ∘L
      (ContinuousLinearMap.adjoint data.transport) ≤
      ContinuousLinearMap.id ℂ K := by
    simpa only [ContinuousLinearMap.adjoint_adjoint] using hcontract
  exact sub_nonneg.mpr hcontract'

theorem RectangularSchurCoDefectStepData.boundary_coisometry_le_leftCoDefectGram
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (data : RectangularSchurCoDefectStepData H K) :
    data.boundary ∘L (ContinuousLinearMap.adjoint data.boundary) ≤
      (ContinuousLinearMap.adjoint data.leftCoDefect) ∘L data.leftCoDefect := by
  have hAmbient :
      0 ≤ (ContinuousLinearMap.adjoint data.oldFrame) ∘L
        rectangularAmbientCoDefect data.transport
          (ContinuousLinearMap.adjoint data.transport) ∘L
          data.oldFrame := by
    have hpositive :
        (rectangularAmbientCoDefect data.transport
          (ContinuousLinearMap.adjoint data.transport)).IsPositive :=
      (ContinuousLinearMap.nonneg_iff_isPositive _).mp
        data.ambientCoDefect_nonneg
    exact (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
      (hpositive.adjoint_conj data.oldFrame)
  have hSchur :
      rectangularTransitionCoDefect data.transition
          (ContinuousLinearMap.adjoint data.transition) =
        (ContinuousLinearMap.adjoint data.oldFrame) ∘L
            rectangularAmbientCoDefect data.transport
              (ContinuousLinearMap.adjoint data.transport) ∘L
          data.oldFrame +
        data.boundary ∘L (ContinuousLinearMap.adjoint data.boundary) :=
    RectangularSchurCoDefectStepData.schur_coDefect_eq_ambient_add_boundary
      (H := H) (K := K) data
  have hBoundary : data.boundary ∘L
      (ContinuousLinearMap.adjoint data.boundary) ≤
      rectangularTransitionCoDefect data.transition
        (ContinuousLinearMap.adjoint data.transition) := by
    calc
      data.boundary ∘L (ContinuousLinearMap.adjoint data.boundary) =
          (0 : H →L[ℂ] H) +
            data.boundary ∘L (ContinuousLinearMap.adjoint data.boundary) := by
            simp
      _ ≤ (ContinuousLinearMap.adjoint data.oldFrame) ∘L
            rectangularAmbientCoDefect data.transport
              (ContinuousLinearMap.adjoint data.transport) ∘L
              data.oldFrame + data.boundary ∘L
                (ContinuousLinearMap.adjoint data.boundary) := by
            exact add_le_add_left hAmbient
              (data.boundary ∘L (ContinuousLinearMap.adjoint data.boundary))
      _ = rectangularTransitionCoDefect data.transition
          (ContinuousLinearMap.adjoint data.transition) :=
        hSchur.symm
  exact hBoundary.trans_eq
    data.leftCoDefect_adjoint_comp_self.symm

theorem RectangularSchurCoDefectStepData.boundaryDagger_norm_le_leftCoDefect
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (data : RectangularSchurCoDefectStepData H K) (x : H) :
    ‖(ContinuousLinearMap.adjoint data.boundary) x‖ ≤
        ‖data.leftCoDefect x‖ := by
  have horder :
      data.boundary ∘L (ContinuousLinearMap.adjoint data.boundary) ≤
        (ContinuousLinearMap.adjoint data.leftCoDefect) ∘L
          data.leftCoDefect :=
    RectangularSchurCoDefectStepData.boundary_coisometry_le_leftCoDefectGram
      (H := H) (K := K) data
  have hpositive :
      (((ContinuousLinearMap.adjoint data.leftCoDefect) ∘L data.leftCoDefect) -
        data.boundary ∘L (ContinuousLinearMap.adjoint data.boundary)).IsPositive :=
    (ContinuousLinearMap.le_def _ _).mp horder
  have hinner :
      re ⟪(data.boundary ∘L
          (ContinuousLinearMap.adjoint data.boundary)) x, x⟫_ℂ ≤
        re ⟪((ContinuousLinearMap.adjoint data.leftCoDefect) ∘L
          data.leftCoDefect) x, x⟫_ℂ := by
    have hnonneg := hpositive.re_inner_nonneg_left x
    simpa only [ContinuousLinearMap.sub_apply, inner_sub_left, map_sub,
      Complex.sub_re, sub_nonneg] using hnonneg
  have hsq : ‖(ContinuousLinearMap.adjoint data.boundary) x‖ ^ 2 ≤
      ‖data.leftCoDefect x‖ ^ 2 := by
    calc
      ‖(ContinuousLinearMap.adjoint data.boundary) x‖ ^ 2 =
          re ⟪((ContinuousLinearMap.adjoint
            (ContinuousLinearMap.adjoint data.boundary)) ∘L
              (ContinuousLinearMap.adjoint data.boundary)) x, x⟫_ℂ := by
            rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left]
      _ = re ⟪(data.boundary ∘L
          (ContinuousLinearMap.adjoint data.boundary)) x, x⟫_ℂ := by
            rw [ContinuousLinearMap.adjoint_adjoint]
      _ ≤ re ⟪((ContinuousLinearMap.adjoint data.leftCoDefect) ∘L
          data.leftCoDefect) x, x⟫_ℂ := hinner
      _ = ‖data.leftCoDefect x‖ ^ 2 := by
            rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-! Douglas now produces the genuine one-step physical readout. -/
structure RectangularBoundaryCoDefectFactorData
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (data : RectangularSchurCoDefectStepData H K) where
  factor : H →L[ℂ] K
  factor_norm_le_one : ‖factor‖ ≤ 1
  factorization : factor ∘L data.leftCoDefect =
    ContinuousLinearMap.adjoint data.boundary

theorem RectangularBoundaryCoDefectFactorData.factor_adjoint_norm_le_one
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {data : RectangularSchurCoDefectStepData H K}
    (factorData : RectangularBoundaryCoDefectFactorData data) :
    ‖ContinuousLinearMap.adjoint factorData.factor‖ ≤ 1 := by
  rw [ContinuousLinearMap.adjoint.norm_map]
  exact factorData.factor_norm_le_one

/-! The adjoint orientation used by the physical crossing is explicit. -/

theorem RectangularBoundaryCoDefectFactorData.boundary_eq_leftCoDefect_comp_factor_adjoint
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {data : RectangularSchurCoDefectStepData H K}
    (factorData : RectangularBoundaryCoDefectFactorData data) :
    data.boundary = data.leftCoDefect ∘L
      ContinuousLinearMap.adjoint factorData.factor := by
  have h := congrArg ContinuousLinearMap.adjoint factorData.factorization
  have hdefect : IsSelfAdjoint
      (canonicalJuliaDefect (ContinuousLinearMap.adjoint data.transition)
        data.transitionAdjointContract) :=
    canonicalJuliaDefect_isSelfAdjoint
      (ContinuousLinearMap.adjoint data.transition)
      data.transitionAdjointContract
  symm
  simpa only [RectangularSchurCoDefectStepData.leftCoDefect,
    ContinuousLinearMap.adjoint_comp,
    hdefect.adjoint_eq, ContinuousLinearMap.adjoint_adjoint] using h

theorem RectangularBoundaryCoDefectFactorData.boundary_comp_eq_leftCoDefect
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {data : RectangularSchurCoDefectStepData H K}
    (factorData : RectangularBoundaryCoDefectFactorData data)
  (readout : K →L[ℂ] K) :
    data.boundary ∘L readout ∘L data.newFrame =
    data.leftCoDefect ∘L ContinuousLinearMap.adjoint factorData.factor ∘L
      readout ∘L data.newFrame := by
  rw [factorData.boundary_eq_leftCoDefect_comp_factor_adjoint]
  rw [ContinuousLinearMap.comp_assoc]

noncomputable def RectangularSchurCoDefectStepData.boundaryCoDefectFactor
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (data : RectangularSchurCoDefectStepData H K) :
    RectangularBoundaryCoDefectFactorData data := by
  let factorWitness :=
    CCM24FiniteSDouglasFactor.exists_factor_of_norm_le
      (ContinuousLinearMap.adjoint data.boundary) data.leftCoDefect 1
      (by norm_num) (by
        intro x
        simpa only [one_mul] using data.boundaryDagger_norm_le_leftCoDefect x)
  let factor := Classical.choose factorWitness
  have factorSpec := Classical.choose_spec factorWitness
  exact { factor := factor
          factor_norm_le_one := factorSpec.1
          factorization := factorSpec.2 }

noncomputable def RectangularSchurCoDefectStepData.toAdjointCoDefectJuliaStep
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (data : RectangularSchurCoDefectStepData H K) : JuliaDefectStep H H :=
  { transfer := ContinuousLinearMap.adjoint data.transition
    defect := data.leftCoDefect
    rangeSine := 0
    weight := 0
    weight_nonneg := by norm_num
    pythagorean := canonicalJuliaDefect_pythagorean
       (ContinuousLinearMap.adjoint data.transition)
      data.transitionAdjointContract
    rangeSine_weighted_le_defect := by simp }

@[simp]
theorem RectangularSchurCoDefectStepData.toAdjointCoDefectJuliaStep_transfer
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (data : RectangularSchurCoDefectStepData H K) :
    data.toAdjointCoDefectJuliaStep.transfer =
      ContinuousLinearMap.adjoint data.transition :=
  rfl

@[simp]
theorem RectangularSchurCoDefectStepData.toAdjointCoDefectJuliaStep_defect
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (data : RectangularSchurCoDefectStepData H K) :
    data.toAdjointCoDefectJuliaStep.defect = data.leftCoDefect :=
  rfl

noncomputable def CurrentRangeJuliaStepData.toAdjointCoDefectStep
    {H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (data : CurrentRangeJuliaStepData H K G) :
    JuliaDefectStep H H :=
  CCM24FiniteSJuliaBessel.CanonicalJuliaStepData.toAdjointCoDefectStep
    data.toCanonicalJuliaStepData

@[simp]
theorem CurrentRangeJuliaStepData.toAdjointCoDefectStep_transfer
    {H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (data : CurrentRangeJuliaStepData H K G) :
      (CurrentRangeJuliaStepData.toAdjointCoDefectStep data).transfer =
      ContinuousLinearMap.adjoint
        (currentRangeCompressedTransfer data.frame data.ambientTransfer) :=
  rfl

noncomputable def currentRangeJuliaCoDefectSteps
    {H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (steps : List (CurrentRangeJuliaStepData H K G)) :
    List (JuliaDefectStep H H) :=
  steps.map CurrentRangeJuliaStepData.toAdjointCoDefectStep

theorem currentRangeJuliaCoDefectSteps_length
    {H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (steps : List (CurrentRangeJuliaStepData H K G)) :
    (currentRangeJuliaCoDefectSteps steps).length = steps.length := by
  simp [currentRangeJuliaCoDefectSteps]

noncomputable def suffixFixedSourceJuliaCoDefectSteps
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) :
    List (JuliaDefectStep (sourceSoninCarrier lambda)
      (sourceSoninCarrier lambda)) :=
  currentRangeJuliaCoDefectSteps
    (fixedSourceCurrentRangeJuliaSteps lambda stepData S)

theorem suffixFixedSourceJuliaCoDefectSteps_length
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) :
    (suffixFixedSourceJuliaCoDefectSteps lambda stepData S).length =
      S.length := by
  rw [suffixFixedSourceJuliaCoDefectSteps,
    currentRangeJuliaCoDefectSteps_length]
  exact fixedSourceCurrentRangeJuliaSteps_length lambda stepData S

end CCM24FiniteSJuliaCoDefect
end CCM25Concrete
end Source
end ConnesWeilRH
