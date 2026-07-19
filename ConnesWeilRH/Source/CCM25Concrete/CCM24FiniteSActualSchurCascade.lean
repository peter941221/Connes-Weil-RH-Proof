/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSJuliaCoDefect
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSTransportBounds

/-!
# Actual consecutive-frame Schur cascade

The fixed-source Julia adapter has one frame per suffix, but a co-defect
identity is a relation between two consecutive frames.  This module makes
that relation explicit.  The ambient map is the normalized genuine Euler
factor, the old and new frames are the actual polar frames of the adjacent
Sonin subspaces, and the source transition is defined by the old-frame
adjoint.

This is intentionally separate from the single-slice `normalizedSchurFrame`.
The latter is a Schur factor on one projected carrier; it is not silently
promoted to an inter-suffix transport.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSActualSchurCascade

open CC20Concrete
open CCM24FiniteSActualJuliaInput
open CCM24FiniteSJuliaCoDefect
open CCM24FiniteSJuliaBessel
open CCM24FiniteSJuliaCausal
open CCM24FiniteSJuliaSchur
open CCM24FiniteSParameterizedEulerEquiv
open CCM24FiniteSParameterizedSoninSubspace
open CCM24FiniteSFixedSourcePolar
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSTransportBounds

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! The two actual adjacent polar frames. -/

noncomputable def oldSuffixFrame
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  parameterizedSoninPolarFrame lambda 1 (p :: S) (by norm_num)

noncomputable def newSuffixFrame
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    sourceSoninCarrier lambda →L[ℂ] finiteSCarrier :=
  parameterizedSoninPolarFrame lambda 1 S (by norm_num)

/-!
The scalar normalization is the upper Euler normalization.  Its purpose is
precisely to make the actual ambient factor contractive before it is
compressed between consecutive isometric frames.
-/

noncomputable def normalizedPrimeEulerFrameTransport
    (p : CCM24VisiblePrime) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  ((1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹) •
    (ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap

theorem normalizedPrimeEulerFrameTransport_norm_le_one
    (p : CCM24VisiblePrime) :
    ‖normalizedPrimeEulerFrameTransport p‖ ≤ 1 := by
  have hdenom : 0 < 1 + ccm24PrimeEulerCoefficient p := by
    exact add_pos_of_pos_of_nonneg zero_lt_one
      (ccm24PrimeEulerCoefficient_nonneg p)
  have hscalar :
      ‖((1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹)‖ =
        (1 + ccm24PrimeEulerCoefficient p)⁻¹ := by
    have hcast :
        (1 + (ccm24PrimeEulerCoefficient p : ℂ)) =
          ((1 + ccm24PrimeEulerCoefficient p : ℝ) : ℂ) := by
      norm_num
    rw [norm_inv, hcast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hdenom]
  have htransport :
      ‖(ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap‖ ≤
        1 + ccm24PrimeEulerCoefficient p := by
    apply ContinuousLinearMap.opNorm_le_bound _
      (le_of_lt hdenom)
    intro u
    change ‖ccm24PrimeEulerTransportEquiv p u‖ ≤
      (1 + ccm24PrimeEulerCoefficient p) * ‖u‖
    exact primeEulerTransport_upper_bound p u
  rw [normalizedPrimeEulerFrameTransport, norm_smul, hscalar]
  calc
    (1 + ccm24PrimeEulerCoefficient p)⁻¹ *
          ‖(ccm24PrimeEulerTransportEquiv p).toContinuousLinearMap‖ ≤
        (1 + ccm24PrimeEulerCoefficient p)⁻¹ *
          (1 + ccm24PrimeEulerCoefficient p) := by
      exact mul_le_mul_of_nonneg_left htransport
        (le_of_lt (inv_pos.mpr hdenom))
    _ = 1 := by field_simp [ne_of_gt hdenom]

/-! A frame image is a member of its concrete Sonin carrier. -/

theorem newSuffixFrame_mem
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (x : sourceSoninCarrier lambda) :
    newSuffixFrame lambda S x ∈
      (parameterizedSoninClosedSubspace lambda 1 S (by norm_num)).toSubmodule := by
  have hrange := parameterizedSoninPolarFrame_range lambda 1 S (by norm_num)
  have hx : newSuffixFrame lambda S x ∈
      (newSuffixFrame lambda S).range := ⟨x, rfl⟩
  dsimp [newSuffixFrame] at hx
  rw [hrange] at hx
  exact hx

/-!
The genuine Euler factor maps the suffix Sonin carrier to the preceding
carrier.  The proof uses the exact finite Euler product recursion and the
closed-submodule transport theorem; no oblique projection is introduced.
-/

theorem normalizedPrimeEulerFrameTransport_mem_oldSuffix
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (x : sourceSoninCarrier lambda) :
    normalizedPrimeEulerFrameTransport p
        (newSuffixFrame lambda S x) ∈
      (parameterizedSoninClosedSubspace lambda 1 (p :: S) (by norm_num)).toSubmodule := by
  have hnew := newSuffixFrame_mem lambda S x
  let T := parameterizedFiniteEulerEquiv 1 S (by norm_num)
  let T' := parameterizedFiniteEulerEquiv 1 (p :: S) (by norm_num)
  let source := ccm24ArchimedeanSoninClosedSubspace lambda
  have hnewMap : newSuffixFrame lambda S x ∈
      ClosedSubmodule.mapEquiv T source := by
    rw [parameterizedFiniteEulerEquiv_maps_sonin]
    exact hnew
  have hpre : T.symm (newSuffixFrame lambda S x) ∈ source := by
    exact (ClosedSubmodule.mem_mapEquiv_iff T source
      (newSuffixFrame lambda S x)).1 hnewMap
  have holdMap : T' (T.symm (newSuffixFrame lambda S x)) ∈
      ClosedSubmodule.mapEquiv T' source := by
    apply (ClosedSubmodule.mem_mapEquiv_iff T' source
      (T' (T.symm (newSuffixFrame lambda S x)))).2
    simpa using hpre
  have hold : T' (T.symm (newSuffixFrame lambda S x)) ∈
      (parameterizedSoninClosedSubspace lambda 1 (p :: S) (by norm_num)).toSubmodule := by
    rw [parameterizedFiniteEulerEquiv_maps_sonin] at holdMap
    exact holdMap
  have hrepr : newSuffixFrame lambda S x =
      ccm24FiniteEulerTransportEquiv S
        (T.symm (newSuffixFrame lambda S x)) := by
    calc
      newSuffixFrame lambda S x =
          T (T.symm (newSuffixFrame lambda S x)) :=
        (T.apply_symm_apply _).symm
      _ = ccm24FiniteEulerTransportEquiv S
          (T.symm (newSuffixFrame lambda S x)) := by
        rw [show T = ccm24FiniteEulerTransportEquiv S by
          simpa only [T] using parameterizedFiniteEulerEquiv_one S]
  have hEuler :
      ccm24PrimeEulerTransportEquiv p
          (newSuffixFrame lambda S x) =
        T' (T.symm (newSuffixFrame lambda S x)) := by
    calc
      ccm24PrimeEulerTransportEquiv p
          (newSuffixFrame lambda S x) =
          ccm24PrimeEulerTransportEquiv p
            (ccm24FiniteEulerTransportEquiv S
              (T.symm (newSuffixFrame lambda S x))) := by
        exact congrArg (ccm24PrimeEulerTransportEquiv p) hrepr
      _ = ccm24FiniteEulerTransportEquiv (p :: S)
          (T.symm (newSuffixFrame lambda S x)) := by
        exact (ccm24FiniteEulerTransportEquiv_cons_apply p S
          (T.symm (newSuffixFrame lambda S x))).symm
      _ = T' (T.symm (newSuffixFrame lambda S x)) := by
        rw [show T' = ccm24FiniteEulerTransportEquiv (p :: S) by
          simpa only [T'] using parameterizedFiniteEulerEquiv_one (p :: S)]
  change ((1 + (ccm24PrimeEulerCoefficient p : ℂ))⁻¹) •
      ccm24PrimeEulerTransportEquiv p (newSuffixFrame lambda S x) ∈
    (parameterizedSoninClosedSubspace lambda 1 (p :: S) (by norm_num)).toSubmodule
  rw [hEuler]
  exact (parameterizedSoninClosedSubspace lambda 1 (p :: S)
    (by norm_num)).toSubmodule.smul_mem _ hold

/-! The compressed transition in the old source coordinate. -/

noncomputable def suffixEulerFrameTransition
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda :=
  ContinuousLinearMap.adjoint (oldSuffixFrame lambda p S) ∘L
    normalizedPrimeEulerFrameTransport p ∘L
      newSuffixFrame lambda S

theorem frame_comp_adjoint_eq_of_mem_range
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (frame : H →L[ℂ] K)
    (hframe : ContinuousLinearMap.adjoint frame ∘L frame =
      ContinuousLinearMap.id ℂ H)
    {y : K} (hy : y ∈ frame.range) :
    frame (ContinuousLinearMap.adjoint frame y) = y := by
  obtain ⟨x, hx⟩ := hy
  calc
    frame (ContinuousLinearMap.adjoint frame y) =
        frame (ContinuousLinearMap.adjoint frame (frame x)) := by
      exact congrArg (fun z : K =>
        frame (ContinuousLinearMap.adjoint frame z)) hx.symm
    _ = frame ((ContinuousLinearMap.adjoint frame ∘L frame) x) := by rfl
    _ = frame ((ContinuousLinearMap.id ℂ H) x) := by rw [hframe]
    _ = y := by simpa using hx

theorem rectangular_frame_transport_norm_le_one
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (oldFrame newFrame : H →L[ℂ] K) (transport : K →L[ℂ] K)
    (hold : ‖oldFrame‖ ≤ 1) (htransport : ‖transport‖ ≤ 1)
    (hnew : ‖newFrame‖ ≤ 1) :
    ‖ContinuousLinearMap.adjoint oldFrame ∘L transport ∘L newFrame‖ ≤ 1 := by
  have holdAdj : ‖ContinuousLinearMap.adjoint oldFrame‖ ≤ 1 := by
    calc
      ‖ContinuousLinearMap.adjoint oldFrame‖ = ‖oldFrame‖ :=
        ContinuousLinearMap.adjoint.norm_map _
      _ ≤ 1 := hold
  calc
    ‖ContinuousLinearMap.adjoint oldFrame ∘L transport ∘L newFrame‖ ≤
        ‖ContinuousLinearMap.adjoint oldFrame ∘L transport‖ *
          ‖newFrame‖ :=
      ContinuousLinearMap.opNorm_comp_le
        (ContinuousLinearMap.adjoint oldFrame ∘L transport) newFrame
    _ ≤ (‖ContinuousLinearMap.adjoint oldFrame‖ * ‖transport‖) *
          ‖newFrame‖ := by
      exact mul_le_mul_of_nonneg_right
        (ContinuousLinearMap.opNorm_comp_le _ _)
        (norm_nonneg newFrame)
    _ ≤ (1 * ‖transport‖) * ‖newFrame‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right holdAdj (norm_nonneg transport))
        (norm_nonneg newFrame)
    _ ≤ (1 * 1) * ‖newFrame‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left htransport zero_le_one)
        (norm_nonneg newFrame)
    _ ≤ (1 * 1) * 1 := by
      exact mul_le_mul_of_nonneg_left hnew (by norm_num)
    _ = 1 := by norm_num

theorem suffixEulerFrameTransition_norm_le_one
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    ‖suffixEulerFrameTransition lambda p S‖ ≤ 1 := by
  have hold : ‖oldSuffixFrame lambda p S‖ ≤ 1 :=
    CCM24FiniteSJuliaCausal.norm_le_one_of_isometric_inclusion
      (oldSuffixFrame lambda p S) (by
      intro x
      exact parameterizedSoninPolarFrame_isometry lambda 1 (p :: S)
        (by norm_num) x)
  have hnew : ‖newSuffixFrame lambda S‖ ≤ 1 :=
    CCM24FiniteSJuliaCausal.norm_le_one_of_isometric_inclusion
      (newSuffixFrame lambda S) (by
      intro x
      exact parameterizedSoninPolarFrame_isometry lambda 1 S
        (by norm_num) x)
  have htransport := normalizedPrimeEulerFrameTransport_norm_le_one p
  simpa only [suffixEulerFrameTransition] using
    rectangular_frame_transport_norm_le_one
      (oldSuffixFrame lambda p S) (newSuffixFrame lambda S)
      (normalizedPrimeEulerFrameTransport p) hold htransport hnew

/-! The actual one-step rectangular Schur owner. -/

noncomputable def suffixEulerFrameSchurStep
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) :
    RectangularSchurCoDefectStepData
      (sourceSoninCarrier lambda) finiteSCarrier := by
  let oldFrame := oldSuffixFrame lambda p S
  let newFrame := newSuffixFrame lambda S
  let ambientTransport := normalizedPrimeEulerFrameTransport p
  let sourceTransition := suffixEulerFrameTransition lambda p S
  refine
    { oldFrame := oldFrame
      newFrame := newFrame
      transport := ambientTransport
      transition := sourceTransition
      oldFrame_isometry := by
        simpa only [oldFrame] using
          parameterizedSoninPolarFrame_adjoint_comp_self lambda 1 (p :: S)
            (by norm_num)
      newFrame_isometry := by
        simpa only [newFrame] using
          parameterizedSoninPolarFrame_adjoint_comp_self lambda 1 S
            (by norm_num)
      transport_norm_le_one := by
        simpa only [ambientTransport] using
          normalizedPrimeEulerFrameTransport_norm_le_one p
      transition_norm_le_one := by
        simpa only [sourceTransition] using
          suffixEulerFrameTransition_norm_le_one lambda p S
      transport_intertwining := by
        apply ContinuousLinearMap.ext
        intro x
        let y := ambientTransport (newFrame x)
        have hy : y ∈ oldFrame.range := by
          change normalizedPrimeEulerFrameTransport p
              (newSuffixFrame lambda S x) ∈ oldFrame.range
          rw [show oldFrame.range =
              (parameterizedSoninClosedSubspace lambda 1 (p :: S) (by norm_num)).toSubmodule by
            dsimp [oldFrame]
            exact parameterizedSoninPolarFrame_range lambda 1 (p :: S)
              (by norm_num)]
          exact normalizedPrimeEulerFrameTransport_mem_oldSuffix lambda p S x
        have hframe := frame_comp_adjoint_eq_of_mem_range oldFrame
          (by
            simpa only [oldFrame] using
              parameterizedSoninPolarFrame_adjoint_comp_self lambda 1 (p :: S)
                (by norm_num)) hy
        change y = oldFrame (ContinuousLinearMap.adjoint oldFrame y)
        exact hframe.symm
      boundaryDagger_eq_adjoint :=
        rectangularBoundaryCompressionDagger_eq_adjoint oldFrame ambientTransport
          newFrame }

/-! Chronological suffix list and its genuine co-defect history. -/

noncomputable def suffixEulerFrameSchurSteps
    (lambda : CCM24SoninScale) :
    List CCM24VisiblePrime →
      List (RectangularSchurCoDefectStepData
        (sourceSoninCarrier lambda) finiteSCarrier)
  | [] => []
  | p :: S =>
      suffixEulerFrameSchurStep lambda p S ::
        suffixEulerFrameSchurSteps lambda S

noncomputable def suffixEulerFrameCoDefectSteps
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    List (JuliaDefectStep (sourceSoninCarrier lambda)
      (sourceSoninCarrier lambda)) :=
  (suffixEulerFrameSchurSteps lambda S).map
    RectangularSchurCoDefectStepData.toAdjointCoDefectJuliaStep

theorem suffixEulerFrameSchurSteps_length
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    (suffixEulerFrameSchurSteps lambda S).length = S.length := by
  induction S with
  | nil => rfl
  | cons p S ih => simp [suffixEulerFrameSchurSteps, ih]

theorem suffixEulerFrameCoDefectSteps_length
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime) :
    (suffixEulerFrameCoDefectSteps lambda S).length = S.length := by
  simp [suffixEulerFrameCoDefectSteps,
    suffixEulerFrameSchurSteps_length lambda S]

theorem suffixEulerFrameCoDefectColumn_normSq_le
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    (x : sourceSoninCarrier lambda) :
    ‖juliaDefectColumn (suffixEulerFrameCoDefectSteps lambda S) x‖ ^ 2 ≤
      ‖x‖ ^ 2 := by
  exact juliaDefectColumn_normSq_le_normSq
    (suffixEulerFrameCoDefectSteps lambda S) x

/-!
The normalized Schur frame has the old projection as a left support.  This
is the exact range fact needed to turn adjacent polar frames into an
intertwining; it is stronger than merely knowing that the Schur operator is
contractive.
-/

theorem PrimeEulerProjectedJuliaInput.normalizedSchurFrame_left_projection
    (data : PrimeEulerProjectedJuliaInput) :
    data.projection ∘L data.normalizedSchurFrame =
      data.normalizedSchurFrame := by
  apply ContinuousLinearMap.ext
  intro x
  have h := ProjectedUnitaryColligation.projection_mul_schurFrame
    data.toColligation data.toColligation.graphCosine
  have hpoint := congrArg
    (fun T : finiteSCarrier →L[ℂ] finiteSCarrier => T x) h
  change data.projection
      (primeEulerSchurNormalizer data.prime
        (data.toColligation.schurFrame
          data.toColligation.graphCosine x)) =
    primeEulerSchurNormalizer data.prime
      (data.toColligation.schurFrame
        data.toColligation.graphCosine x)
  rw [primeEulerSchurNormalizer]
  simp only [ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, map_smul]
  rw [show data.projection
      (data.toColligation.schurFrame
        data.toColligation.graphCosine x) =
      data.toColligation.schurFrame
        data.toColligation.graphCosine x by
        simpa only [ContinuousLinearMap.mul_apply] using hpoint]

theorem PrimeEulerProjectedJuliaInput.normalizedSchurFrame_mem_projection_range
    (data : PrimeEulerProjectedJuliaInput) (x : finiteSCarrier) :
    data.normalizedSchurFrame x ∈ data.projection.range := by
  have h := congrArg
    (fun T : finiteSCarrier →L[ℂ] finiteSCarrier => T x)
    (PrimeEulerProjectedJuliaInput.normalizedSchurFrame_left_projection data)
  have hpoint : data.projection (data.normalizedSchurFrame x) =
      data.normalizedSchurFrame x := by
    simpa only [ContinuousLinearMap.comp_apply] using h
  exact ⟨data.normalizedSchurFrame x, hpoint⟩

/-!
This is the Schur, rather than raw-Euler, adjacent-frame owner.  It consumes
the source-owned one-step Schur data and stores the consecutive frames and
the compressed transition in one rectangular record.  The old frame is the
`S` suffix carrier; the new frame is the `p :: S` carrier.
-/

noncomputable def suffixActualSchurFrameStep
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime) :
    RectangularSchurCoDefectStepData
      (sourceSoninCarrier lambda) finiteSCarrier := by
  let input := parameterizedPrimeEulerProjectedJuliaInput lambda 1 S
    (by norm_num) p
  let oldFrame := newSuffixFrame lambda S
  let newFrame := oldSuffixFrame lambda p S
  let ambientTransport := input.normalizedSchurFrame
  let sourceTransition :=
    ContinuousLinearMap.adjoint oldFrame ∘L ambientTransport ∘L newFrame
  have htransport : ‖ambientTransport‖ ≤ 1 := by
    dsimp [ambientTransport, input]
    exact CCM24FiniteSJuliaCausal.norm_le_one_of_adjoint_comp_self_le_id
      (parameterizedPrimeEulerProjectedJuliaInput lambda 1 S
        (by norm_num) p).normalizedSchurFrame
      (stepData p S).transfer_contract
  have holdFrame : ContinuousLinearMap.adjoint oldFrame ∘L oldFrame =
      ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
    simpa only [oldFrame] using
      parameterizedSoninPolarFrame_adjoint_comp_self lambda 1 S
        (by norm_num)
  have hnewFrame : ContinuousLinearMap.adjoint newFrame ∘L newFrame =
      ContinuousLinearMap.id ℂ (sourceSoninCarrier lambda) := by
    simpa only [newFrame] using
      parameterizedSoninPolarFrame_adjoint_comp_self lambda 1 (p :: S)
        (by norm_num)
  have htransition : ‖sourceTransition‖ ≤ 1 := by
    have hold : ‖oldFrame‖ ≤ 1 :=
      CCM24FiniteSJuliaCausal.norm_le_one_of_isometric_inclusion
        oldFrame (by
        intro x
        exact parameterizedSoninPolarFrame_isometry lambda 1 S
          (by norm_num) x)
    have hnew : ‖newFrame‖ ≤ 1 :=
      CCM24FiniteSJuliaCausal.norm_le_one_of_isometric_inclusion
        newFrame (by
        intro x
        exact parameterizedSoninPolarFrame_isometry lambda 1 (p :: S)
          (by norm_num) x)
    simpa only [sourceTransition] using
      rectangular_frame_transport_norm_le_one oldFrame newFrame
        ambientTransport hold htransport hnew
  refine
    { oldFrame := oldFrame
      newFrame := newFrame
      transport := ambientTransport
      transition := sourceTransition
      oldFrame_isometry := holdFrame
      newFrame_isometry := hnewFrame
      transport_norm_le_one := htransport
      transition_norm_le_one := htransition
      transport_intertwining := by
        apply ContinuousLinearMap.ext
        intro x
        let y := ambientTransport (newFrame x)
        have hyProjection : y ∈ input.projection.range := by
          change input.normalizedSchurFrame (newFrame x) ∈ input.projection.range
          exact
            (PrimeEulerProjectedJuliaInput.normalizedSchurFrame_mem_projection_range
              input _)
        have hyOld : y ∈ oldFrame.range := by
          have hprojectionRange : input.projection.range =
              (parameterizedSoninClosedSubspace lambda 1 S (by norm_num)).toSubmodule := by
            dsimp [input]
            exact parameterizedPrimeEulerProjectedJuliaInput_projection_range
              lambda 1 S (by norm_num) p
          rw [show oldFrame.range =
              (parameterizedSoninClosedSubspace lambda 1 S (by norm_num)).toSubmodule by
            dsimp [oldFrame]
            exact parameterizedSoninPolarFrame_range lambda 1 S (by norm_num)]
          rw [← hprojectionRange]
          exact hyProjection
        have hframe := frame_comp_adjoint_eq_of_mem_range oldFrame
          holdFrame hyOld
        change y = oldFrame (ContinuousLinearMap.adjoint oldFrame y)
        exact hframe.symm
      boundaryDagger_eq_adjoint :=
        rectangularBoundaryCompressionDagger_eq_adjoint oldFrame ambientTransport
          newFrame }

noncomputable def suffixActualSchurFrameSteps
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S) :
    List CCM24VisiblePrime →
      List (RectangularSchurCoDefectStepData
        (sourceSoninCarrier lambda) finiteSCarrier)
  | [] => []
  | p :: S =>
      suffixActualSchurFrameStep lambda stepData p S ::
        suffixActualSchurFrameSteps lambda stepData S

noncomputable def suffixActualSchurCoDefectSteps
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) :
    List (JuliaDefectStep (sourceSoninCarrier lambda)
      (sourceSoninCarrier lambda)) :=
  (suffixActualSchurFrameSteps lambda stepData S).map
    RectangularSchurCoDefectStepData.toAdjointCoDefectJuliaStep

theorem suffixActualSchurFrameSteps_length
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) :
    (suffixActualSchurFrameSteps lambda stepData S).length = S.length := by
  induction S with
  | nil => rfl
  | cons p S ih => simp [suffixActualSchurFrameSteps, ih]

theorem suffixActualSchurCoDefectSteps_length
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) :
    (suffixActualSchurCoDefectSteps lambda stepData S).length = S.length := by
  simp [suffixActualSchurCoDefectSteps,
    suffixActualSchurFrameSteps_length lambda stepData S]

theorem suffixActualSchurCoDefectColumn_normSq_le
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) (x : sourceSoninCarrier lambda) :
    ‖juliaDefectColumn (suffixActualSchurCoDefectSteps lambda stepData S) x‖ ^ 2 ≤
      ‖x‖ ^ 2 := by
  exact juliaDefectColumn_normSq_le_normSq
    (suffixActualSchurCoDefectSteps lambda stepData S) x

/-!
The local Schur boundary columns are packed in the same chronological
`PiLp` carrier as the co-defect history.  The tail is precomposed by the
adjoint source transition, exactly as in `juliaDefectMaps`.
-/

noncomputable def rectangularBoundaryDaggerMaps
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] :
    List (RectangularSchurCoDefectStepData H K) -> List (H →L[ℂ] K)
  | [] => []
  | step :: steps =>
      step.boundaryDagger ::
        (rectangularBoundaryDaggerMaps steps).map
          (fun f => f ∘L ContinuousLinearMap.adjoint step.transition)

theorem rectangularBoundaryDaggerMaps_length
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (steps : List (RectangularSchurCoDefectStepData H K)) :
    (rectangularBoundaryDaggerMaps steps).length =
      (steps.map
        (fun step => step.toAdjointCoDefectJuliaStep)).length := by
  induction steps with
  | nil => rfl
  | cons step steps ih =>
      simp [rectangularBoundaryDaggerMaps, ih]

noncomputable def rectangularBoundaryDaggerColumn
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (steps : List (RectangularSchurCoDefectStepData H K)) :
    H →L[ℂ] PiLp 2
      (fun _ : Fin (steps.map
        (fun step => step.toAdjointCoDefectJuliaStep)).length => K) :=
  (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : Fin (steps.map
        (fun step => step.toAdjointCoDefectJuliaStep)).length => K)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun i : Fin (steps.map
        (fun step => step.toAdjointCoDefectJuliaStep)).length =>
      (rectangularBoundaryDaggerMaps steps).get
        ⟨i, by
          simpa only [rectangularBoundaryDaggerMaps_length steps] using i.isLt⟩)

@[simp]
theorem rectangularBoundaryDaggerColumn_apply
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (steps : List (RectangularSchurCoDefectStepData H K)) (x : H)
    (i : Fin (steps.map
      (fun step => step.toAdjointCoDefectJuliaStep)).length) :
    rectangularBoundaryDaggerColumn steps x i =
      (rectangularBoundaryDaggerMaps steps).get
        ⟨i, by
          simpa only [rectangularBoundaryDaggerMaps_length steps] using i.isLt⟩ x := by
  rfl

theorem rectangularBoundaryDaggerColumn_normSq_eq
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (steps : List (RectangularSchurCoDefectStepData H K)) (x : H) :
    ‖rectangularBoundaryDaggerColumn steps x‖ ^ 2 =
      ((rectangularBoundaryDaggerMaps steps).map
        (fun f => ‖f x‖ ^ 2)).sum := by
  change ‖WithLp.toLp 2
      (fun i : Fin (steps.map
        (fun step => step.toAdjointCoDefectJuliaStep)).length =>
         rectangularBoundaryDaggerColumn steps x i)‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [rectangularBoundaryDaggerColumn_apply, List.get_eq_getElem]
  let hlen := rectangularBoundaryDaggerMaps_length steps
  have hsum :
      ∑ i : Fin (steps.map
          (fun step => step.toAdjointCoDefectJuliaStep)).length,
          ‖(rectangularBoundaryDaggerMaps steps).get
            ⟨i, by
              rw [hlen]
              exact i.isLt⟩ x‖ ^ 2 =
        ((rectangularBoundaryDaggerMaps steps).map
          (fun f => ‖f x‖ ^ 2)).sum := by
    calc
      ∑ i : Fin (steps.map
          (fun step => step.toAdjointCoDefectJuliaStep)).length,
          ‖(rectangularBoundaryDaggerMaps steps).get
            ⟨i, by
              rw [hlen]
              exact i.isLt⟩ x‖ ^ 2 =
          ∑ i : Fin (rectangularBoundaryDaggerMaps steps).length,
            ‖(rectangularBoundaryDaggerMaps steps).get i x‖ ^ 2 := by
        simpa [hlen] using
          (Equiv.sum_comp (finCongr hlen.symm)
            (fun i : Fin (rectangularBoundaryDaggerMaps steps).length =>
              ‖(rectangularBoundaryDaggerMaps steps).get i x‖ ^ 2))
      _ = ((rectangularBoundaryDaggerMaps steps).map
          (fun f => ‖f x‖ ^ 2)).sum := by
        simpa only [List.get_eq_getElem] using
          (Fin.sum_univ_fun_getElem (rectangularBoundaryDaggerMaps steps)
            (fun f : H →L[ℂ] K => ‖f x‖ ^ 2))
  exact hsum

theorem rectangularBoundaryDaggerMaps_normSq_sum_le
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (steps : List (RectangularSchurCoDefectStepData H K)) (x : H) :
    ((rectangularBoundaryDaggerMaps steps).map
        (fun f => ‖f x‖ ^ 2)).sum ≤
      juliaDefectEnergy
        (steps.map (fun step => step.toAdjointCoDefectJuliaStep)) x := by
  induction steps generalizing x with
  | nil =>
      simp [rectangularBoundaryDaggerMaps, juliaDefectEnergy]
  | cons step steps ih =>
      have hlocal : ‖step.boundaryDagger x‖ ^ 2 ≤
          ‖step.leftCoDefect x‖ ^ 2 := by
        have hnorm : ‖step.boundaryDagger x‖ ≤
            ‖step.leftCoDefect x‖ := by
          rw [RectangularSchurCoDefectStepData.boundaryDagger,
            step.boundaryDagger_eq_adjoint]
          exact step.boundaryDagger_norm_le_leftCoDefect x
        exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hnorm
      have htail := ih (ContinuousLinearMap.adjoint step.transition x)
      simpa only [rectangularBoundaryDaggerMaps, List.map_cons,
        List.map_map, List.sum_cons, ContinuousLinearMap.comp_apply,
        juliaDefectEnergy,
        RectangularSchurCoDefectStepData.toAdjointCoDefectJuliaStep_defect,
        RectangularSchurCoDefectStepData.toAdjointCoDefectJuliaStep_transfer] using
        add_le_add hlocal htail

theorem rectangularBoundaryDaggerColumn_normSq_le
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (steps : List (RectangularSchurCoDefectStepData H K)) (x : H) :
    ‖rectangularBoundaryDaggerColumn steps x‖ ^ 2 ≤
      ‖juliaDefectColumn
        (steps.map (fun step => step.toAdjointCoDefectJuliaStep)) x‖ ^ 2 := by
  rw [rectangularBoundaryDaggerColumn_normSq_eq,
    juliaDefectColumn_normSq_eq]
  exact rectangularBoundaryDaggerMaps_normSq_sum_le steps x

/-!
The actual boundary column preserves square summability on a genuine
Hilbert--Schmidt source input.  This is the unconditional part of the
trace-level stable-coframe ledger: it uses only the column contraction proved
above and does not compare the source input with an unrelated compact root.
-/
theorem rectangularBoundaryDaggerColumn_summable_normSq_of_summable_input
    {ι H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (steps : List (RectangularSchurCoDefectStepData H K))
    (sourceBasis : HilbertBasis ι ℂ H)
    (input : H →L[ℂ] H)
    (hinput : Summable (fun i => ‖input (sourceBasis i)‖ ^ 2)) :
    Summable (fun i =>
      ‖rectangularBoundaryDaggerColumn steps
        (input (sourceBasis i))‖ ^ 2) := by
  have hdefect : Summable (fun i =>
      ‖juliaDefectColumn
        (steps.map (fun step => step.toAdjointCoDefectJuliaStep))
        (input (sourceBasis i))‖ ^ 2) :=
    Summable.of_nonneg_of_le
      (fun i => sq_nonneg _)
      (fun i => juliaDefectColumn_normSq_le_normSq
        (steps.map (fun step => step.toAdjointCoDefectJuliaStep))
        (input (sourceBasis i)))
      hinput
  apply Summable.of_nonneg_of_le
    (fun i => sq_nonneg _)
    (fun i => rectangularBoundaryDaggerColumn_normSq_le steps
      (input (sourceBasis i)))
    hdefect

theorem rectangularBoundaryDaggerColumn_tsum_normSq_le_of_summable_input
    {ι H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (steps : List (RectangularSchurCoDefectStepData H K))
    (sourceBasis : HilbertBasis ι ℂ H)
    (input : H →L[ℂ] H)
    (hinput : Summable (fun i => ‖input (sourceBasis i)‖ ^ 2)) :
    (∑' i, ‖rectangularBoundaryDaggerColumn steps
        (input (sourceBasis i))‖ ^ 2) ≤
      ∑' i, ‖input (sourceBasis i)‖ ^ 2 := by
  have hcolumn :=
    rectangularBoundaryDaggerColumn_summable_normSq_of_summable_input
      steps sourceBasis input hinput
  have hdefect : Summable (fun i =>
      ‖juliaDefectColumn
        (steps.map (fun step => step.toAdjointCoDefectJuliaStep))
        (input (sourceBasis i))‖ ^ 2) :=
    Summable.of_nonneg_of_le
      (fun i => sq_nonneg _)
      (fun i => juliaDefectColumn_normSq_le_normSq
        (steps.map (fun step => step.toAdjointCoDefectJuliaStep))
        (input (sourceBasis i)))
      hinput
  exact (hcolumn.tsum_le_tsum
      (fun i => rectangularBoundaryDaggerColumn_normSq_le steps
        (input (sourceBasis i))) hdefect).trans
    (hdefect.tsum_le_tsum
      (fun i => juliaDefectColumn_normSq_le_normSq
        (steps.map (fun step => step.toAdjointCoDefectJuliaStep))
        (input (sourceBasis i))) hinput)

/-!
Douglas factorization now acts on the complete packed boundary column.  The
factor has norm at most one, so the local boundary contractions are retained
before a later physical signed readout is applied.
-/

structure RectangularSchurCascadeBoundaryCoDefectFactorData
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (steps : List (RectangularSchurCoDefectStepData H K)) where
  factor : PiLp 2
      (fun _ : Fin (steps.map
        (fun step => step.toAdjointCoDefectJuliaStep)).length => H) →L[ℂ]
      PiLp 2
        (fun _ : Fin (steps.map
          (fun step => step.toAdjointCoDefectJuliaStep)).length => K)
  factor_norm_le_one : ‖factor‖ ≤ 1
  factorization :
    factor ∘L juliaDefectColumn
        (steps.map (fun step => step.toAdjointCoDefectJuliaStep)) =
      rectangularBoundaryDaggerColumn steps

noncomputable def rectangularSchurCascadeBoundaryCoDefectFactor
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (steps : List (RectangularSchurCoDefectStepData H K)) :
    RectangularSchurCascadeBoundaryCoDefectFactorData steps := by
  let factorWitness :=
    CCM24FiniteSDouglasFactor.exists_factor_of_norm_sq_le
      (rectangularBoundaryDaggerColumn steps)
      (juliaDefectColumn
        (steps.map (fun step => step.toAdjointCoDefectJuliaStep)))
      1 (by norm_num) (by
        intro x
        simpa only [one_pow, one_mul] using
          rectangularBoundaryDaggerColumn_normSq_le steps x)
  let factor := Classical.choose factorWitness
  have factorSpec := Classical.choose_spec factorWitness
  refine
    { factor := factor
      factor_norm_le_one := by simpa using factorSpec.1
      factorization := factorSpec.2 }

noncomputable def suffixActualSchurBoundaryCoDefectFactor
    (lambda : CCM24SoninScale) {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (stepData : ∀ (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime),
      SuffixPrimeEulerProjectedJuliaSchurFrameStepData lambda G p S)
    (S : List CCM24VisiblePrime) :
    RectangularSchurCascadeBoundaryCoDefectFactorData
      (suffixActualSchurFrameSteps lambda stepData S) :=
  rectangularSchurCascadeBoundaryCoDefectFactor
    (suffixActualSchurFrameSteps lambda stepData S)

end CCM24FiniteSActualSchurCascade
end CCM25Concrete
end Source
end ConnesWeilRH
