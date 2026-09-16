/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3SurvivorCoframeBridge
import ConnesWeilRH.Dev.C1G8R3ScaleDetectorRootSquareSum
import ConnesWeilRH.Source.CC20Concrete.HilbertSchmidtIdeal

/-!
# The G8 square-sum gate as an ambient Hilbert-Schmidt normal form

Map 042 work order WO-S3, record 1503 section 2.  The gate

`(★)  Summable i, ‖(J† ∘L C ∘L J)(e_i)‖²`

on the source Sonin carrier is equivalent to the Hilbert-Schmidt column
square-sum of the ambient projection-conjugate `P ∘L C ∘L P` on the global
logarithmic carrier, for any pair of named bases.  The proof is the ambient
column-sum surgery promised by record 1503 section 2: `P = J J†` turns the
ambient conjugate into the lifted detector precomposed by the inclusion
adjoint, and the existing bounded-precomposition square-sum transfer applies
in both directions.  No estimate for the gate is claimed and RH is not
touched.
-/

namespace ConnesWeilRH
namespace Dev

open MeasureTheory
open Source
open Source.CC20Concrete
open Source.CC20Concrete.PositiveTrace
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSActualBandQuadraticCycle
open Source.CCM25Concrete.CCM24FiniteSRootCompletedFirstJet
open Source.CCM25Concrete.CCM24SourceProlateTrace
open Source.CCM25Concrete.SelectedWeilSquare
open scoped InnerProduct InnerProductSpace

noncomputable local instance gateAmbientSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- Pointwise projection identity: the Sonin projection reproduces the
included source vector. -/
theorem gateAmbient_projection_apply_inclusion
    (lambda : CCM24SoninScale)
    (e : sourceSoninCarrier lambda) :
    sourceSoninProjection lambda (sourceInclusion lambda e) =
      sourceInclusion lambda e := by
  have h := congrArg
    (fun T : finiteSCarrier →L[ℂ] finiteSCarrier =>
      T (sourceInclusion lambda e))
    (sourceInclusion_comp_adjoint lambda)
  simp only [ContinuousLinearMap.comp_apply] at h
  rw [← h]
  have h2 := congrArg
    (fun T : sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda =>
      T e)
    (sourceInclusion_adjoint_comp_self lambda)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
    at h2
  exact congrArg (sourceInclusion lambda) h2

/-- Pointwise norm identity at the projection: the projected part of a
vector is the included image of the adjoint readout, so the norms agree. -/
theorem gateAmbient_norm_projection_eq_norm_adjoint
    (lambda : CCM24SoninScale) (w : finiteSCarrier) :
    ‖sourceSoninProjection lambda w‖ =
      ‖(sourceInclusion lambda).adjoint w‖ := by
  have h := congrArg
    (fun T : finiteSCarrier →L[ℂ] finiteSCarrier => T w)
    (sourceInclusion_comp_adjoint lambda)
  simp only [ContinuousLinearMap.comp_apply] at h
  rw [← h, g8BridgeSourceInclusion_norm_map]

/-- The ambient projection-conjugate is the compressed detector lifted by
the inclusion and precomposed by the inclusion adjoint: `P C P =
(J ∘L (J† ∘L C ∘L J)) ∘L J†`. -/
theorem gateAmbient_projectionConjugate_eq_lifted_comp_adjoint
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale) :
    (sourceInclusion lambda ∘L
        ((sourceInclusion lambda).adjoint ∘L rootConvolution owner ∘L
          sourceInclusion lambda)) ∘L
      (sourceInclusion lambda).adjoint =
      sourceSoninProjection lambda ∘L rootConvolution owner ∘L
        sourceSoninProjection lambda := by
  apply ContinuousLinearMap.ext
  intro w
  simp only [ContinuousLinearMap.comp_apply,
    ← sourceInclusion_comp_adjoint]

set_option maxHeartbeats 1000000 in
-- reason: the congruence simp rewrites large composed operator terms
/-- The gate normal form (record 1503 section 2): the in-Sonin square-sum
gate on the source carrier holds iff the ambient projection-conjugate
`P ∘L C ∘L P` has square-summable columns on any named ambient basis. -/
theorem gateAmbient_iff_sourceGate_squareSum
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    {ρ ν : Type*}
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    (Summable fun i : ρ =>
      ‖((sourceInclusion lambda).adjoint ∘L rootConvolution owner ∘L
          sourceInclusion lambda) (sourceBasis i)‖ ^ 2) ↔
    Summable fun j : ν =>
      ‖(sourceSoninProjection lambda ∘L rootConvolution owner ∘L
          sourceSoninProjection lambda) (globalBasis j)‖ ^ 2 := by
  constructor
  · -- gate → ambient: lift the detector by the isometric inclusion, then
    -- precompose by the bounded inclusion adjoint.
    intro hgate
    have hlift : Summable fun i : ρ =>
        ‖(sourceInclusion lambda ∘L
            ((sourceInclusion lambda).adjoint ∘L rootConvolution owner ∘L
              sourceInclusion lambda)) (sourceBasis i)‖ ^ 2 := by
      refine Summable.congr hgate (fun i => ?_)
      exact congrArg (fun z : ℝ => z ^ 2)
        (g8BridgeSourceInclusion_norm_map lambda
          (((sourceInclusion lambda).adjoint ∘L rootConvolution owner ∘L
            sourceInclusion lambda) (sourceBasis i))).symm
    have hprecomp := PositiveTrace.summable_normSq_precomp sourceBasis
      globalBasis globalBasis
      (sourceInclusion lambda ∘L
        ((sourceInclusion lambda).adjoint ∘L rootConvolution owner ∘L
          sourceInclusion lambda))
      ((sourceInclusion lambda).adjoint) hlift
    refine Summable.congr hprecomp (fun j => ?_)
    exact congrArg (fun v : finiteSCarrier => ‖v‖ ^ 2)
      (congrArg (fun T : finiteSCarrier →L[ℂ] finiteSCarrier =>
        T (globalBasis j))
        (gateAmbient_projectionConjugate_eq_lifted_comp_adjoint owner
          lambda))
  · -- ambient → gate: precompose the ambient conjugate by the inclusion;
    -- the projected part is exactly the in-Sonin readout.
    intro hamb
    have hprecomp := PositiveTrace.summable_normSq_precomp globalBasis
      globalBasis sourceBasis
      (sourceSoninProjection lambda ∘L rootConvolution owner ∘L
        sourceSoninProjection lambda)
      (sourceInclusion lambda) hamb
    refine Summable.congr hprecomp (fun i => ?_)
    simp only [ContinuousLinearMap.comp_apply,
      gateAmbient_projection_apply_inclusion]
    rw [gateAmbient_norm_projection_eq_norm_adjoint]

set_option maxHeartbeats 1000000 in
-- reason: the projection split is transported through several composed maps
/-- The source-compressed gate is equivalent to the full detector energy on
  the included source carrier once the already-controlled Sonin leakage is
  supplied.  This is the live S3 reduction; it does not assert either side. -/
theorem sourceGate_squareSum_iff_sourceInputEnergy
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    {ρ : Type*}
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) :
    (Summable fun i : ρ =>
      ‖((sourceInclusion lambda).adjoint ∘L rootConvolution owner ∘L
          sourceInclusion lambda) (sourceBasis i)‖ ^ 2) ↔
    (Summable fun i : ρ =>
      ‖(rootConvolution owner ∘L sourceInclusion lambda)
        (sourceBasis i)‖ ^ 2) := by
  let gate := (sourceInclusion lambda).adjoint ∘L
    rootConvolution owner ∘L sourceInclusion lambda
  let full := rootConvolution owner ∘L sourceInclusion lambda
  let leak := (ContinuousLinearMap.id ℂ finiteSCarrier -
    sourceSoninProjection lambda) ∘L full
  have hleak : Summable fun i : ρ => ‖leak (sourceBasis i)‖ ^ 2 := by
    simpa only [leak, full] using
      (selectedRoot_sourceSoninLeakage_sourceBasis_normSq_summable
        owner lambda sourceBasis)
  have hsplit (i : ρ) :
      ‖full (sourceBasis i)‖ ^ 2 =
        ‖gate (sourceBasis i)‖ ^ 2 + ‖leak (sourceBasis i)‖ ^ 2 := by
    simpa only [gate, full, leak, ContinuousLinearMap.comp_apply] using
      (g8BridgeSoninCarrier_normSq_split lambda
        (rootConvolution owner (sourceInclusion lambda (sourceBasis i))))
  constructor
  · intro hgate
    have hsum := hgate.add hleak
    exact hsum.congr (fun i => (hsplit i).symm)
  · intro hfull
    apply Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => ?_) hfull
    rw [hsplit i]
    exact le_add_of_nonneg_right (sq_nonneg _)

set_option maxHeartbeats 1000000 in
-- reason: the prolate subtraction is expanded through five composed maps
/-- The remaining S3 gate is exactly the Hardy-compressed root energy.  The
prolate correction is already Hilbert--Schmidt after the bounded source input,
so it can be removed from the square-sum obligation. -/
theorem sourceGate_squareSum_iff_hardyCompressedRootEnergy
    (owner : SelectedWeilSquareOwner) (lambda : CCM24SoninScale)
    {ρ : Type*}
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) :
    (Summable fun i : ρ =>
      ‖((sourceInclusion lambda).adjoint ∘L rootConvolution owner ∘L
          sourceInclusion lambda) (sourceBasis i)‖ ^ 2) ↔
    (Summable fun i : ρ =>
      ‖(radialSupportProjection lambda ∘L
          sourceFourierSupportProjection lambda ∘L
          radialSupportProjection lambda ∘L rootConvolution owner ∘L
          sourceInclusion lambda) (sourceBasis i)‖ ^ 2) := by
  let C := rootConvolution owner
  let J := sourceInclusion lambda
  let P := sourceSoninProjection lambda
  let E := radialSupportProjection lambda
  let Q := sourceFourierSupportProjection lambda
  let K := sourceProlateHilbertSchmidtFactor lambda
  let gate := J.adjoint ∘L C ∘L J
  let projected := P ∘L C ∘L J
  let hardy := E ∘L Q ∘L E ∘L C ∘L J
  let remainder := (sourceProlateRemainder lambda) ∘L C ∘L J
  let factorLeg := K ∘L C ∘L J
  let globalBasisIndex := Classical.choose (exists_hilbertBasis ℂ finiteSCarrier)
  let globalBasis :=
    Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ finiteSCarrier))
  have hfactorLeg : Summable fun i : ρ => ‖factorLeg (sourceBasis i)‖ ^ 2 := by
    simpa only [factorLeg, K, C, J] using
      (PositiveTrace.summable_normSq_precomp globalBasis globalBasis sourceBasis
        K (C ∘L J)
        (sourceProlateHilbertSchmidtFactor_summable_all_scales globalBasis lambda))
  have hprolate : Summable fun i : ρ => ‖remainder (sourceBasis i)‖ ^ 2 := by
    have hpost := PositiveTrace.summable_normSq_postcomp sourceBasis
      factorLeg K.adjoint hfactorLeg
    simpa only [remainder, factorLeg, K, C, J,
      ← sourceProlateHilbertSchmidtFactor_adjoint_comp_self lambda,
      ContinuousLinearMap.comp_assoc] using hpost
  have hdecomp : hardy = projected + remainder := by
    unfold hardy projected remainder P E Q C J
    rw [sourceSoninProjection_eq_compression_sub_prolate lambda]
    apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply]
    abel
  have hgate_projected :
      (Summable fun i : ρ => ‖gate (sourceBasis i)‖ ^ 2) ↔
        (Summable fun i : ρ => ‖projected (sourceBasis i)‖ ^ 2) := by
    constructor
    · intro h
      refine h.congr (fun i => ?_)
      exact congrArg (fun r : ℝ => r ^ 2)
        (gateAmbient_norm_projection_eq_norm_adjoint lambda
          (C (J (sourceBasis i)))).symm
    · intro h
      refine h.congr (fun i => ?_)
      exact congrArg (fun r : ℝ => r ^ 2)
        (gateAmbient_norm_projection_eq_norm_adjoint lambda
          (C (J (sourceBasis i))))
  have hprojected_hardy :
      (Summable fun i : ρ => ‖projected (sourceBasis i)‖ ^ 2) ↔
        (Summable fun i : ρ => ‖hardy (sourceBasis i)‖ ^ 2) := by
    constructor
    · intro h
      have hsum := PositiveTrace.summable_normSq_add sourceBasis projected
        remainder h hprolate
      exact hsum.congr (fun i =>
        congrArg (fun v : finiteSCarrier => ‖v‖ ^ 2)
          (DFunLike.congr_fun hdecomp (sourceBasis i)).symm)
    · intro h
      have hneg : Summable fun i : ρ => ‖(-remainder) (sourceBasis i)‖ ^ 2 := by
        simpa only [ContinuousLinearMap.neg_apply, norm_neg] using hprolate
      have hsum := PositiveTrace.summable_normSq_add sourceBasis hardy
        (-remainder) h hneg
      have hcancel : hardy + (-remainder) = projected := by
        apply ContinuousLinearMap.ext
        intro u
        have hu := DFunLike.congr_fun hdecomp u
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply,
          sub_eq_add_neg] at hu ⊢
        calc
          hardy u + -remainder u =
              (projected u + remainder u) + -remainder u := by rw [hu]
          _ = projected u := by abel
      exact hsum.congr (fun i =>
        congrArg (fun v : finiteSCarrier => ‖v‖ ^ 2)
          (DFunLike.congr_fun hcancel (sourceBasis i)))
  simpa only [gate, hardy] using hgate_projected.trans hprojected_hardy

end Dev
end ConnesWeilRH
