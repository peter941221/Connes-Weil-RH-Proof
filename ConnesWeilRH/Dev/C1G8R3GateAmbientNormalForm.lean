/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3SurvivorCoframeBridge
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

end Dev
end ConnesWeilRH
