/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedSourcePolar
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSInputSideTraceConsumer

/-!
# Isometric-frame owner for the physical Julia column

The existing input-side producer stores a Hilbert--Schmidt root.  A fixed
source polar frame is instead an isometry, so it cannot be inserted into that
producer without making the source basis energy infinite.  This owner keeps
the two physical Hilbert--Schmidt legs as the trace data and uses the
isometric frame only as the input to the genuine Julia range column.

The range-column summability and the physical readout remain explicit.  The
owner therefore removes a carrier restriction, but does not manufacture the
Gate 3U producer.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSIsometricFrameOwner

open CC20Concrete
open CCM24FiniteSBandTrace
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24FiniteSFixedSourcePolar
open CCM24FiniteSJuliaBessel

open scoped InnerProduct InnerProductSpace

variable {H K G : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K]
variable [NormedAddCommGroup G] [InnerProductSpace ℂ G]
variable [CompleteSpace H] [CompleteSpace K] [CompleteSpace G]

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-!
The data are deliberately stated on the physical legs.  The frame is only
the carrier through which the actual finite-S Julia range row is evaluated.
-/
structure IsometricFrameJuliaReadoutData
    {ι : Type*} (sourceBasis : HilbertBasis ι ℂ H) where
  frame : H →L[ℂ] K
  frame_adjoint_comp_self : (ContinuousLinearMap.adjoint frame) ∘L frame =
    ContinuousLinearMap.id ℂ H
  leftLeg : H →L[ℂ] G
  rightLeg : H →L[ℂ] G
  leftLeg_summable_normSq : Summable fun i =>
    ‖leftLeg (sourceBasis i)‖ ^ 2
  steps : List (JuliaDefectStep K G)
  rangeEnergy_summable : Summable fun i =>
    juliaRangeEnergy steps (frame (sourceBasis i))
  factor : PiLp 2 (fun _ : Fin steps.length => G) →L[ℂ] G
  factorBound : ℝ
  factorBound_nonneg : 0 ≤ factorBound
  factor_norm_le : ‖factor‖ ≤ factorBound
  physicalColumn_eq_readout :
    rightLeg = factor ∘L (juliaRangeColumn steps ∘L frame)
  response : H →L[ℂ] H
  response_eq : (ContinuousLinearMap.adjoint leftLeg) ∘L rightLeg = response

noncomputable def IsometricFrameJuliaReadoutData.ofPairData
    {ι : Type*} {sourceBasis : HilbertBasis ι ℂ H}
    (pairData : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis)
    (frame : H →L[ℂ] K)
    (frame_adjoint_comp_self : (ContinuousLinearMap.adjoint frame) ∘L frame =
      ContinuousLinearMap.id ℂ H)
    (steps : List (JuliaDefectStep K G))
    (rangeEnergy_summable : Summable fun i =>
      juliaRangeEnergy steps (frame (sourceBasis i)))
    (factor : PiLp 2 (fun _ : Fin steps.length => G) →L[ℂ] G)
    (factorBound : ℝ) (factorBound_nonneg : 0 ≤ factorBound)
    (factor_norm_le : ‖factor‖ ≤ factorBound)
    (physicalColumn_eq_readout :
      pairData.right = factor ∘L (juliaRangeColumn steps ∘L frame)) :
    IsometricFrameJuliaReadoutData (H := H) (K := K) (G := G) sourceBasis :=
  { frame := frame
    frame_adjoint_comp_self := frame_adjoint_comp_self
    leftLeg := pairData.left
    rightLeg := pairData.right
    leftLeg_summable_normSq := pairData.left_summable_normSq
    steps := steps
    rangeEnergy_summable := rangeEnergy_summable
    factor := factor
    factorBound := factorBound
    factorBound_nonneg := factorBound_nonneg
    factor_norm_le := factor_norm_le
    physicalColumn_eq_readout := physicalColumn_eq_readout
    response := pairData.traceProduct
    response_eq := rfl }

/-!
The fixed-source polar owner can now obtain its readout from the same
operator-level Douglas condition used by the input-side consumer.  The
condition is on every source vector; no basis-only estimate is promoted to an
operator factor.
-/
noncomputable def IsometricFrameJuliaReadoutData.ofOperatorDomination
    {ι : Type*} {sourceBasis : HilbertBasis ι ℂ H}
    (pairData : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis)
    (frame : H →L[ℂ] K)
    (frame_adjoint_comp_self : (ContinuousLinearMap.adjoint frame) ∘L frame =
      ContinuousLinearMap.id ℂ H)
    (steps : List (JuliaDefectStep K G))
    (rangeEnergy_summable : Summable fun i =>
      juliaRangeEnergy steps (frame (sourceBasis i)))
    (factorBound : ℝ) (factorBound_nonneg : 0 ≤ factorBound)
    (hdom : ∀ x : H,
      ‖pairData.right x‖ ≤
        factorBound *
          ‖juliaRangeColumn steps (frame x)‖) :
    IsometricFrameJuliaReadoutData (H := H) (K := K) (G := G) sourceBasis := by
  let rangeColumn : H →L[ℂ]
      PiLp 2 (fun _ : Fin steps.length => G) :=
    juliaRangeColumn steps ∘L frame
  let factorWitness :=
    CCM24FiniteSDouglasFactor.exists_factor_of_norm_le
      pairData.right rangeColumn factorBound factorBound_nonneg (by
        intro x
        exact hdom x)
  let factor := Classical.choose factorWitness
  have factorSpec := Classical.choose_spec factorWitness
  exact IsometricFrameJuliaReadoutData.ofPairData
    (H := H) (K := K) (G := G) pairData frame
    frame_adjoint_comp_self steps rangeEnergy_summable factor factorBound
    factorBound_nonneg factorSpec.1 factorSpec.2.symm

noncomputable def sourcePolarFrameReadoutData
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    {ι G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G]
    (sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda))
    (pairData : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis)
    (steps : List (JuliaDefectStep finiteSCarrier G))
    (rangeEnergy_summable : Summable fun i =>
      juliaRangeEnergy steps
        ((parameterizedSoninPolarFrame lambda 1 S (by norm_num))
          (sourceBasis i)))
    (factor : PiLp 2 (fun _ : Fin steps.length => G) →L[ℂ] G)
    (factorBound : ℝ) (factorBound_nonneg : 0 ≤ factorBound)
    (factor_norm_le : ‖factor‖ ≤ factorBound)
    (physicalColumn_eq_readout :
      pairData.right = factor ∘L
        (juliaRangeColumn steps ∘L
          parameterizedSoninPolarFrame lambda 1 S (by norm_num))) :
    IsometricFrameJuliaReadoutData
      (H := sourceSoninCarrier lambda) (K := finiteSCarrier) (G := G) sourceBasis :=
  IsometricFrameJuliaReadoutData.ofPairData pairData
    (parameterizedSoninPolarFrame lambda 1 S (by norm_num))
    (parameterizedSoninPolarFrame_adjoint_comp_self lambda 1 S (by norm_num))
    steps rangeEnergy_summable factor factorBound factorBound_nonneg
    factor_norm_le physicalColumn_eq_readout

theorem IsometricFrameJuliaReadoutData.factor_through_frame
    {ι : Type*} {sourceBasis : HilbertBasis ι ℂ H}
    (data : IsometricFrameJuliaReadoutData
      (H := H) (K := K) (G := G) sourceBasis)
    (leg : H →L[ℂ] G) :
    (leg ∘L (ContinuousLinearMap.adjoint data.frame)) ∘L data.frame = leg := by
  rw [ContinuousLinearMap.comp_assoc, data.frame_adjoint_comp_self,
    ContinuousLinearMap.comp_id]

theorem IsometricFrameJuliaReadoutData.frame_isometry
    {ι : Type*} {sourceBasis : HilbertBasis ι ℂ H}
    (data : IsometricFrameJuliaReadoutData
      (H := H) (K := K) (G := G) sourceBasis) (x : H) :
    ‖data.frame x‖ = ‖x‖ :=
  ((ContinuousLinearMap.norm_map_iff_adjoint_comp_self data.frame).mpr
    data.frame_adjoint_comp_self) x

theorem IsometricFrameJuliaReadoutData.rangeColumn_normSq_eq
    {ι : Type*} {sourceBasis : HilbertBasis ι ℂ H}
    (data : IsometricFrameJuliaReadoutData
      (H := H) (K := K) (G := G) sourceBasis) (i : ι) :
    ‖juliaRangeColumn data.steps (data.frame (sourceBasis i))‖ ^ 2 =
      juliaRangeEnergy data.steps (data.frame (sourceBasis i)) := by
  exact juliaRangeColumn_normSq_eq data.steps (data.frame (sourceBasis i))

theorem IsometricFrameJuliaReadoutData.rightLeg_normSq_le
    {ι : Type*} {sourceBasis : HilbertBasis ι ℂ H}
    (data : IsometricFrameJuliaReadoutData
      (H := H) (K := K) (G := G) sourceBasis) (i : ι) :
    ‖data.rightLeg (sourceBasis i)‖ ^ 2 ≤
      data.factorBound ^ 2 *
        ‖juliaRangeColumn data.steps (data.frame (sourceBasis i))‖ ^ 2 := by
  have hfactorization := congrArg
    (fun T : H →L[ℂ] G => T (sourceBasis i))
    data.physicalColumn_eq_readout
  have hpoint :
      ‖data.factor (juliaRangeColumn data.steps
        (data.frame (sourceBasis i)))‖ ^ 2 ≤
        (‖data.factor‖ *
          ‖juliaRangeColumn data.steps (data.frame (sourceBasis i))‖) ^ 2 := by
    gcongr
    exact data.factor.le_opNorm _
  have hfactorBound_sq : ‖data.factor‖ ^ 2 ≤
      data.factorBound ^ 2 := by
    have hprod : 0 ≤ (data.factorBound - ‖data.factor‖) *
        (data.factorBound + ‖data.factor‖) :=
      mul_nonneg (sub_nonneg.mpr data.factor_norm_le)
        (add_nonneg data.factorBound_nonneg (norm_nonneg _))
    nlinarith
  rw [show data.rightLeg (sourceBasis i) =
      data.factor (juliaRangeColumn data.steps
        (data.frame (sourceBasis i))) by
        simpa only [ContinuousLinearMap.comp_apply] using hfactorization]
  calc
    ‖data.factor (juliaRangeColumn data.steps
        (data.frame (sourceBasis i)))‖ ^ 2 ≤
        (‖data.factor‖ *
          ‖juliaRangeColumn data.steps
            (data.frame (sourceBasis i))‖) ^ 2 := hpoint
    _ = ‖data.factor‖ ^ 2 *
        ‖juliaRangeColumn data.steps
          (data.frame (sourceBasis i))‖ ^ 2 := by ring
    _ ≤ data.factorBound ^ 2 *
        ‖juliaRangeColumn data.steps
          (data.frame (sourceBasis i))‖ ^ 2 := by
      exact mul_le_mul_of_nonneg_right hfactorBound_sq (sq_nonneg _)

theorem IsometricFrameJuliaReadoutData.rightLeg_summable_normSq
    {ι : Type*} {sourceBasis : HilbertBasis ι ℂ H}
    (data : IsometricFrameJuliaReadoutData
      (H := H) (K := K) (G := G) sourceBasis) :
    Summable fun i => ‖data.rightLeg (sourceBasis i)‖ ^ 2 := by
  have hrange : Summable (fun i =>
      ‖juliaRangeColumn data.steps (data.frame (sourceBasis i))‖ ^ 2) := by
    simpa only [data.rangeColumn_normSq_eq] using data.rangeEnergy_summable
  have hmajorant : Summable (fun i => data.factorBound ^ 2 *
      ‖juliaRangeColumn data.steps (data.frame (sourceBasis i))‖ ^ 2) :=
    hrange.mul_left (data.factorBound ^ 2)
  exact Summable.of_nonneg_of_le
    (fun i => sq_nonneg _)
    (fun i => data.rightLeg_normSq_le i)
    hmajorant

theorem IsometricFrameJuliaReadoutData.traceProduct_eq_response
    {ι : Type*} {sourceBasis : HilbertBasis ι ℂ H}
    (data : IsometricFrameJuliaReadoutData
      (H := H) (K := K) (G := G) sourceBasis) :
    (CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.mk
      data.leftLeg data.rightLeg data.leftLeg_summable_normSq
        data.rightLeg_summable_normSq).traceProduct = data.response := by
  change (ContinuousLinearMap.adjoint data.leftLeg) ∘L data.rightLeg =
    data.response
  exact data.response_eq

theorem IsometricFrameJuliaReadoutData.ordinaryTrace_norm_le
    {ι : Type*} {sourceBasis : HilbertBasis ι ℂ H}
    (data : IsometricFrameJuliaReadoutData
      (H := H) (K := K) (G := G) sourceBasis) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        data.response‖ ≤
      (1 / 2 : ℝ) *
        ((∑' i, ‖data.leftLeg (sourceBasis i)‖ ^ 2) +
          data.factorBound ^ 2 *
            (∑' i, ‖juliaRangeColumn data.steps
              (data.frame (sourceBasis i))‖ ^ 2)) := by
  let pairData :
      CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
        (G := G) sourceBasis :=
    { left := data.leftLeg
      right := data.rightLeg
      left_summable_normSq := data.leftLeg_summable_normSq
      right_summable_normSq := data.rightLeg_summable_normSq }
  have hresponse : pairData.traceProduct = data.response := by
    simpa only [pairData] using data.traceProduct_eq_response
  have htrace : CC20Concrete.PositiveTrace.IsTraceClassAlong sourceBasis
      data.response := by
    rw [← hresponse]
    exact pairData.traceProduct_isTraceClassAlong
  have hdiag : Summable (fun i =>
      ‖⟪sourceBasis i, data.response (sourceBasis i)⟫_ℂ‖) :=
    htrace.norm
  have hleft : Summable (fun i =>
      ‖data.leftLeg (sourceBasis i)‖ ^ 2) :=
    data.leftLeg_summable_normSq
  have hrange : Summable (fun i =>
      ‖juliaRangeColumn data.steps (data.frame (sourceBasis i))‖ ^ 2) := by
    simpa only [data.rangeColumn_normSq_eq] using data.rangeEnergy_summable
  have hrightMajorant : Summable (fun i => data.factorBound ^ 2 *
      ‖juliaRangeColumn data.steps (data.frame (sourceBasis i))‖ ^ 2) :=
    hrange.mul_left (data.factorBound ^ 2)
  have hmajorant : Summable (fun i =>
      (1 / 2 : ℝ) *
        (‖data.leftLeg (sourceBasis i)‖ ^ 2 +
          data.factorBound ^ 2 *
            ‖juliaRangeColumn data.steps
              (data.frame (sourceBasis i))‖ ^ 2)) := by
    have hleft' := hleft.mul_left (1 / 2 : ℝ)
    have hright' := hrightMajorant.mul_left (1 / 2 : ℝ)
    apply (hleft'.add hright').congr
    intro i
    ring
  have hpoint : ∀ i, ‖⟪sourceBasis i,
      data.response (sourceBasis i)⟫_ℂ‖ ≤
      (1 / 2 : ℝ) *
        (‖data.leftLeg (sourceBasis i)‖ ^ 2 +
          data.factorBound ^ 2 *
            ‖juliaRangeColumn data.steps
              (data.frame (sourceBasis i))‖ ^ 2) := by
    intro i
    have hdiagonal :
        ⟪sourceBasis i, data.response (sourceBasis i)⟫_ℂ =
      ⟪data.leftLeg (sourceBasis i), data.rightLeg (sourceBasis i)⟫_ℂ := by
      rw [← hresponse]
      exact pairData.traceProduct_diagonal i
    rw [hdiagonal]
    have hright := data.rightLeg_normSq_le i
    have hsum : ‖data.leftLeg (sourceBasis i)‖ ^ 2 +
        ‖data.rightLeg (sourceBasis i)‖ ^ 2 ≤
      ‖data.leftLeg (sourceBasis i)‖ ^ 2 +
        data.factorBound ^ 2 *
          ‖juliaRangeColumn data.steps
            (data.frame (sourceBasis i))‖ ^ 2 :=
      add_le_add_right hright
        (‖data.leftLeg (sourceBasis i)‖ ^ 2)
    calc
      ‖⟪data.leftLeg (sourceBasis i),
          data.rightLeg (sourceBasis i)⟫_ℂ‖ ≤
          ‖data.leftLeg (sourceBasis i)‖ *
            ‖data.rightLeg (sourceBasis i)‖ :=
        norm_inner_le_norm _ _
      _ ≤ (1 / 2 : ℝ) *
          (‖data.leftLeg (sourceBasis i)‖ ^ 2 +
            ‖data.rightLeg (sourceBasis i)‖ ^ 2) := by
        nlinarith [sq_nonneg
          (‖data.leftLeg (sourceBasis i)‖ -
            ‖data.rightLeg (sourceBasis i)‖)]
      _ ≤ (1 / 2 : ℝ) *
          (‖data.leftLeg (sourceBasis i)‖ ^ 2 +
            data.factorBound ^ 2 *
              ‖juliaRangeColumn data.steps
                (data.frame (sourceBasis i))‖ ^ 2) := by
        exact mul_le_mul_of_nonneg_left hsum (by norm_num)
  rw [CC20Concrete.PositiveTrace.ordinaryTraceAlong]
  calc
    ‖∑' i, ⟪sourceBasis i,
        data.response (sourceBasis i)⟫_ℂ‖ ≤
        ∑' i, ‖⟪sourceBasis i,
          data.response (sourceBasis i)⟫_ℂ‖ :=
      norm_tsum_le_tsum_norm hdiag
    _ ≤ ∑' i, (1 / 2 : ℝ) *
        (‖data.leftLeg (sourceBasis i)‖ ^ 2 +
          data.factorBound ^ 2 *
            ‖juliaRangeColumn data.steps
              (data.frame (sourceBasis i))‖ ^ 2) :=
      hdiag.tsum_le_tsum hpoint hmajorant
    _ = (1 / 2 : ℝ) *
        ((∑' i, ‖data.leftLeg (sourceBasis i)‖ ^ 2) +
          data.factorBound ^ 2 *
            (∑' i, ‖juliaRangeColumn data.steps
              (data.frame (sourceBasis i))‖ ^ 2)) := by
      rw [tsum_mul_left, hleft.tsum_add hrightMajorant,
        tsum_mul_left]

theorem sourceBandGramResponse_ordinaryTrace_norm_le_of_isometricFrameReadout
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    {ι G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)}
    (data : IsometricFrameJuliaReadoutData
      (H := sourceSoninCarrier lambda) (K := finiteSCarrier) (G := G)
        sourceBasis)
    (hresponse : data.response = sourceBandGramResponse owner lambda family) :
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        (sourceBandGramResponse owner lambda family)‖ ≤
      (1 / 2 : ℝ) *
        ((∑' i, ‖data.leftLeg (sourceBasis i)‖ ^ 2) +
          data.factorBound ^ 2 *
            (∑' i, ‖juliaRangeColumn data.steps
              (data.frame (sourceBasis i))‖ ^ 2)) := by
  rw [← hresponse]
  exact data.ordinaryTrace_norm_le

end CCM24FiniteSIsometricFrameOwner
end CCM25Concrete
end Source
end ConnesWeilRH
