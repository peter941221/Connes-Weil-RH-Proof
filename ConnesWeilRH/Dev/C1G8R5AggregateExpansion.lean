/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3ActualEndpointTraceLimit
import ConnesWeilRH.Dev.C1G8R3SameOwnerGateNormalForm
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSEndpointArithmeticLedger
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSMovingBandSelfAdjointTrace
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSMovingBandMatrixCancellation

/-!
# Exact four-channel expansion of the endpoint aggregate

This leaf fixes the paper object before any limiting argument.  The endpoint
operator is the actual composition `J† C† G C J`; expanding the adjoint shear
inside `G` gives the base, two cross channels, and the leakage square.  The
identity is purely algebraic and does not identify the resulting trace with the
Euler/Archimedean/P2 arithmetic ledger.
-/

namespace ConnesWeilRH
namespace Dev

open Source.CC20Concrete
open Source.CC20Concrete.PositiveTrace
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSGramResponse
open Source.CCM25Concrete.CCM24FiniteSCoframeResponse
open Source.CCM25Concrete.CCM24FiniteSBandTrace
open Source.CCM25Concrete.CCM24FiniteSMovingBandPrefixCompression
open Source.CCM25Concrete.CCM24FiniteSRectangularPrefixCycle
open Source.CCM25Concrete.CCM24FiniteSEndpointArithmeticLedger
open Source.CCM25Concrete.CCM24FiniteSMovingBandSelfAdjointTrace
open Source.CCM25Concrete.CCM24FiniteSMovingBandMatrixCancellation
open Source.CCM25Concrete.CCM24FiniteSGatePhysicalObliqueShearReduction
open Source.CCM25Concrete.SelectedCrossingOperatorBridge
open Source.C1G8AdjointShearGram
open scoped InnerProduct InnerProductSpace Topology

noncomputable section

noncomputable local instance g8R5SourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! The only type-correct way to expose the root convolution is to keep the
whole aggregate on the ambient carrier first, and compress it by `J` only at
the end. -/
noncomputable def g8AmbientRootAggregate
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  (rootConvolution owner).adjoint ∘L
    g8AdjointShearGram owner lambda family ∘L rootConvolution owner

theorem g8AmbientRootAggregate_isPositive
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (g8AmbientRootAggregate owner lambda family).IsPositive := by
  unfold g8AmbientRootAggregate
  exact (g8AdjointShearGram_isPositive owner lambda family).adjoint_conj _

theorem g8EndpointSourceCutoffLimitOperator_eq_sourceCompression_ambientRootAggregate
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    g8EndpointSourceCutoffLimitOperator owner lambda family =
      (sourceInclusion lambda).adjoint ∘L
        g8AmbientRootAggregate owner lambda family ∘L sourceInclusion lambda := by
  rfl

set_option maxHeartbeats 1000000 in
theorem g8AmbientRootAggregate_eq_fourTerms
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    g8AmbientRootAggregate owner lambda family =
      (rootConvolution owner).adjoint ∘L detectorOperator owner ∘L
          rootConvolution owner +
        (rootConvolution owner).adjoint ∘L
          finiteEulerPulledObliqueShear lambda family ∘L
            detectorOperator owner ∘L rootConvolution owner +
        (rootConvolution owner).adjoint ∘L detectorOperator owner ∘L
          (finiteEulerPulledObliqueShear lambda family).adjoint ∘L
            rootConvolution owner +
        (rootConvolution owner).adjoint ∘L
          finiteEulerPulledObliqueShear lambda family ∘L
            detectorOperator owner ∘L
              (finiteEulerPulledObliqueShear lambda family).adjoint ∘L
                rootConvolution owner := by
  let C := rootConvolution owner
  let N := finiteEulerPulledObliqueShear lambda family
  let W := detectorOperator owner
  have hadjoint_add (A B : finiteSCarrier →L[ℂ] finiteSCarrier) :
      (A + B)† = A† + B† := by
    apply ContinuousLinearMap.ext
    intro y
    exact ext_inner_right ℂ fun z => by
      simp only [ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.add_apply, inner_add_left, inner_add_right]
  change C† ∘L ((ContinuousLinearMap.id ℂ finiteSCarrier + N†)† ∘L W ∘L
      (ContinuousLinearMap.id ℂ finiteSCarrier + N†)) ∘L C = _
  rw [hadjoint_add, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.adjoint_id]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.id_apply, map_add]
  abel

theorem g8EndpointSourceCutoffLimitOperator_isPositive
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (g8EndpointSourceCutoffLimitOperator owner lambda family).IsPositive := by
  rw [g8EndpointSourceCutoffLimitOperator_eq_sourceCompression_ambientRootAggregate]
  exact (g8AmbientRootAggregate_isPositive owner lambda family).adjoint_conj _

/-! The arithmetic bridge must carry the difference between the ambient G8
aggregate and the already-defined root response as an actual operator.  This
definition is an obligation marker, not a vanishing assumption. -/
noncomputable def g8AmbientArithmeticCorrection
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    finiteSCarrier →L[ℂ] finiteSCarrier :=
  g8AmbientRootAggregate owner lambda family -
    rootSandwichedBandResponse owner lambda family

theorem g8AmbientArithmeticCorrection_adjoint_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (g8AmbientArithmeticCorrection owner lambda family).adjoint =
      g8AmbientArithmeticCorrection owner lambda family := by
  have hadjoint_sub (A B : finiteSCarrier →L[ℂ] finiteSCarrier) :
      (A - B)† = A† - B† := by
    apply ContinuousLinearMap.ext
    intro y
    exact ext_inner_right ℂ fun z => by
      simp only [ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right]
  rw [g8AmbientArithmeticCorrection, hadjoint_sub,
    (g8AmbientRootAggregate_isPositive owner lambda family).isSelfAdjoint.adjoint_eq,
    rootSandwichedBandResponse_adjoint_eq]

theorem trace_basisPrefixMatrix_g8AmbientArithmeticCorrection_im_eq_zero
    (basis : HilbertBasis ℕ ℂ finiteSCarrier) (N : ℕ)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (Matrix.trace (basisPrefixMatrix basis N
      (g8AmbientArithmeticCorrection owner lambda family))).im = 0 := by
  have hmatrix := basisPrefixMatrix_adjoint_eq_conjTranspose basis N
    (g8AmbientArithmeticCorrection owner lambda family)
  rw [g8AmbientArithmeticCorrection_adjoint_eq] at hmatrix
  have htrace : Matrix.trace (basisPrefixMatrix basis N
      (g8AmbientArithmeticCorrection owner lambda family)) =
      star (Matrix.trace (basisPrefixMatrix basis N
        (g8AmbientArithmeticCorrection owner lambda family))) := by
    calc
      Matrix.trace (basisPrefixMatrix basis N
          (g8AmbientArithmeticCorrection owner lambda family)) =
          Matrix.trace (Matrix.conjTranspose (basisPrefixMatrix basis N
            (g8AmbientArithmeticCorrection owner lambda family))) := by
        rw [← hmatrix]
      _ = star (Matrix.trace (basisPrefixMatrix basis N
          (g8AmbientArithmeticCorrection owner lambda family))) := by
        exact Matrix.trace_conjTranspose _
  have him := congrArg Complex.im htrace
  rw [Complex.star_def, Complex.conj_im] at him
  linarith

theorem g8AmbientRootAggregate_eq_rootSandwiched_add_correction
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    g8AmbientRootAggregate owner lambda family =
      rootSandwichedBandResponse owner lambda family +
        g8AmbientArithmeticCorrection owner lambda family := by
  unfold g8AmbientArithmeticCorrection
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
  abel

theorem g8EndpointSourceCutoffLimitOperator_eq_sourceCompression_rootResponse_add_correction
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    g8EndpointSourceCutoffLimitOperator owner lambda family =
      (sourceInclusion lambda).adjoint ∘L
        (rootSandwichedBandResponse owner lambda family +
          g8AmbientArithmeticCorrection owner lambda family) ∘L
            sourceInclusion lambda := by
  rw [g8EndpointSourceCutoffLimitOperator_eq_sourceCompression_ambientRootAggregate,
    g8AmbientRootAggregate_eq_rootSandwiched_add_correction]

theorem trace_basisPrefixMatrix_g8AmbientRootAggregate_eq_rootResponse_add_correction
    (basis : HilbertBasis ℕ ℂ finiteSCarrier) (N : ℕ)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    Matrix.trace (basisPrefixMatrix basis N
        (g8AmbientRootAggregate owner lambda family)) =
      Matrix.trace (basisPrefixMatrix basis N
        (rootSandwichedBandResponse owner lambda family)) +
        Matrix.trace (basisPrefixMatrix basis N
          (g8AmbientArithmeticCorrection owner lambda family)) := by
  rw [g8AmbientRootAggregate_eq_rootSandwiched_add_correction,
    basisPrefixMatrix_add, Matrix.trace_add]

/-! Combining the correction split with the committed arithmetic ledger gives
the exact finite-prefix bookkeeping needed by the endpoint bridge.  No limit
or sign assertion is hidden here: the completed residual and `Delta_G8` both
remain explicit obligations. -/
theorem trace_basisPrefixMatrix_g8AmbientRootAggregate_eq_arithmetic_add_residual_add_correction
    (basis : HilbertBasis ℕ ℂ finiteSCarrier) (N : ℕ)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    Matrix.trace (basisPrefixMatrix basis N
        (g8AmbientRootAggregate owner lambda family)) =
      Matrix.trace (basisPrefixMatrix basis N
        (arithmeticOperator owner family)) +
        actualBandEndpointCompletedResidualTrace basis N owner lambda family +
        Matrix.trace (basisPrefixMatrix basis N
          (g8AmbientArithmeticCorrection owner lambda family)) := by
  rw [trace_basisPrefixMatrix_g8AmbientRootAggregate_eq_rootResponse_add_correction,
    trace_targetPrefixRootResponse_eq_arithmetic_add_completedResidual]

set_option maxHeartbeats 1000000 in
theorem trace_basisPrefixMatrix_g8AmbientRootAggregate_eq_fourChannel_sum
    (basis : HilbertBasis ℕ ℂ finiteSCarrier) (N : ℕ)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    Matrix.trace (basisPrefixMatrix basis N
        (g8AmbientRootAggregate owner lambda family)) =
      Matrix.trace (basisPrefixMatrix basis N
        ((rootConvolution owner).adjoint ∘L detectorOperator owner ∘L
          rootConvolution owner)) +
      Matrix.trace (basisPrefixMatrix basis N
        ((rootConvolution owner).adjoint ∘L
          finiteEulerPulledObliqueShear lambda family ∘L
            detectorOperator owner ∘L rootConvolution owner)) +
      Matrix.trace (basisPrefixMatrix basis N
        ((rootConvolution owner).adjoint ∘L detectorOperator owner ∘L
          (finiteEulerPulledObliqueShear lambda family).adjoint ∘L
            rootConvolution owner)) +
      Matrix.trace (basisPrefixMatrix basis N
        ((rootConvolution owner).adjoint ∘L
          finiteEulerPulledObliqueShear lambda family ∘L
            detectorOperator owner ∘L
              (finiteEulerPulledObliqueShear lambda family).adjoint ∘L
                rootConvolution owner)) := by
  rw [g8AmbientRootAggregate_eq_fourTerms]
  simp only [basisPrefixMatrix_add, Matrix.trace_add]

/-! The arithmetic supplier is exposed directly at the active G8 interface.
The hypotheses are exactly the support and per-prime-power trace data required
by the selected crossing theorem; no G8 positivity or correction estimate is
used. -/
theorem ordinaryTraceAlong_g8ArithmeticOperator_eq_finitePrimeTerm_sum
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (family : FinitePrimePowerFamily)
    (a c : ℝ)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (basisData : ∀ pm : {pm // pm ∈ family.terms},
      GlobalPrimePowerTraceBasisData a c pm.1.1 pm.1.2) :
    PositiveTrace.ordinaryTraceAlong globalBasis
        (arithmeticOperator owner family) =
      ∑ pm ∈ family.terms, owner.finitePrimeTerm (pm.1 ^ pm.2) := by
  rw [arithmeticOperator]
  exact ordinaryTraceAlong_eulerLogWeightedGlobalPairTraceOperatorSum_eq_finitePrimeTerm_pow_sum
    owner a c family.terms family.prime family.exponent_ne_zero hsupp
      globalBasis basisData

set_option maxHeartbeats 1000000 in
theorem g8EndpointSourceCutoffLimitOperator_eq_fourTerms
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    g8EndpointSourceCutoffLimitOperator owner lambda family =
      (sourceInclusion lambda)† ∘L (rootConvolution owner)† ∘L
          detectorOperator owner ∘L rootConvolution owner ∘L
            sourceInclusion lambda +
        (sourceInclusion lambda)† ∘L (rootConvolution owner)† ∘L
          finiteEulerPulledObliqueShear lambda family ∘L
            detectorOperator owner ∘L rootConvolution owner ∘L
              sourceInclusion lambda +
        (sourceInclusion lambda)† ∘L (rootConvolution owner)† ∘L
          detectorOperator owner ∘L
            (finiteEulerPulledObliqueShear lambda family)† ∘L
              rootConvolution owner ∘L sourceInclusion lambda +
        (sourceInclusion lambda)† ∘L (rootConvolution owner)† ∘L
          finiteEulerPulledObliqueShear lambda family ∘L
            detectorOperator owner ∘L
              (finiteEulerPulledObliqueShear lambda family)† ∘L
                rootConvolution owner ∘L sourceInclusion lambda := by
  let J := sourceInclusion lambda
  let C := rootConvolution owner
  let N := finiteEulerPulledObliqueShear lambda family
  let W := detectorOperator owner
  have hadjoint_add (A B : finiteSCarrier →L[ℂ] finiteSCarrier) :
      (A + B)† = A† + B† := by
    apply ContinuousLinearMap.ext
    intro y
    exact ext_inner_right ℂ fun z => by
      simp only [ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.add_apply, inner_add_left, inner_add_right]
  change J† ∘L C† ∘L ((ContinuousLinearMap.id ℂ finiteSCarrier + N†)† ∘L
      W ∘L (ContinuousLinearMap.id ℂ finiteSCarrier + N†)) ∘L C ∘L J = _
  rw [hadjoint_add, ContinuousLinearMap.adjoint_adjoint,
    ContinuousLinearMap.adjoint_id]
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.id_apply, map_add]
  abel

/-! The positive-trace sign is a downstream consumer: once the survivor
square-sum and the single aggregate equality are supplied, the existing
same-owner readback constructor produces the sign without a new C3 estimate.
-/
theorem qw_nonnegative_of_g8_survivorCore_and_aggregate_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    {ν ρ : Type*}
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hcore : Summable fun i : ρ =>
      ‖((sourceInclusion lambda).adjoint ∘L rootConvolution owner ∘L
        sourceInclusion lambda) (sourceBasis i)‖ ^ 2)
    (heq : (ordinaryTraceAlong sourceBasis
          (g8EndpointSourceCutoffLimitOperator owner lambda family)).re
        = Source.C1SameOwnerWeil.qw owner.sourceTest) :
    0 ≤ Source.C1SameOwnerWeil.qw owner.sourceTest := by
  exact qw_nonnegative_of_g8SameOwnerReadbackData owner lambda family
    globalBasis sourceBasis
    (g8R5ZeroRemainderReadbackData owner lambda family globalBasis sourceBasis
      hcore heq)

end
end Dev
end ConnesWeilRH
