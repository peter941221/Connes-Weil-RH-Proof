/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3ActualEndpointTraceLimit
import ConnesWeilRH.Dev.C1G8R3SameOwnerGateNormalForm

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
open Source.CCM25Concrete.CCM24FiniteSGatePhysicalObliqueShearReduction
open Source.C1G8AdjointShearGram
open scoped InnerProduct InnerProductSpace Topology

noncomputable section

noncomputable local instance g8R5SourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

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
