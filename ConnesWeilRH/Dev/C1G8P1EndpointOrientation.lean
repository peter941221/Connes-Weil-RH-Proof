import ConnesWeilRH.Dev.C1G8P1MetricChannels
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGramOrderingBridge

/-!
# G8 P1 endpoint orientation bridge

The uncut leakage/source response is aligned with the existing finite-S
source-band owner.  The equality is only an orientation/owner identity; no
finite-prime scalar readback or cutoff limit is asserted here.
-/

namespace ConnesWeilRH
namespace Source
namespace C1G8P1EndpointOrientation

open CCM25Concrete
open CC20Concrete
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24FiniteSGramResponse
open CCM25Concrete.CCM24FiniteSBandTrace
open CCM25Concrete.CCM24FiniteSGramOrderingBridge
open C1G8P1MetricChannels
open C1G8AdjointShearGram
open CC20Concrete.PositiveTrace
open scoped InnerProduct InnerProductSpace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

theorem g8MetricLeakageSourceCross_eq_neg_sourceBandGramResponse_adjoint
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    (g8MetricLeakageCoframe lambda family)† ∘L
        detectorOperator owner ∘L sourceInclusion lambda =
      -(sourceBandGramResponse owner lambda family)† := by
  calc
    (g8MetricLeakageCoframe lambda family)† ∘L
          detectorOperator owner ∘L sourceInclusion lambda =
        finiteEulerTargetCommutatorResponse owner lambda family := by
      exact (finiteEulerTargetCommutatorResponse_eq_g8MetricLeakageCross
        owner lambda family).symm
    _ = leftOrderedSourceGramResponse owner lambda family := by
      exact (leftOrderedSourceGramResponse_eq_targetCommutator
        owner lambda family).symm
    _ = -leftOrderedSourceBandGramResponse owner lambda family := by
      simp only [leftOrderedSourceBandGramResponse, neg_neg]
    _ = -(sourceBandGramResponse owner lambda family)† := by
      rw [leftOrderedSourceBandGramResponse_eq_adjoint]

theorem ordinaryTraceAlong_g8MetricLeakageSourceCross_eq_neg_star_sourceBand
    {ι : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (basis : HilbertBasis ι ℂ (sourceSoninCarrier lambda)) :
    ordinaryTraceAlong basis
        ((g8MetricLeakageCoframe lambda family)† ∘L
          detectorOperator owner ∘L sourceInclusion lambda) =
      -star (ordinaryTraceAlong basis
        (sourceBandGramResponse owner lambda family)) := by
  rw [g8MetricLeakageSourceCross_eq_neg_sourceBandGramResponse_adjoint]
  have hneg (operator : sourceSoninCarrier lambda →L[ℂ]
      sourceSoninCarrier lambda) :
      ordinaryTraceAlong basis (-operator) =
        -ordinaryTraceAlong basis operator := by
    unfold ordinaryTraceAlong
    simp only [ContinuousLinearMap.neg_apply, inner_neg_right, tsum_neg]
  rw [hneg]
  rw [ordinaryTraceAlong_adjoint]

end C1G8P1EndpointOrientation
end Source
end ConnesWeilRH
