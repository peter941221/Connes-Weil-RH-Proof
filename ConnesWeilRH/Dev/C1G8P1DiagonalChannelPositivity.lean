import ConnesWeilRH.Dev.C1G8P1MetricChannels
import ConnesWeilRH.Dev.C1G8AdjointShearGram

/-!
# G8 P1 diagonal channel positivity

For either literal metric coframe leg, the diagonal channel is a positive
same-owner operator because the detector remains in the middle of an adjoint
conjugation.  This isolates the only potentially signed pieces of the
four-channel expansion: the two mixed channels.
-/

namespace ConnesWeilRH
namespace Source
namespace C1G8P1DiagonalChannelPositivity

open CCM25Concrete
open CC20Concrete
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24FiniteSGramResponse
open CCM25Concrete.CCM24FiniteSFixedSourcePolar
open CCM25Concrete.CCM24FiniteSTransportBounds
open C1G8P1MetricChannels
open C1G8AdjointShearGram
open Dev.C1Stage3ProjectionWindow
open CC20Concrete.PositiveTrace
open scoped InnerProduct InnerProductSpace

noncomputable section

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
    (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

theorem g8MetricCutoffChannel_self_isPositive
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat)
    (leg : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier) :
    (g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n leg leg).IsPositive := by
  have hpos := (detectorOperator_isPositive_for_g8 owner).adjoint_conj
    (leg ∘L (sourceInclusion lambda)† ∘L
      (g8SourceCutoffPairData owner lambda family globalBasis sourceBasis n).left)
  simpa only [g8MetricCutoffChannel, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.comp_assoc] using hpos

theorem g8MetricCutoffChannel_self_trace_re_nonnegative
    {ι ρ : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (globalBasis : HilbertBasis ι ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda)) (n : Nat)
    (leg : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier) :
    0 ≤ (ordinaryTraceAlong sourceBasis
      (g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n leg leg)).re := by
  let T := g8MetricCutoffChannel owner lambda family globalBasis sourceBasis n leg leg
  have hpositive : T.IsPositive := by
    simpa only [T] using
      (g8MetricCutoffChannel_self_isPositive owner lambda family globalBasis sourceBasis n leg)
  have htrace : IsTraceClassAlong sourceBasis T := by
    simpa only [T] using
      (g8MetricCutoffChannel_isTraceClassAlong owner lambda family globalBasis sourceBasis n leg leg)
  change 0 ≤ (ordinaryTraceAlong sourceBasis T).re
  rw [ordinaryTraceAlong]
  rw [Complex.re_tsum htrace]
  exact tsum_nonneg (fun i => hpositive.re_inner_nonneg_right (sourceBasis i))

end
end C1G8P1DiagonalChannelPositivity
end Source
end ConnesWeilRH
