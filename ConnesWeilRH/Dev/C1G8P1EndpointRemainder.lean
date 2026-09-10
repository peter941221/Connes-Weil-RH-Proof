import ConnesWeilRH.Dev.C1G8P1EndpointOrientation
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualBandSourceRemainder

/-!
# G8 P1 endpoint remainder handoff

The endpoint trace orientation is combined with the existing same-owner
first-jet minus remainder decomposition.  The remainder stays explicit.
-/

namespace ConnesWeilRH
namespace Source
namespace C1G8P1EndpointRemainder

open CCM25Concrete
open CC20Concrete
open CCM25Concrete.CCM24FiniteSProjectionTrace
open CCM25Concrete.CCM24FiniteSGramResponse
open CCM25Concrete.CCM24FiniteSBandTrace
open CCM25Concrete.CCM24FiniteSActualBandSourceRemainder
open CCM25Concrete.CCM24FiniteSCommonBoundaryPair
open CCM25Concrete.CCM24SourceProlateTrace
open CC20Concrete.CompactRootHalfLinePair
open C1G8P1MetricChannels
open C1G8P1EndpointOrientation
open CC20Concrete.PositiveTrace
open MeasureTheory
open scoped InnerProduct InnerProductSpace

noncomputable section

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

set_option maxHeartbeats 1000000 in
theorem ordinaryTraceAlong_g8MetricLeakageSourceCross_eq_neg_star_first_sub_remainder
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ tau ιr κr taur nu mu sigma rho : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis taur ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (pairedBoundaryBasis : HilbertBasis sigma ℂ
      (actualBandPairCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    ordinaryTraceAlong sourceBasis
        ((g8MetricLeakageCoframe lambda family)† ∘L
          detectorOperator owner ∘L sourceInclusion lambda) =
      -star (ordinaryTraceAlong sourceBasis
        (sourceActualBandFiniteEulerSoninResponse owner lambda family) -
        ordinaryTraceAlong sourceBasis
          (sourceActualBandFiniteEulerRemainderResponse owner lambda family)) := by
  rw [ordinaryTraceAlong_g8MetricLeakageSourceCross_eq_neg_star_sourceBand]
  rw [ordinaryTraceAlong_sourceBandGramResponse_eq_first_sub_remainder
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor]

end
end C1G8P1EndpointRemainder
end Source
end ConnesWeilRH
