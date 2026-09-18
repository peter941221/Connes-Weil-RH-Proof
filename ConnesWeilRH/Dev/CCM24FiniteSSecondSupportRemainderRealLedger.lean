import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRootCompletedDetectorCompletedKernelOperator

/-!
# Real ledger for the coupled second-support/prolate remainder

The coupled remainder is already known to be both trace-class along the
named global basis and skew-adjoint.  This leaf combines those facts into the
exact zero-real-trace statement.  It does not address the translated and
prefix-sandwiched Hermitian response, where the remaining sign problem lives.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSSecondSupportRemainderRealLedger

open MeasureTheory
open CC20Concrete
open CC20Concrete.PositiveTrace
open CCM24FiniteSProjectionTrace
open CCM24FiniteSFixedQuotientCarrier
open CCM24FiniteSCommonBoundaryPair
open CCM24RadialBoundaryPairTransport
open scoped InnerProduct InnerProductSpace

noncomputable section

theorem sourceSecondSupportProlateRemainder_trace_re_eq_zero
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    (ordinaryTraceAlong globalBasis
      (sourceSecondSupportProlateRemainder owner lambda)).re = 0 := by
  have hadj := sourceSecondSupportProlateRemainder_adjoint_eq_neg owner lambda
  have hstar := ordinaryTraceAlong_adjoint globalBasis
    (sourceSecondSupportProlateRemainder owner lambda)
  rw [hadj] at hstar
  have hre := congrArg Complex.re hstar
  have hsum :
      -(ordinaryTraceAlong globalBasis
        (sourceSecondSupportProlateRemainder owner lambda)).re =
        (ordinaryTraceAlong globalBasis
          (sourceSecondSupportProlateRemainder owner lambda)).re := by
    simpa [ordinaryTraceAlong, tsum_neg, Complex.star_def] using hre
  linarith

end
end CCM24FiniteSSecondSupportRemainderRealLedger
end CCM25Concrete
end Source
end ConnesWeilRH
