import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRootCompletedDetectorSignedKernelResponse

/-!
# Real trace of the signed compact-root kernel

The compact-root response is skew-adjoint.  Consequently its ordinary named-
basis trace has zero real part.  This is only a cancellation statement: the
coupled second-support/prolate remainder still carries the unresolved sign.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSRootCompletedDetectorSignedKernelReal

open MeasureTheory
open CC20Concrete
open CC20Concrete.PositiveTrace
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSProjectionTrace
open CCM24FiniteSFixedQuotientCarrier
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSRootCompletedDetectorSignedKernelResponse
open scoped InnerProduct InnerProductSpace

noncomputable section

theorem sourceCompactRootSignedKernelOperator_trace_re_eq_zero
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (a c : ℝ) (hac : a ≤ c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    (ordinaryTraceAlong globalBasis
      (sourceCompactRootSignedKernelOperator owner a c)).re = 0 := by
  have hadj := sourceCompactRootSignedKernelOperator_adjoint_eq_neg owner a c
    hac negativeBasis positiveBasis outputBasis globalBasis
  have htrace := ordinaryTraceAlong_adjoint globalBasis
    (sourceCompactRootSignedKernelOperator owner a c)
  rw [hadj] at htrace
  have hre := congrArg Complex.re htrace
  have hsum :
      -(ordinaryTraceAlong globalBasis
        (sourceCompactRootSignedKernelOperator owner a c)).re =
        (ordinaryTraceAlong globalBasis
          (sourceCompactRootSignedKernelOperator owner a c)).re := by
    simpa [ordinaryTraceAlong, tsum_neg, Complex.star_def] using hre
  linarith

end
end CCM24FiniteSRootCompletedDetectorSignedKernelReal
end CCM25Concrete
end Source
end ConnesWeilRH
