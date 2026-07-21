/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSEndpointArithmeticLedger

/-!
# Arithmetic-prefix and completed-residual limits

Trace-class diagonal summability turns the finite `Fin N` prefix traces into
ordinary traces.  This module applies that general limit to the arithmetic
operator and then reads Proof 462's completed residual prefix as the exact
difference between the route trace and the finite-prime sum.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSEndpointArithmeticLimit

open CC20Concrete
open Filter
open MeasureTheory
open scoped InnerProduct InnerProductSpace Matrix Topology
open SelectedCrossingOperatorBridge
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSBandTrace
open CCM24FiniteSMovingBandPrefixCompression
open CCM24FiniteSEndpointArithmeticLedger

noncomputable local instance finiteSCarrierCompleteSpace :
    CompleteSpace finiteSCarrier := inferInstance

/-- A trace-class diagonal is the limit of its ordered finite-prefix matrix
traces. -/
theorem tendsto_trace_basisPrefixMatrix_ordinaryTraceAlong
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    (basis : HilbertBasis ℕ ℂ H)
    (operator : H →L[ℂ] H)
    (htrace : PositiveTrace.IsTraceClassAlong basis operator) :
    Tendsto
      (fun N : ℕ => Matrix.trace (basisPrefixMatrix basis N operator))
      atTop (𝓝 (PositiveTrace.ordinaryTraceAlong basis operator)) := by
  rw [PositiveTrace.IsTraceClassAlong] at htrace
  simpa only [CCM24FiniteSMovingBandPrefixCompression.trace_basisPrefixMatrix_eq_rangeDiagonal,
    PositiveTrace.ordinaryTraceAlong] using htrace.hasSum.tendsto_sum_nat

/-- The arithmetic finite-prefix trace converges to the selected finite-prime
sum already identified by the whole-line crossing owner. -/
theorem tendsto_arithmeticPrefixTrace_eq_finitePrimeSum
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (a c : ℝ) (family : FinitePrimePowerFamily)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    (basis : HilbertBasis ℕ ℂ finiteSCarrier)
    (basisData : ∀ pm : {pm // pm ∈ family.terms},
      GlobalPrimePowerTraceBasisData a c pm.1.1 pm.1.2) :
    Tendsto
      (fun N : ℕ => Matrix.trace (basisPrefixMatrix basis N
        (arithmeticOperator owner family)))
      atTop (𝓝 (∑ pm ∈ family.terms,
        owner.finitePrimeTerm (pm.1 ^ pm.2))) := by
  have htrace := arithmeticOperator_isTraceClassAlong owner a c family hsupp
    basis basisData
  have hlimit := tendsto_trace_basisPrefixMatrix_ordinaryTraceAlong basis
    (arithmeticOperator owner family) htrace
  have hvalue :
      PositiveTrace.ordinaryTraceAlong basis (arithmeticOperator owner family) =
        ∑ pm ∈ family.terms, owner.finitePrimeTerm (pm.1 ^ pm.2) := by
    rw [arithmeticOperator]
    exact ordinaryTraceAlong_eulerLogWeightedGlobalPairTraceOperatorSum_eq_finitePrimeTerm_pow_sum
      owner a c family.terms family.prime family.exponent_ne_zero hsupp basis basisData
  simpa only [hvalue] using hlimit

/-- The completed residual prefix has an exact limit: route ordinary trace
minus the selected finite-prime sum. -/
theorem tendsto_completedResidualPrefix_eq_routeTrace_sub_finitePrimeSum
    (basis : HilbertBasis ℕ ℂ finiteSCarrier)
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (a c : ℝ) (lambda : CCM24SoninScale)
    (family : FinitePrimePowerFamily)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    (basisData : ∀ pm : {pm // pm ∈ family.terms},
      GlobalPrimePowerTraceBasisData a c pm.1.1 pm.1.2)
    (hroute : PositiveTrace.IsTraceClassAlong basis
      (rootSandwichedBandResponse owner lambda family)) :
    Tendsto
      (fun N : ℕ => actualBandEndpointCompletedResidualTrace
        basis N owner lambda family)
      atTop (𝓝 (
        PositiveTrace.ordinaryTraceAlong basis
          (rootSandwichedBandResponse owner lambda family) -
          (∑ pm ∈ family.terms,
            owner.finitePrimeTerm (pm.1 ^ pm.2)))) := by
  have hroot := tendsto_trace_basisPrefixMatrix_ordinaryTraceAlong basis
    (rootSandwichedBandResponse owner lambda family) hroute
  have harithmetic := tendsto_arithmeticPrefixTrace_eq_finitePrimeSum owner
    a c family hsupp basis basisData
  have hdifference :
      (fun N : ℕ => actualBandEndpointCompletedResidualTrace
        basis N owner lambda family) =
        (fun N : ℕ =>
          Matrix.trace (basisPrefixMatrix basis N
            (rootSandwichedBandResponse owner lambda family)) -
          Matrix.trace (basisPrefixMatrix basis N
            (arithmeticOperator owner family))) := by
    funext N
    have h := trace_targetPrefixRootResponse_eq_arithmetic_add_completedResidual
      basis N owner lambda family
    symm
    apply sub_eq_iff_eq_add.mpr
    calc
      Matrix.trace (basisPrefixMatrix basis N
          (rootSandwichedBandResponse owner lambda family)) =
          Matrix.trace (basisPrefixMatrix basis N
            (arithmeticOperator owner family)) +
            actualBandEndpointCompletedResidualTrace basis N owner lambda family := h
      _ = actualBandEndpointCompletedResidualTrace basis N owner lambda family +
          Matrix.trace (basisPrefixMatrix basis N
            (arithmeticOperator owner family)) := add_comm _ _
  rw [hdifference]
  exact hroot.sub harithmetic

end CCM24FiniteSEndpointArithmeticLimit
end CCM25Concrete
end Source
end ConnesWeilRH
