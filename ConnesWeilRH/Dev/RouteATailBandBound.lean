import Mathlib.Analysis.InnerProductSpace.PiL2
import ConnesWeilRH.Source.CC20Concrete.PositiveTrace
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCausalMarkovRawRenewalTailBound

/-!
# Route-A finite-band tail trace bound on the real route carrier

Route A re-points the Gate readout to a decaying *finite band* of the real
route carrier `sourceSoninCarrier lambda`.  This module proves a genuinely
route-object statement: on ANY finite Hilbert band `b` of the real carrier,
the real-part ordinary trace of the **actual library tail operator**
`inverseLowerFactorPhysicalRenewalTailResponse` is bounded by the closed
operator-norm tail bound times the band index cardinality:

```text
|Re Tr_b (Tail)| <= (card rho) * ||Tail||
||Tail||         <= C0 * exp(-B/4) * prod_p quarter-mass   (TailBound:751)
=> |Re Tr_b Tail| <= (card rho) * C0 * exp(-B/4) * prod
```

No trace-class certificate on the infinite carrier is claimed (docs/860
A1/A2 seam); the trace here is the finite diagonal sum over `rho`
(`[Fintype rho]`), which the promoted `PositiveTrace` finite bridge bounds
directly, so this band really closes.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete

open MeasureTheory
open scoped BigOperators InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSCanonicalCompletedResponse
open CCM24FiniteSCanonicalRealGate
open CCM24FiniteSBandTrace
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSForwardRenewal
open CCM24FiniteSGramResponse
open CCM24FiniteSMultiRenewal
open CCM24FiniteSPhysicalRenewalExpansion
open CCM24FiniteSProjectionTrace
open CCM24FiniteSCausalMarkovRawRenewalBridge
open CCM24FiniteSCausalMarkovRawRenewalSupportSplit
open CCM24FiniteSCausalMarkovRawRenewalTailBound
open CCM24FiniteSSupportMajorant
open CCM24FiniteSTwoSidedIndexBridge
open CCM24FiniteSTwoSidedOperatorExpansion
open CCM24FiniteSTwoSidedRenewal
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

namespace RouteATailBandBound

/-- Real-part ordinary trace of the REAL route tail operator, restricted to a
finite band `rho` of the carrier, bounded by band cardinality times the closed
operator-norm tail decay `C0*exp(-B/4)*prod`. -/
theorem finiteBand_tail_trace_le
    {rho : Type*}
    (B : ℝ) (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (b : HilbertBasis rho ℂ (sourceSoninCarrier lambda)) [Fintype rho] :
    ‖(ordinaryTraceAlong b
        (inverseLowerFactorPhysicalRenewalTailResponse B owner lambda family)).re‖ ≤
      (Fintype.card rho : ℝ) *
        (rawRenewalTailNormConstant owner lambda family *
          (Real.exp (-B / 4) * (family.visiblePrimes.map primeTwoSidedQuarterMass).prod)) := by
  let T := inverseLowerFactorPhysicalRenewalTailResponse B owner lambda family
  have hTr := abs_re_ordinaryTraceAlong_le_card_mul_opNorm b T
  have hTail := norm_inverseLowerFactorPhysicalRenewalTailResponse_le_const_exp B owner lambda family
  have hc : 0 ≤ (Fintype.card rho : ℝ) := by positivity
  calc
    ‖(ordinaryTraceAlong b T).re‖ ≤ (Fintype.card rho : ℝ) * ‖T‖ := by simpa [T] using hTr
    _ ≤ (Fintype.card rho : ℝ) *
        (rawRenewalTailNormConstant owner lambda family *
          (Real.exp (-B / 4) * (family.visiblePrimes.map primeTwoSidedQuarterMass).prod)) := by
      exact mul_le_mul_of_nonneg_left hTail hc

theorem finiteBandSupport_le
    {rho : Type*}
    (B : Real) (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (b : HilbertBasis rho Complex (sourceSoninCarrier lambda)) [Fintype rho] :
    ‖(ordinaryTraceAlong b (inverseLowerFactorPhysicalRenewalSupportResponse B owner lambda family)).re‖ <=
      (Fintype.card rho : Real) * ‖(inverseLowerFactorPhysicalRenewalSupportResponse B owner lambda family)‖ :=
  abs_re_ordinaryTraceAlong_le_card_mul_opNorm b (inverseLowerFactorPhysicalRenewalSupportResponse B owner lambda family)


end RouteATailBandBound

end CCM25Concrete
end Source
end ConnesWeilRH



