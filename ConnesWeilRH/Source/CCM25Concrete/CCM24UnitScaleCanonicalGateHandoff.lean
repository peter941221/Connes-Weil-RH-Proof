import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCanonicalAdjointEnergyGate
import ConnesWeilRH.Source.CCM25Concrete.CCM24UnitScaleStrictAngle

/-!
# Unit-scale Gate 3U handoff
This leaf plugs the axiom-clean unit-scale
Hilbert--Schmidt factor (`sourceProlateHilbertSchmidtFactor_unit_summable`) into
the adjoint completed-kernel energy handoff at `lambda = unitSoninScale`,
discharging the `hfactor` premise.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24UnitScaleCanonicalGateHandoff

open MeasureTheory
open scoped BigOperators InnerProduct InnerProductSpace
open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSCanonicalRealGate
open CCM24FiniteSCombinedPhysicalEnergyGate
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSFixedPhysicalEnergyBound
open CCM24FiniteSFixedQuotientContractionBound
open CCM24FiniteSGatePhysicalCanonicalCompletedKernelTraceLegality
open CCM24FiniteSGatePhysicalCompletedKernelBridge
open CCM24FiniteSGatePhysicalNormalizedAnomalyBoundaryReadout
open CCM24FiniteSGatePhysicalObliqueShearKernelReduction
open CCM24FiniteSGramOrderingBridge
open CCM24FiniteSGramResponse
open CCM24FiniteSPhysicalLeakage
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRootCompletedDetectorCompletedKernelOperator
open CCM24SourceProlateTrace
open CCM24FiniteSCanonicalAdjointEnergyGate
open CCM24UnitScaleProlateAlignment
open CCM24UnitScaleProlateTraceReduction

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

theorem canonicalRealGate3UAt_unit_of_rightEnergy
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu : Type*}
    (negativeBasis : HilbertBasis iota ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis kappa ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis iotaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier unitSoninScale))
    (hright : sourcePhysicalCoframeCompletedKernelRightEnergy owner unitSoninScale
      (CCM24FiniteSCanonicalCompletedResponse.canonicalFamily owner)
      a c hac hsupp negativeBasis positiveBasis
      outputBasis reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis sourceBasis
        (sourceProlateHilbertSchmidtFactor_unit_summable globalBasis) ≤
        fixedPhysicalEnergyMajorant owner unitSoninScale a c globalBasis) :
    canonicalRealGate3UAt owner unitSoninScale sourceBasis
      (fixedPhysicalEnergyMajorant owner unitSoninScale a c globalBasis) := by
  exact abs_re_ordinaryTraceAlong_targetCommutator_le_of_rightEnergy owner
    unitSoninScale (CCM24FiniteSCanonicalCompletedResponse.canonicalFamily owner)
    a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis
    (sourceProlateHilbertSchmidtFactor_unit_summable globalBasis) hright

end CCM24UnitScaleCanonicalGateHandoff
end CCM25Concrete
end Source
end ConnesWeilRH
