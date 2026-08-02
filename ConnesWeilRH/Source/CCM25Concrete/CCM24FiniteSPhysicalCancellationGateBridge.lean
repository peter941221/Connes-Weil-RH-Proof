/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSEndpointContractionGuard
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCombinedPhysicalEnergyContractionReduction
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGateTraceUncomposedEndpointEnergyBridge

/-!
# Gate bridge from physical same-object cancellation

Proof 722 identifies endpoint contraction with the same-object cancellation
of the raw forward coframe against the completed physical leakage. This file
feeds that exact cancellation directly into the existing combined-energy and
Gate trace consumers. It does not prove the cancellation.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSPhysicalCancellationGateBridge

open MeasureTheory
open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSCombinedPhysicalEnergyContractionReduction
open CCM24FiniteSEndpointContractionGuard
open CCM24FiniteSGateTraceUncomposedEndpointEnergyBridge
open CCM24FiniteSCombinedPhysicalEnergyGate
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSFixedPhysicalEnergyBound
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSPhysicalLeakage
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawRemainderCommonPair
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- A same-object cancellation of the raw forward coframe against the complete
physical leakage is exactly the source input needed by the combined physical
right-energy consumer. -/
theorem sourceActualBandCombinedPhysicalRightEnergy_le_of_forward_add_physicalLeakage_eq_zero
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu rho : Type*}
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
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (hcancellation :
      sourceActualBandForwardCoframe lambda family +
          sourcePhysicalCoframeLeakage lambda family = 0) :
    sourceActualBandCombinedPhysicalRightEnergy owner lambda family a c hac
        hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis sourceBasis
        hfactor ≤
      fixedPhysicalEnergyMajorant owner lambda a c globalBasis := by
  have hendpoint :
      ‖sourceActualBandForwardEndpointCoframe lambda family‖ ≤ 1 := by
    exact
      (norm_sourceActualBandForwardEndpointCoframe_le_one_iff_forward_add_physicalLeakage_eq_zero
        lambda family).mpr hcancellation
  exact
    sourceActualBandCombinedPhysicalRightEnergy_le_of_endpoint_contraction
      owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor hendpoint

/-- Gate-facing form of the same cancellation: once the full forward plus
physical leakage cancels, the lower-factor-gauged completed relative response
has the existing family-independent trace bound. -/
theorem lowerFactorGauged_trace_norm_le_of_forward_add_physicalLeakage_eq_zero
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu mu rho : Type*}
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
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (hcancellation :
      sourceActualBandForwardCoframe lambda family +
          sourcePhysicalCoframeLeakage lambda family = 0) :
    ‖ordinaryTraceAlong sourceBasis
        (CCM24FiniteSRawCompletedGaugeOwner.lowerFactorGaugedActualBandCompletedRelativeResponse
          owner lambda family)‖ ≤
      2 * fixedPhysicalEnergyMajorant owner lambda a c globalBasis := by
  have hcombined :=
    sourceActualBandCombinedPhysicalRightEnergy_le_of_forward_add_physicalLeakage_eq_zero
      owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor hcancellation
  exact
    lowerFactorGauged_trace_norm_le_of_uncomposedEndpoint_combinedEnergy
      owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor hcombined

end CCM24FiniteSPhysicalCancellationGateBridge
end CCM25Concrete
end Source
end ConnesWeilRH
