/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCombinedPhysicalEnergyGate
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedPhysicalSourceInput
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCommonBoundaryPair
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFrameGramCalculus

/-!
# Gate trace bridge for an uncomposed endpoint energy producer

Proof 712 produces an endpoint/readout equality before a source operator is
composed into the rectangular column.  This module exposes the correct Gate
consumer boundary: a source producer supplies the already-combined physical
right energy, and the existing signed trace consumer is applied directly.
No identity-input Hilbert-basis energy is introduced.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGateTraceUncomposedEndpointEnergyBridge

open MeasureTheory
open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSCombinedPhysicalEnergyGate
open CCM24FiniteSFixedPhysicalEnergyBound
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSProjectionTrace
open CCM24SourceProlateTrace

set_option maxHeartbeats 3000000 in
/-- Direct Gate handoff from the actual combined physical right energy.  The
endpoint/readout producer is intentionally represented by its semantic output
`hcombined`; the consumer does not manufacture a fake source-input
factorization. -/
theorem lowerFactorGauged_trace_norm_le_of_uncomposedEndpoint_combinedEnergy
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
    (hcombined :
      sourceActualBandCombinedPhysicalRightEnergy owner lambda family a c hac
          hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
          reflectedPositiveBasis reflectedOutputBasis globalBasis sourceBasis
          hfactor ≤
        fixedPhysicalEnergyMajorant owner lambda a c globalBasis) :
    ‖ordinaryTraceAlong sourceBasis
        (CCM24FiniteSRawCompletedGaugeOwner.lowerFactorGaugedActualBandCompletedRelativeResponse
          owner lambda family)‖ ≤
      2 * fixedPhysicalEnergyMajorant owner lambda a c globalBasis := by
  exact lowerFactorGaugedActualBandCompletedRelativeResponse_trace_norm_le_of_combinedEnergy
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor hcombined

end CCM24FiniteSGateTraceUncomposedEndpointEnergyBridge
end CCM25Concrete
end Source
end ConnesWeilRH
