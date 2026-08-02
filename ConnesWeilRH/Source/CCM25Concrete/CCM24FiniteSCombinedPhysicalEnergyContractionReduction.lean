/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCombinedPhysicalEnergyGate
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedPhysicalEnergyBound
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedQuotientContractionBound
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRawRemainderCommonPair
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFrameGramCalculus
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCommonBoundaryPair

/-!
# Reduction of the combined physical energy to endpoint contraction

The unresolved combined physical energy is a Hilbert--Schmidt energy of the
fixed three-branch right leg postcomposed with the complete endpoint coframe.
This module proves that a single operator-norm contraction of that endpoint
coframe is sufficient.  It does not assert the contraction; it isolates it as
the exact next source theorem and preserves the complete endpoint object.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCombinedPhysicalEnergyContractionReduction

open MeasureTheory
open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSCombinedPhysicalEnergyGate
open CCM24FiniteSFixedPhysicalEnergyBound
open CCM24FiniteSFixedQuotientContractionBound
open CCM24FiniteSFrameGramCalculus
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawRemainderCommonPair
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

set_option maxHeartbeats 2000000 in
-- The endpoint energy expansion elaborates several dependent Hilbert bases.
/-- A contraction of the complete endpoint coframe closes the combined
physical energy bound.  The left map in `boundedPrecomp` is dummy data; the
right energy depends only on the endpoint coframe. -/
theorem sourceActualBandCombinedPhysicalRightEnergy_le_of_endpoint_contraction
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
    (hendpoint :
      ‖sourceActualBandForwardEndpointCoframe lambda family‖ ≤ 1) :
    sourceActualBandCombinedPhysicalRightEnergy owner lambda family a c hac
        hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis sourceBasis
        hfactor ≤
      fixedPhysicalEnergyMajorant owner lambda a c globalBasis := by
  let base := sourceThreeBranchPairData owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
  let endpoint := sourceActualBandForwardEndpointCoframe lambda family
  have henergy := boundedPrecomp_right_tsum_le_of_norm_le_one
    boundaryBasis sourceBasis base
    (0 : sourceSoninCarrier lambda →L[ℂ] finiteSCarrier) endpoint hendpoint
  have hbase := sourceThreeBranchPairData_right_basisEnergy_le_fixedMajorant
    owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis hfactor
  rw [sourceActualBandCombinedPhysicalRightEnergy]
  calc
    (∑' i, ‖base.right (endpoint (sourceBasis i))‖ ^ 2) ≤
        ∑' i, ‖base.right (globalBasis i)‖ ^ 2 := by
      simpa only [base, endpoint, BasisHilbertSchmidtPairData.boundedPrecomp,
        ContinuousLinearMap.zero_apply, zero_smul, zero_add]
        using henergy
    _ ≤ fixedPhysicalEnergyMajorant owner lambda a c globalBasis := hbase

end CCM24FiniteSCombinedPhysicalEnergyContractionReduction
end CCM25Concrete
end Source
end ConnesWeilRH
