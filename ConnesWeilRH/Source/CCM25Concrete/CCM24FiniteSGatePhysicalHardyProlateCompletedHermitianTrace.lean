/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalHardyProlateCompletedHermitianKernel
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCanonicalRealGate

/-!
# Trace-level Hermitian completed Hardy--prolate endpoint

This module connects the real canonical Gate directly to the completed
Hardy--prolate physical pairing of Proof 783.  The result only changes the
readout of the same signed kernel; it introduces neither a branchwise estimate
nor a new trace cycle.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGatePhysicalHardyProlateCompletedHermitianTrace

open scoped InnerProduct InnerProductSpace

open MeasureTheory
open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSCanonicalCompletedResponse
open CCM24FiniteSCanonicalRealGate
open CCM24FiniteSGramOrderingBridge
open CCM24FiniteSGramResponse
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGatePhysicalHardyProlateCompletedBoundaryKernel
open CCM24FiniteSGatePhysicalHardyProlateCompletedHermitianKernel
open CCM24FiniteSGatePhysicalTargetHermitianPrefix
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The ordinary Hermitian target trace is the one series of real parts of
the completed physical Hardy--prolate pairing. -/
theorem ordinaryTraceAlong_targetHermitianResponse_eq_completePhysicalBoundaryPairing_re
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu : Type*}
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
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    ordinaryTraceAlong sourceBasis
        (finiteEulerTargetHermitianResponse owner lambda family) =
      ∑' i, ((finiteEulerCausalHardyProlateCompletePhysicalBoundaryPairing
        owner lambda family a c hac hsupp reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
        (sourceBasis i) (sourceBasis i)).re : ℂ) := by
  unfold ordinaryTraceAlong
  apply tsum_congr
  intro i
  exact inner_targetHermitianResponse_eq_completePhysicalBoundaryPairing_re
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis hfactor (sourceBasis i)

/-- The canonical real Gate is exactly a bound for one completed
Hardy--prolate physical trace.  Compact-root support must control this series
before an absolute value is applied to any physical branch. -/
theorem canonicalRealGate3UAt_iff_completePhysicalHermitianBoundaryTraceBound
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {iota kappa tau iotaR kappaR tauR nu : Type*}
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
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (bound : ℝ)
    (htrace : IsTraceClassAlong sourceBasis
      (finiteEulerTargetCommutatorResponse owner lambda
        (canonicalFamily owner))) :
    canonicalRealGate3UAt owner lambda sourceBasis bound ↔
      ‖∑' i, ((finiteEulerCausalHardyProlateCompletePhysicalBoundaryPairing
        owner lambda (canonicalFamily owner) a c hac hsupp reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
        (sourceBasis i) (sourceBasis i)).re : ℂ)‖ ≤ bound := by
  rw [canonicalRealGate3UAt_iff_targetHermitianTraceBound owner lambda
    sourceBasis bound htrace,
    ordinaryTraceAlong_targetHermitianResponse_eq_completePhysicalBoundaryPairing_re
      owner lambda (canonicalFamily owner) a c hac hsupp negativeBasis
      positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis sourceBasis hfactor]

end CCM24FiniteSGatePhysicalHardyProlateCompletedHermitianTrace
end CCM25Concrete
end Source
end ConnesWeilRH
