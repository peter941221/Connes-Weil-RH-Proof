/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCausalMarkovRawCumulativeLedger

/-!
# Raw completed-trace readout of the canonical Gate 3U contract

Proof 798 expresses a raw completed physical trace as a signed cumulative
forcing ledger.  This module identifies that same raw scalar with the
canonical real Gate 3U readout.  Thus a source-specific estimate of the
signed raw forcing, if obtained, feeds the actual Gate without a lower-factor
normalization or division.

This is a readout identity only.  It supplies neither a bound for the raw
trace nor a construction of a compatible family chain for the canonical
finite prime-power family.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCausalMarkovRawGateReadout

open MeasureTheory
open scoped BigOperators InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSActualBandSourceRemainder
open CCM24FiniteSBandTrace
open CCM24FiniteSCanonicalCompletedResponse
open CCM24FiniteSCanonicalRealGate
open CCM24FiniteSCausalMarkovCompletedPhysicalDifference
open CCM24FiniteSCausalMarkovRawBase
open CCM24FiniteSCausalMarkovRawCumulativeLedger
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSGramResponse
open CCM24FiniteSProjectionTrace
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The canonical real Gate is exactly the absolute raw completed physical
trace.  In particular, the unscaled cumulative forcing ledger from Proof 798
has the right scalar orientation for Gate 3U. -/
theorem canonicalRealGate3UAt_iff_abs_rawCompletePhysicalHermitianTrace_le
    {rho iota kappa tau iotaR kappaR tauR nu mu : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a <= c)
    (hsupp : Function.support owner.sourceTest.test <= Set.Icc a c)
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
    (bound : ℝ) :
    canonicalRealGate3UAt owner lambda sourceBasis bound ↔
      |rawCompletePhysicalHermitianTrace owner lambda (canonicalFamily owner)
        a c hac hsupp reflectedNegativeBasis reflectedPositiveBasis
        reflectedOutputBasis globalBasis sourceBasis hfactor| <= bound := by
  rw [canonicalRealGate3UAt_iff_sourceBandRealBound]
  have hreadback :=
    completePhysicalHermitianTrace_eq_neg_sourceBandGramRealTrace owner lambda
      (canonicalFamily owner) a c hac hsupp negativeBasis positiveBasis
      outputBasis reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis boundaryBasis sourceBasis hfactor
  have hreadbackRe := congrArg Complex.re hreadback
  simp only [Complex.neg_re, Complex.ofReal_re] at hreadbackRe
  unfold rawCompletePhysicalHermitianTrace
  rw [hreadbackRe, abs_neg]

/-- Any raw completed physical support bound closes the canonical real Gate
with no lower-factor conversion. -/
theorem canonicalRealGate3UAt_of_abs_rawCompletePhysicalHermitianTrace_le
    {rho iota kappa tau iotaR kappaR tauR nu mu : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a <= c)
    (hsupp : Function.support owner.sourceTest.test <= Set.Icc a c)
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
    (bound : ℝ)
    (hbound :
      |rawCompletePhysicalHermitianTrace owner lambda (canonicalFamily owner)
        a c hac hsupp reflectedNegativeBasis reflectedPositiveBasis
        reflectedOutputBasis globalBasis sourceBasis hfactor| <= bound) :
    canonicalRealGate3UAt owner lambda sourceBasis bound :=
  (canonicalRealGate3UAt_iff_abs_rawCompletePhysicalHermitianTrace_le owner
    lambda a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor bound).mpr hbound

end CCM24FiniteSCausalMarkovRawGateReadout
end CCM25Concrete
end Source
end ConnesWeilRH
