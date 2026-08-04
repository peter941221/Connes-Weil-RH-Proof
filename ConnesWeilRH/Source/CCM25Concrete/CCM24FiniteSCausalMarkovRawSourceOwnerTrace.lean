/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCausalMarkovRawGateReadout

/-!
# Raw Gate 3U trace collapses exactly onto the Q_S source owner

Proof 264 `(AA.1)` fixes the finite-S real bilinear form `Q_S(eta,xi)`, and
`(AA.32)` is its bound.  This module records that the gate's analytic target
is *exactly* the ordinary trace of the existing `sourceGramResponse` operator
on the canonical finite prime-power family.  Thus no new owner is needed: the
missing analytic bound is a compact-root support estimate for that already
declared operator, after the raw trace is read back onto a Hilbert basis of
the source Sonin carrier.

This is a statement-planting contract.  It fixes the precise scalar/operator
whose bound closes the raw readout; it does not by itself provide that bound.
A valid producer closes the canonical real Gate by bounding
`abs (ordinaryTraceAlong sourceBasis (sourceGramResponse owner lambda
(canonicalFamily owner))).re` uniformly in the finite family, with compact
root support applied before any absolute value.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCausalMarkovRawSourceOwnerTrace

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
open CCM24FiniteSCausalMarkovRawGateReadout
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSGramResponse
open CCM24FiniteSProjectionTrace
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The Q_S source owner is the negation of the source-band response.  The
sign is recorded once so the Gate readback reads the already-declared owner
without inventing a new operator. -/
theorem ordinaryTraceAlong_sourceGramResponse_eq_neg_sourceBand
    {rho : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda)) :
    ordinaryTraceAlong sourceBasis
        (sourceGramResponse owner lambda family) =
      -ordinaryTraceAlong sourceBasis
        (sourceBandGramResponse owner lambda family) := by
  rw [sourceBandGramResponse]
  rw [CCM24FiniteSProjectionTrace.PositiveTrace.ordinaryTraceAlong_neg]
  simp

/-- The raw Gate scalar on a finite family is exactly the real ordinary trace
of the Q_S source owner.  This is `(AA.32)`'s analytic object. -/
theorem rawCompletePhysicalHermitianTrace_eq_realOrdinaryTrace_sourceGramResponse
    {rho iota kappa tau iotaR kappaR taur nu mu : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a <= c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
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
    (reflectedOutputBasis : HilbertBasis taur ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    rawCompletePhysicalHermitianTrace owner lambda family a c hac hsupp
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis sourceBasis hfactor =
      (ordinaryTraceAlong sourceBasis
        (sourceGramResponse owner lambda family)).re := by
  unfold rawCompletePhysicalHermitianTrace
  rw [completePhysicalHermitianTrace_eq_neg_sourceBandGramRealTrace owner lambda
    family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor]
  rw [sourceBandGramResponse]
  rw [CCM24FiniteSProjectionTrace.PositiveTrace.ordinaryTraceAlong_neg]
  simp only [Complex.neg_re, Complex.ofReal_re, Complex.ofReal_neg, neg_neg]

/-- Closing the real ordinary trace of the Q_S source owner on the canonical
family closes the canonical real Gate 3U.  This is the `(AA.32)` handoff. -/
theorem canonicalRealGate3UAt_iff_abs_realOrdinaryTrace_sourceGramResponse_le
    {rho iota kappa tau iotaR kappaR taur nu mu : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a <= c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
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
    (reflectedOutputBasis : HilbertBasis taur ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (bound : ℝ) :
    canonicalRealGate3UAt owner lambda sourceBasis bound ↔
      |(ordinaryTraceAlong sourceBasis
        (sourceGramResponse owner lambda (canonicalFamily owner))).re| ≤
          bound := by
  rw [canonicalRealGate3UAt_iff_abs_rawCompletePhysicalHermitianTrace_le owner
    lambda a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor bound]
  rw [rawCompletePhysicalHermitianTrace_eq_realOrdinaryTrace_sourceGramResponse
    owner lambda (canonicalFamily owner) a c hac hsupp negativeBasis positiveBasis
    outputBasis reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor]

/-- A producer who supplies a compact-support bound for the real ordinary trace
of the Q_S source owner may close the canonical real Gate directly.  This is
the `(AA.32)` consumer: it applies a support estimate to the already declared
owner, with no lower-factor normalization. -/
theorem canonicalRealGate3UAt_of_abs_realOrdinaryTrace_sourceGramResponse_le
    {rho iota kappa tau iotaR kappaR taur nu mu : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a <= c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
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
    (reflectedOutputBasis : HilbertBasis taur ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (bound : ℝ)
    (hbound :
      |(ordinaryTraceAlong sourceBasis
        (sourceGramResponse owner lambda (canonicalFamily owner))).re| ≤
          bound) :
    canonicalRealGate3UAt owner lambda sourceBasis bound :=
  (canonicalRealGate3UAt_iff_abs_realOrdinaryTrace_sourceGramResponse_le owner
    lambda a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor bound).mpr hbound

end CCM24FiniteSCausalMarkovRawSourceOwnerTrace
end CCM25Concrete
end Source
end ConnesWeilRH