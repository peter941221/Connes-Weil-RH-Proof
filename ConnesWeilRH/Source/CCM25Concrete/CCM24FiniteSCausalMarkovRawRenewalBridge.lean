/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCausalMarkovRawGateReadout
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSOrderedCausalGram

/-!
# Raw forcing as a complete physical renewal trace

The raw finite-S forcing is the signed difference of two completed physical
renewal responses after each family has retained its own inverse lower-factor
square.  This module makes that owner explicit and proves its trace-legal
readback.  It deliberately keeps the two endpoint renewal responses coupled
inside one signed operator before taking a real part or an absolute value.

No support-polynomial estimate is supplied here.  In particular, the result
does not divide the scaled forcing estimate by a lower factor and does not
bound the Markov coboundary and completed remainder separately.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCausalMarkovRawRenewalBridge

open MeasureTheory
open scoped BigOperators InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSActualBandSourceRemainder
open CCM24FiniteSBandTrace
open CCM24FiniteSCanonicalCompletedResponse
open CCM24FiniteSCanonicalRealGate
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSCausalMarkovCompletedPhysicalDifference
open CCM24FiniteSCausalMarkovRawBase
open CCM24FiniteSCausalMarkovRawGateReadout
open CCM24FiniteSGramResponse
open CCM24FiniteSForwardRenewal
open CCM24FiniteSMultiRenewal
open CCM24FiniteSOrderedCausalGram
open CCM24FiniteSPhysicalRenewalExpansion
open CCM24FiniteSProjectionTrace
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The full physical renewal response with the family-specific inverse
Euler lower-factor square retained outside the already assembled renewal sum.
This is an operator on the actual source Sonin carrier. -/
noncomputable def inverseLowerFactorPhysicalRenewalResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[Complex] sourceSoninCarrier lambda :=
  ((finiteEulerLowerFactor family.visiblePrimes : Complex) ^ 2)⁻¹ •
    (∑ forwardIndex : FiniteEulerForwardIndex family.visiblePrimes,
      ∑' renewalIndex : FiniteEulerRenewalIndex family.visiblePrimes,
        finiteEulerPhysicalResponseAtom owner lambda family forwardIndex
          renewalIndex)

/-- The renewal owner is exactly the raw source-band endpoint.  This is an
operator identity, so it introduces no trace interchange or norm estimate. -/
theorem inverseLowerFactorPhysicalRenewalResponse_eq_sourceBandGramResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    inverseLowerFactorPhysicalRenewalResponse owner lambda family =
      sourceBandGramResponse owner lambda family := by
  exact (sourceBandGramResponse_eq_inv_lowerFactor_sq_smul_renewalExpansion
    owner lambda family).symm

/-- The inverse-lower-factor renewal response inherits the existing
Hardy--prolate trace-legality witness for the raw source endpoint. -/
theorem inverseLowerFactorPhysicalRenewalResponse_isTraceClassAlong
    {rho iota kappa tau iotaR kappaR tauR nu mu : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : Real) (hac : a <= c)
    (hsupp : Function.support owner.sourceTest.test <= Set.Icc a c)
    (negativeBasis : HilbertBasis iota Complex
      (Lp Complex 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis kappa Complex
      (Lp Complex 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau Complex
      (Lp Complex 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis iotaR Complex
      (Lp Complex 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR Complex
      (Lp Complex 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR Complex
      (Lp Complex 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu Complex finiteSCarrier)
    (boundaryBasis : HilbertBasis mu Complex (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho Complex (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      norm (sourceProlateHilbertSchmidtFactor lambda (globalBasis i)) ^ 2) :
    IsTraceClassAlong sourceBasis
      (inverseLowerFactorPhysicalRenewalResponse owner lambda family) := by
  rw [inverseLowerFactorPhysicalRenewalResponse_eq_sourceBandGramResponse]
  exact sourceBandGramResponse_isTraceClassAlong owner lambda family
    a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor

/-- The real ordinary trace of one complete inverse-lower-factor renewal
response.  Its trace legality is supplied by the theorem above when a
Hardy--prolate pair-data witness is available. -/
noncomputable def inverseLowerFactorPhysicalRenewalTrace
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis rho Complex (sourceSoninCarrier lambda)) : Real :=
  (ordinaryTraceAlong sourceBasis
    (inverseLowerFactorPhysicalRenewalResponse owner lambda family)).re

/-- The signed operator whose ordinary real trace is the literal raw
one-prime forcing.  The old and new physical renewal responses stay together
inside this one subtraction. -/
noncomputable def rawPhysicalRenewalForcingResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (newFamily oldFamily : FinitePrimePowerFamily) :
    sourceSoninCarrier lambda →L[Complex] sourceSoninCarrier lambda :=
  inverseLowerFactorPhysicalRenewalResponse owner lambda oldFamily -
    inverseLowerFactorPhysicalRenewalResponse owner lambda newFamily

/-- The signed raw-renewal forcing response is trace class on the same source
basis as its two completed endpoint owners. -/
theorem rawPhysicalRenewalForcingResponse_isTraceClassAlong
    {rho iota kappa tau iotaR kappaR tauR nu mu : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (newFamily oldFamily : FinitePrimePowerFamily)
    (a c : Real) (hac : a <= c)
    (hsupp : Function.support owner.sourceTest.test <= Set.Icc a c)
    (negativeBasis : HilbertBasis iota Complex
      (Lp Complex 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis kappa Complex
      (Lp Complex 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau Complex
      (Lp Complex 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis iotaR Complex
      (Lp Complex 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR Complex
      (Lp Complex 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR Complex
      (Lp Complex 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu Complex finiteSCarrier)
    (boundaryBasis : HilbertBasis mu Complex (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho Complex (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      norm (sourceProlateHilbertSchmidtFactor lambda (globalBasis i)) ^ 2) :
    IsTraceClassAlong sourceBasis
      (rawPhysicalRenewalForcingResponse owner lambda newFamily oldFamily) := by
  unfold rawPhysicalRenewalForcingResponse
  exact isTraceClassAlong_sub sourceBasis _ _
    (inverseLowerFactorPhysicalRenewalResponse_isTraceClassAlong owner lambda
      oldFamily a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor)
    (inverseLowerFactorPhysicalRenewalResponse_isTraceClassAlong owner lambda
      newFamily a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor)

/-- The signed renewal forcing trace is the old endpoint trace minus the new
endpoint trace, before its real part is used by the Gate ledger. -/
theorem ordinaryTraceAlong_rawPhysicalRenewalForcingResponse_eq
    {rho iota kappa tau iotaR kappaR tauR nu mu : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (newFamily oldFamily : FinitePrimePowerFamily)
    (a c : Real) (hac : a <= c)
    (hsupp : Function.support owner.sourceTest.test <= Set.Icc a c)
    (negativeBasis : HilbertBasis iota Complex
      (Lp Complex 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis kappa Complex
      (Lp Complex 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau Complex
      (Lp Complex 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis iotaR Complex
      (Lp Complex 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR Complex
      (Lp Complex 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR Complex
      (Lp Complex 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu Complex finiteSCarrier)
    (boundaryBasis : HilbertBasis mu Complex (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho Complex (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      norm (sourceProlateHilbertSchmidtFactor lambda (globalBasis i)) ^ 2) :
    ordinaryTraceAlong sourceBasis
        (rawPhysicalRenewalForcingResponse owner lambda newFamily oldFamily) =
      ordinaryTraceAlong sourceBasis
          (inverseLowerFactorPhysicalRenewalResponse owner lambda oldFamily) -
        ordinaryTraceAlong sourceBasis
          (inverseLowerFactorPhysicalRenewalResponse owner lambda newFamily) := by
  unfold rawPhysicalRenewalForcingResponse
  exact ordinaryTraceAlong_sub sourceBasis _ _
    (inverseLowerFactorPhysicalRenewalResponse_isTraceClassAlong owner lambda
      oldFamily a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor)
    (inverseLowerFactorPhysicalRenewalResponse_isTraceClassAlong owner lambda
      newFamily a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor)

/-- The raw completed physical endpoint is the negative real trace of its
complete inverse-lower-factor renewal response. -/
theorem rawCompletePhysicalHermitianTrace_eq_neg_inverseLowerFactorPhysicalRenewalTrace
    {rho iota kappa tau iotaR kappaR tauR nu mu : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : Real) (hac : a <= c)
    (hsupp : Function.support owner.sourceTest.test <= Set.Icc a c)
    (negativeBasis : HilbertBasis iota Complex
      (Lp Complex 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis kappa Complex
      (Lp Complex 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau Complex
      (Lp Complex 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis iotaR Complex
      (Lp Complex 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR Complex
      (Lp Complex 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR Complex
      (Lp Complex 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu Complex finiteSCarrier)
    (boundaryBasis : HilbertBasis mu Complex (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho Complex (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      norm (sourceProlateHilbertSchmidtFactor lambda (globalBasis i)) ^ 2) :
    rawCompletePhysicalHermitianTrace owner lambda family a c hac hsupp
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis sourceBasis hfactor =
      -inverseLowerFactorPhysicalRenewalTrace owner lambda family sourceBasis := by
  unfold rawCompletePhysicalHermitianTrace inverseLowerFactorPhysicalRenewalTrace
  rw [inverseLowerFactorPhysicalRenewalResponse_eq_sourceBandGramResponse]
  have hphysical := completePhysicalHermitianTrace_eq_neg_sourceBandGramRealTrace
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor
  have hphysicalRe := congrArg Complex.re hphysical
  simpa only [Complex.neg_re, Complex.ofReal_re] using hphysicalRe

set_option maxHeartbeats 2000000 in
-- The endpoint ledger and trace subtraction are kept intact until the final
-- scalar elimination, so no physical branch is estimated separately.
/-- The literal raw Markov/remainder forcing is the real ordinary trace of
one signed difference of complete inverse-lower-factor physical renewal
responses.  This identifies the remaining same-object support-polynomial
object; it does not supply its estimate. -/
theorem rawCompletePhysicalForcing_eq_rawPhysicalRenewalForcingTrace_re
    {rho iota kappa tau iotaR kappaR tauR nu mu sigma : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (newFamily oldFamily : FinitePrimePowerFamily)
    (hnew : newFamily.visiblePrimes = p :: S)
    (hold : oldFamily.visiblePrimes = S)
    (a c : Real) (hac : a <= c)
    (hsupp : Function.support owner.sourceTest.test <= Set.Icc a c)
    (negativeBasis : HilbertBasis iota Complex
      (Lp Complex 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis kappa Complex
      (Lp Complex 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau Complex
      (Lp Complex 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis iotaR Complex
      (Lp Complex 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis kappaR Complex
      (Lp Complex 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis tauR Complex
      (Lp Complex 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu Complex finiteSCarrier)
    (boundaryBasis : HilbertBasis mu Complex (commonBoundaryCarrier a c))
    (pairedBoundaryBasis : HilbertBasis sigma Complex (actualBandPairCarrier a c))
    (sourceBasis : HilbertBasis rho Complex (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      norm (sourceProlateHilbertSchmidtFactor lambda (globalBasis i)) ^ 2) :
    rawCompletePhysicalForcing owner lambda p S newFamily oldFamily sourceBasis =
      (ordinaryTraceAlong sourceBasis
        (rawPhysicalRenewalForcingResponse owner lambda newFamily oldFamily)).re := by
  have hledger := rawCompletePhysicalHermitianTrace_cons_eq_add_forcing
    owner lambda p S newFamily oldFamily hnew hold a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      pairedBoundaryBasis sourceBasis hfactor
  have hnewTrace :=
    rawCompletePhysicalHermitianTrace_eq_neg_inverseLowerFactorPhysicalRenewalTrace
      owner lambda newFamily a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis boundaryBasis sourceBasis hfactor
  have holdTrace :=
    rawCompletePhysicalHermitianTrace_eq_neg_inverseLowerFactorPhysicalRenewalTrace
      owner lambda oldFamily a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis boundaryBasis sourceBasis hfactor
  have hrenewal := ordinaryTraceAlong_rawPhysicalRenewalForcingResponse_eq
    owner lambda newFamily oldFamily a c hac hsupp negativeBasis positiveBasis
      outputBasis reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor
  rw [hnewTrace, holdTrace] at hledger
  rw [hrenewal]
  simp only [Complex.sub_re]
  unfold inverseLowerFactorPhysicalRenewalTrace at hledger
  linarith

/-- The canonical real Gate is exactly the compact-support-first bound for
the complete inverse-lower-factor physical renewal trace of the canonical
family.  This identifies the remaining producer without asserting it. -/
theorem canonicalRealGate3UAt_iff_abs_inverseLowerFactorPhysicalRenewalTrace_le
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (sourceBasis : HilbertBasis rho Complex (sourceSoninCarrier lambda))
    (bound : Real) :
    canonicalRealGate3UAt owner lambda sourceBasis bound <->
      abs (inverseLowerFactorPhysicalRenewalTrace owner lambda
        (canonicalFamily owner) sourceBasis) <= bound := by
  change canonicalRealGate3UAt owner lambda sourceBasis bound <->
    abs ((ordinaryTraceAlong sourceBasis
      (inverseLowerFactorPhysicalRenewalResponse owner lambda
        (canonicalFamily owner))).re) <= bound
  rw [canonicalRealGate3UAt_iff_sourceBandRealBound,
    <- inverseLowerFactorPhysicalRenewalResponse_eq_sourceBandGramResponse]

end CCM24FiniteSCausalMarkovRawRenewalBridge
end CCM25Concrete
end Source
end ConnesWeilRH
