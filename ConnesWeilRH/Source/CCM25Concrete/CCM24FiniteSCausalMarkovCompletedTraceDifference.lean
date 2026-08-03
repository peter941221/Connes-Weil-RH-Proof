/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCausalMarkovCompletedFirstDifference

/-!
# Trace-legal completed one-prime ledger

The completed first-difference identity lives on the actual source Sonin
carrier. This module proves that its three terms remain trace legal along one
fixed source basis under the existing physical pair-data hypotheses. The
ordinary trace of the endpoint increment is therefore exactly the Markov
coboundary trace minus the completed-remainder trace.

This is a legality and identity result only. It does not bound either trace,
separate physical branches, or prove the lower-factor-square estimate required
by Gate 3U.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCausalMarkovCompletedTraceDifference

open scoped InnerProduct InnerProductSpace

open MeasureTheory
open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSBandTrace
open CCM24FiniteSActualBandSourceRemainder
open CCM24FiniteSCausalMarkovCompletedFirstDifference
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The completed endpoint increment is trace class whenever the two actual
source first jets and the two actual completed remainders are trace class on
one basis. This creates no independent trace cycle. -/
theorem sourceBandGramIncrement_isTraceClassAlong_of_actualBandTraceClass
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (newFamily oldFamily : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hnew : newFamily.visiblePrimes = p :: S)
    (hold : oldFamily.visiblePrimes = S)
    (hfirstNew : IsTraceClassAlong sourceBasis
      (sourceActualBandFiniteEulerSoninResponse owner lambda newFamily))
    (hfirstOld : IsTraceClassAlong sourceBasis
      (sourceActualBandFiniteEulerSoninResponse owner lambda oldFamily))
    (hremainderNew : IsTraceClassAlong sourceBasis
      (sourceActualBandFiniteEulerRemainderResponse owner lambda newFamily))
    (hremainderOld : IsTraceClassAlong sourceBasis
      (sourceActualBandFiniteEulerRemainderResponse owner lambda oldFamily)) :
    IsTraceClassAlong sourceBasis
      (sourceBandGramIncrement owner lambda newFamily oldFamily) := by
  have hcoboundary : IsTraceClassAlong sourceBasis
      (normalizedListActualBandSoninCoboundary owner lambda p S) := by
    rw [← sourceActualBandFiniteEulerSoninResponse_sub_eq_coboundary_of_visiblePrimeLists
      owner lambda p S newFamily oldFamily hnew hold]
    exact isTraceClassAlong_sub sourceBasis _ _ hfirstNew hfirstOld
  have hremainders : IsTraceClassAlong sourceBasis
      (sourceActualBandFiniteEulerRemainderIncrement owner lambda newFamily oldFamily) := by
    unfold sourceActualBandFiniteEulerRemainderIncrement
    exact isTraceClassAlong_sub sourceBasis _ _ hremainderNew hremainderOld
  rw [sourceBandGramIncrement_eq_coboundary_sub_remainder owner lambda p S
    newFamily oldFamily hnew hold]
  exact isTraceClassAlong_sub sourceBasis _ _ hcoboundary hremainders

/-- The trace-level completed ledger. The Markov coboundary and completed
remainder remain coupled by subtraction before any scalar bound is attempted. -/
theorem
    ordinaryTraceAlong_sourceBandGramIncrement_eq_coboundary_sub_remainder_of_actualBandTraceClass
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (newFamily oldFamily : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hnew : newFamily.visiblePrimes = p :: S)
    (hold : oldFamily.visiblePrimes = S)
    (hfirstNew : IsTraceClassAlong sourceBasis
      (sourceActualBandFiniteEulerSoninResponse owner lambda newFamily))
    (hfirstOld : IsTraceClassAlong sourceBasis
      (sourceActualBandFiniteEulerSoninResponse owner lambda oldFamily))
    (hremainderNew : IsTraceClassAlong sourceBasis
      (sourceActualBandFiniteEulerRemainderResponse owner lambda newFamily))
    (hremainderOld : IsTraceClassAlong sourceBasis
      (sourceActualBandFiniteEulerRemainderResponse owner lambda oldFamily)) :
    ordinaryTraceAlong sourceBasis
        (sourceBandGramIncrement owner lambda newFamily oldFamily) =
      ordinaryTraceAlong sourceBasis
          (normalizedListActualBandSoninCoboundary owner lambda p S) -
        ordinaryTraceAlong sourceBasis
          (sourceActualBandFiniteEulerRemainderIncrement owner lambda
            newFamily oldFamily) := by
  have hcoboundary : IsTraceClassAlong sourceBasis
      (normalizedListActualBandSoninCoboundary owner lambda p S) := by
    rw [← sourceActualBandFiniteEulerSoninResponse_sub_eq_coboundary_of_visiblePrimeLists
      owner lambda p S newFamily oldFamily hnew hold]
    exact isTraceClassAlong_sub sourceBasis _ _ hfirstNew hfirstOld
  have hremainders : IsTraceClassAlong sourceBasis
    (sourceActualBandFiniteEulerRemainderIncrement owner lambda newFamily
      oldFamily) := by
    unfold sourceActualBandFiniteEulerRemainderIncrement
    exact isTraceClassAlong_sub sourceBasis _ _ hremainderNew hremainderOld
  rw [sourceBandGramIncrement_eq_coboundary_sub_remainder owner lambda p S
    newFamily oldFamily hnew hold]
  exact ordinaryTraceAlong_sub sourceBasis _ _ hcoboundary hremainders

set_option maxHeartbeats 800000 in
-- The physical specialization unfolds four-coordinate pair carriers.
/-- The actual Hardy--prolate pair-data hypotheses discharge the trace-class
conditions in the completed one-prime ledger. -/
theorem sourceBandGramIncrement_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (newFamily oldFamily : FinitePrimePowerFamily)
    (hnew : newFamily.visiblePrimes = p :: S)
    (hold : oldFamily.visiblePrimes = S)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ tau ιr κr taur nu mu sigma rho : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis taur ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (pairedBoundaryBasis : HilbertBasis sigma ℂ (actualBandPairCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    IsTraceClassAlong sourceBasis
      (sourceBandGramIncrement owner lambda newFamily oldFamily) := by
  exact sourceBandGramIncrement_isTraceClassAlong_of_actualBandTraceClass
    owner lambda p S newFamily oldFamily sourceBasis hnew hold
    (sourceActualBandFiniteEulerSoninResponse_isTraceClassAlong owner lambda
      newFamily a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor)
    (sourceActualBandFiniteEulerSoninResponse_isTraceClassAlong owner lambda
      oldFamily a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor)
    (sourceActualBandFiniteEulerRemainderResponse_isTraceClassAlong owner lambda
      newFamily a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor)
    (sourceActualBandFiniteEulerRemainderResponse_isTraceClassAlong owner lambda
      oldFamily a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor)

set_option maxHeartbeats 800000 in
-- The physical trace identity elaborates the same four-coordinate pair data.
/-- The actual physical pair data gives the legal scalar version of the
completed one-prime ledger on one fixed source basis. -/
theorem ordinaryTraceAlong_sourceBandGramIncrement_eq_coboundary_sub_remainder
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (newFamily oldFamily : FinitePrimePowerFamily)
    (hnew : newFamily.visiblePrimes = p :: S)
    (hold : oldFamily.visiblePrimes = S)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ tau ιr κr taur nu mu sigma rho : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis tau ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis taur ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (pairedBoundaryBasis : HilbertBasis sigma ℂ (actualBandPairCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    ordinaryTraceAlong sourceBasis
        (sourceBandGramIncrement owner lambda newFamily oldFamily) =
      ordinaryTraceAlong sourceBasis
          (normalizedListActualBandSoninCoboundary owner lambda p S) -
        ordinaryTraceAlong sourceBasis
          (sourceActualBandFiniteEulerRemainderIncrement owner lambda
            newFamily oldFamily) := by
  exact
    ordinaryTraceAlong_sourceBandGramIncrement_eq_coboundary_sub_remainder_of_actualBandTraceClass
    owner lambda p S newFamily oldFamily sourceBasis hnew hold
    (sourceActualBandFiniteEulerSoninResponse_isTraceClassAlong owner lambda
      newFamily a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor)
    (sourceActualBandFiniteEulerSoninResponse_isTraceClassAlong owner lambda
      oldFamily a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor)
    (sourceActualBandFiniteEulerRemainderResponse_isTraceClassAlong owner lambda
      newFamily a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor)
    (sourceActualBandFiniteEulerRemainderResponse_isTraceClassAlong owner lambda
      oldFamily a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor)

end CCM24FiniteSCausalMarkovCompletedTraceDifference
end CCM25Concrete
end Source
end ConnesWeilRH
