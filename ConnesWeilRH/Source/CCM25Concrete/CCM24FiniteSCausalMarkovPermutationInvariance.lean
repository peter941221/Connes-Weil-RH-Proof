/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCausalMarkovRawBase

/-!
# Permutation invariance for the raw finite-S endpoint

`FinitePrimePowerFamily.visiblePrimes` is obtained from `Finset.toList`, whose
order is a choice of list representative.  A term-level deletion therefore
need not expose the literal tail of that list.  This module proves that the
actual raw endpoint is insensitive to this representation choice: it depends
on the visible places only up to permutation.

This does not construct a suffix family or a cumulative forcing estimate.  It
is the order-invariance prerequisite for a future term-deletion chain.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCausalMarkovPermutationInvariance

open MeasureTheory
open scoped BigOperators InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSActualBandSourceRemainder
open CCM24FiniteSBandTrace
open CCM24FiniteSCausalMarkov
open CCM24FiniteSCausalMarkovTwoSidedFirstDifference
open CCM24FiniteSCausalMarkovCompletedFirstDifference
open CCM24FiniteSCausalMarkovCompletedPhysicalDifference
open CCM24FiniteSCausalMarkovRawBase
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSGramResponse
open CCM24FiniteSProjectionTrace
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The scalar lower factor is insensitive to the order chosen for the
visible-prime list. -/
theorem finiteEulerLowerFactor_eq_of_perm
    {S T : List CCM24VisiblePrime} (hperm : S.Perm T) :
    finiteEulerLowerFactor S = finiteEulerLowerFactor T := by
  unfold finiteEulerLowerFactor
  exact (hperm.map fun p => 1 - ccm24PrimeEulerCoefficient p).prod_eq

/-- The normalized finite Euler inverse is a function of the finite place
set, rather than of the chosen list representative. -/
theorem normalizedFiniteEulerInverseList_eq_of_perm
    {S T : List CCM24VisiblePrime} (hperm : S.Perm T) :
    normalizedFiniteEulerInverseList S = normalizedFiniteEulerInverseList T := by
  unfold normalizedFiniteEulerInverseList
  rw [finiteEulerLowerFactor_eq_of_perm hperm,
    ccm24FiniteEulerTransportEquiv_eq_of_perm hperm]

/-- The literal-list actual-band paired response has the same order
invariance as its normalized Euler inverse. -/
theorem normalizedListActualBandPairedResponse_eq_of_perm
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {S T : List CCM24VisiblePrime}
    (hperm : S.Perm T) :
    normalizedListActualBandPairedResponse owner lambda S =
      normalizedListActualBandPairedResponse owner lambda T := by
  unfold normalizedListActualBandPairedResponse
  rw [normalizedFiniteEulerInverseList_eq_of_perm hperm]

/-- Pulling the literal-list paired response back to the source Sonin carrier
preserves its permutation invariance. -/
theorem normalizedListActualBandSoninResponse_eq_of_perm
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) {S T : List CCM24VisiblePrime}
    (hperm : S.Perm T) :
    normalizedListActualBandSoninResponse owner lambda S =
      normalizedListActualBandSoninResponse owner lambda T := by
  unfold normalizedListActualBandSoninResponse
  rw [normalizedListActualBandPairedResponse_eq_of_perm owner lambda hperm]

/-- The actual source first jet has the one-prime coboundary whenever the new
family exposes `p :: S` and the old family's list is merely a permutation of
`S`.  This is the usable form for term-deletion towers. -/
theorem sourceActualBandFiniteEulerSoninResponse_sub_eq_coboundary_of_visiblePrimeList_perm
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (newFamily oldFamily : FinitePrimePowerFamily)
    (hnew : newFamily.visiblePrimes = p :: S)
    (hold : oldFamily.visiblePrimes.Perm S) :
    sourceActualBandFiniteEulerSoninResponse owner lambda newFamily -
        sourceActualBandFiniteEulerSoninResponse owner lambda oldFamily =
      normalizedListActualBandSoninCoboundary owner lambda p S := by
  rw [sourceActualBandFiniteEulerSoninResponse_eq_normalizedList,
    sourceActualBandFiniteEulerSoninResponse_eq_normalizedList, hnew,
    normalizedListActualBandSoninResponse_eq_of_perm owner lambda hold]
  exact normalizedListActualBandSoninResponse_cons_sub_eq_coboundary
    owner lambda p S

/-- The same one-prime source ledger only depends on the new and old visible
places up to permutation.  This is the form consumed by recursive deletion
of all prime-power terms at one visible prime. -/
theorem sourceActualBandFiniteEulerSoninResponse_sub_eq_coboundary_of_visiblePrimeLists_perm
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (newFamily oldFamily : FinitePrimePowerFamily)
    (hnew : newFamily.visiblePrimes.Perm (p :: S))
    (hold : oldFamily.visiblePrimes.Perm S) :
    sourceActualBandFiniteEulerSoninResponse owner lambda newFamily -
        sourceActualBandFiniteEulerSoninResponse owner lambda oldFamily =
      normalizedListActualBandSoninCoboundary owner lambda p S := by
  rw [sourceActualBandFiniteEulerSoninResponse_eq_normalizedList,
    sourceActualBandFiniteEulerSoninResponse_eq_normalizedList,
    normalizedListActualBandSoninResponse_eq_of_perm owner lambda hnew,
    normalizedListActualBandSoninResponse_eq_of_perm owner lambda hold]
  exact normalizedListActualBandSoninResponse_cons_sub_eq_coboundary
    owner lambda p S

/-- The finite Euler frame depends on the visible finite places only up to
permutation. -/
theorem finiteEulerFrame_eq_of_visiblePrimes_perm
    (lambda : CCM24SoninScale) (first second : FinitePrimePowerFamily)
    (hperm : first.visiblePrimes.Perm second.visiblePrimes) :
    finiteEulerFrame lambda first = finiteEulerFrame lambda second := by
  rw [finiteEulerFrame_eq_transport_comp_inclusion,
    finiteEulerFrame_eq_transport_comp_inclusion,
    ccm24FiniteEulerTransportEquiv_eq_of_perm hperm]

/-- The inverse source Gram covariance has the same permutation invariance. -/
theorem finiteEulerGramInv_eq_of_visiblePrimes_perm
    (lambda : CCM24SoninScale) (first second : FinitePrimePowerFamily)
    (hperm : first.visiblePrimes.Perm second.visiblePrimes) :
    finiteEulerGramInv lambda first = finiteEulerGramInv lambda second := by
  simp only [finiteEulerGramInv]
  rw [ccm24FiniteEulerTransportEquiv_eq_of_perm hperm]

/-- The actual source Gram response is independent of the chosen `Finset`
list representative. -/
theorem sourceBandGramResponse_eq_of_visiblePrimes_perm
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (first second : FinitePrimePowerFamily)
    (hperm : first.visiblePrimes.Perm second.visiblePrimes) :
    sourceBandGramResponse owner lambda first =
      sourceBandGramResponse owner lambda second := by
  unfold sourceBandGramResponse sourceGramResponse
  rw [finiteEulerFrame_eq_of_visiblePrimes_perm lambda first second hperm,
    finiteEulerGramInv_eq_of_visiblePrimes_perm lambda first second hperm]

/-- The literal raw completed physical trace depends only on the visible
finite places up to permutation. This is an equality of the Gate-facing raw
scalar, not a bound. -/
theorem rawCompletePhysicalHermitianTrace_eq_of_visiblePrimes_perm
    {rho iota kappa tau iotaR kappaR tauR nu mu : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (first second : FinitePrimePowerFamily)
    (hperm : first.visiblePrimes.Perm second.visiblePrimes)
    (a c : ℝ) (hac : a <= c)
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
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    rawCompletePhysicalHermitianTrace owner lambda first a c hac hsupp
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis sourceBasis hfactor =
      rawCompletePhysicalHermitianTrace owner lambda second a c hac hsupp
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis sourceBasis hfactor := by
  have hresponse : sourceBandGramResponse owner lambda first =
      sourceBandGramResponse owner lambda second :=
    sourceBandGramResponse_eq_of_visiblePrimes_perm owner lambda first second
      hperm
  unfold rawCompletePhysicalHermitianTrace
  rw [completePhysicalHermitianTrace_eq_neg_sourceBandGramRealTrace owner lambda
      first a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor,
    completePhysicalHermitianTrace_eq_neg_sourceBandGramRealTrace owner lambda
      second a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor,
    hresponse]

end CCM24FiniteSCausalMarkovPermutationInvariance
end CCM25Concrete
end Source
end ConnesWeilRH
