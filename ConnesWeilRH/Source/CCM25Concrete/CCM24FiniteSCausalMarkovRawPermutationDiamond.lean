/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCausalMarkovRawPermutationOrderInvariance

/-!
# Local diamond identity for raw finite-S forcing

Deleting two distinct visible-prime blocks in opposite orders changes the
intermediate finite families and the individual raw forcings.  This module
proves that the two-step signed sums agree exactly.  It is the local
curl-free form of the raw endpoint potential.

The result keeps the Markov coboundary and completed remainder coupled in
every forcing term.  It supplies no absolute-value estimate and does not
prove Gate 3U.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCausalMarkovRawPermutationDiamond

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
open CCM24FiniteSCausalMarkovPermutationInvariance
open CCM24FiniteSCausalMarkovPermutationLedger
open CCM24FiniteSCausalMarkovRawBase
open CCM24FiniteSCausalMarkovRawPermutationOrderInvariance
open CCM24FiniteSGramResponse
open CCM24FiniteSProjectionTrace
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

set_option maxHeartbeats 2000000 in
-- Four completed physical endpoint readbacks must be elaborated before the
-- final scalar elimination.
/-- The raw completed forcing is a discrete potential on prime-block
deletions.  The two paths around a two-prime deletion square have the same
signed total without comparing either forcing term by absolute value. -/
theorem rawCompletePhysicalForcing_diamond_of_root_visiblePrimes_perm
    {rho iota kappa tau iotaR kappaR tauR nu mu sigma : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (p q : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
    (hroot : family.visiblePrimes.Perm (p :: q :: S))
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
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    rawCompletePhysicalForcing owner lambda p (q :: S) family
        (removeVisiblePrime family p) sourceBasis +
      rawCompletePhysicalForcing owner lambda q S
        (removeVisiblePrime family p)
        (removeVisiblePrime (removeVisiblePrime family p) q) sourceBasis =
    rawCompletePhysicalForcing owner lambda q (p :: S) family
        (removeVisiblePrime family q) sourceBasis +
      rawCompletePhysicalForcing owner lambda p S
        (removeVisiblePrime family q)
        (removeVisiblePrime (removeVisiblePrime family q) p) sourceBasis := by
  let afterP := removeVisiblePrime family p
  let afterPQ := removeVisiblePrime afterP q
  let afterQ := removeVisiblePrime family q
  let afterQP := removeVisiblePrime afterQ p
  have hswap : (p :: q :: S).Perm (q :: p :: S) := by
    exact (List.Perm.swap p q S).symm
  have hrootQ : family.visiblePrimes.Perm (q :: p :: S) :=
    hroot.trans hswap
  have hP : afterP.visiblePrimes.Perm (q :: S) := by
    simpa only [afterP] using
      (removeVisiblePrime_visiblePrimes_perm_tail family p (q :: S) hroot)
  have hPQ : afterPQ.visiblePrimes.Perm S := by
    simpa only [afterP, afterPQ] using
      (removeVisiblePrime_visiblePrimes_perm_tail afterP q S hP)
  have hQ : afterQ.visiblePrimes.Perm (p :: S) := by
    simpa only [afterQ] using
      (removeVisiblePrime_visiblePrimes_perm_tail family q (p :: S) hrootQ)
  have hQP : afterQP.visiblePrimes.Perm S := by
    simpa only [afterQ, afterQP] using
      (removeVisiblePrime_visiblePrimes_perm_tail afterQ p S hQ)
  have hstepP :=
    rawCompletePhysicalHermitianTrace_cons_eq_add_forcing_of_visiblePrimeLists_perm
      owner lambda p (q :: S) family afterP hroot hP a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      pairedBoundaryBasis sourceBasis hfactor
  have hstepPQ :=
    rawCompletePhysicalHermitianTrace_cons_eq_add_forcing_of_visiblePrimeLists_perm
      owner lambda q S afterP afterPQ hP hPQ a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      pairedBoundaryBasis sourceBasis hfactor
  have hstepQ :=
    rawCompletePhysicalHermitianTrace_cons_eq_add_forcing_of_visiblePrimeLists_perm
      owner lambda q (p :: S) family afterQ hrootQ hQ a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      pairedBoundaryBasis sourceBasis hfactor
  have hstepQP :=
    rawCompletePhysicalHermitianTrace_cons_eq_add_forcing_of_visiblePrimeLists_perm
      owner lambda p S afterQ afterQP hQ hQP a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      pairedBoundaryBasis sourceBasis hfactor
  have htail := rawCompletePhysicalHermitianTrace_eq_of_visiblePrimes_perm
    owner lambda afterPQ afterQP (hPQ.trans hQP.symm) a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    sourceBasis hfactor
  dsimp only [afterP, afterPQ, afterQ, afterQP] at hstepP hstepPQ hstepQ hstepQP htail
  linarith

end CCM24FiniteSCausalMarkovRawPermutationDiamond
end CCM25Concrete
end Source
end ConnesWeilRH
