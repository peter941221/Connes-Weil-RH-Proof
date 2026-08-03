/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCausalMarkovRawPermutationCumulativeLedger

/-!
# Deletion-order invariance for the raw finite-S forcing chain

The raw completed physical trace is an endpoint scalar, while each deletion
step is represented by a signed Markov/remainder forcing.  A different order
of prime-block deletion changes every intermediate family and every summand.
This module proves that the complete signed sum is nevertheless invariant.

This is an exact discrete-potential statement.  It permits a future analytic
argument to choose a support-adapted deletion order before estimating the one
complete signed sum.  It supplies no absolute-value estimate.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCausalMarkovRawPermutationOrderInvariance

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
open CCM24FiniteSCausalMarkovRawBase
open CCM24FiniteSCausalMarkovRawPermutationCumulativeLedger
open CCM24FiniteSGramResponse
open CCM24FiniteSProjectionTrace
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The complete signed forcing sum is determined by the root visible-prime
set, even though its individual deletion steps use different intermediate
families.  This is the exact endpoint potential identity behind any legal
reordering of the raw Gate 3U forcing chain. -/
theorem rawCompletePhysicalPermutationForcingChain_eq_of_root_visiblePrimes_perm
    {rho iota kappa tau iotaR kappaR tauR nu mu sigma : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
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
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    {S T : List CCM24VisiblePrime}
    (first : RawCompletePhysicalPermutationFamilyChain S)
    (second : RawCompletePhysicalPermutationFamilyChain T)
    (hroot : first.family.visiblePrimes.Perm second.family.visiblePrimes) :
    rawCompletePhysicalPermutationForcingChain owner lambda sourceBasis first =
      rawCompletePhysicalPermutationForcingChain owner lambda sourceBasis second := by
  calc
    rawCompletePhysicalPermutationForcingChain owner lambda sourceBasis first =
        rawCompletePhysicalHermitianTrace owner lambda first.family a c hac hsupp
          reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
          globalBasis sourceBasis hfactor :=
      (rawCompletePhysicalHermitianTrace_eq_permutationForcingChain owner lambda
        a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor first).symm
    _ = rawCompletePhysicalHermitianTrace owner lambda second.family a c hac hsupp
          reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
          globalBasis sourceBasis hfactor :=
      rawCompletePhysicalHermitianTrace_eq_of_visiblePrimes_perm owner lambda
        first.family second.family hroot a c hac hsupp negativeBasis positiveBasis
        outputBasis reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis boundaryBasis sourceBasis hfactor
    _ = rawCompletePhysicalPermutationForcingChain owner lambda sourceBasis second :=
      rawCompletePhysicalHermitianTrace_eq_permutationForcingChain owner lambda
        a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor second

/-- Reindexing the deletion tower by a permutation of its target list leaves
the complete signed raw forcing sum unchanged. -/
theorem rawCompletePhysicalPermutationForcingChain_eq_of_targetList_perm
    {rho iota kappa tau iotaR kappaR tauR nu mu sigma : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
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
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    {S T : List CCM24VisiblePrime}
    (first : RawCompletePhysicalPermutationFamilyChain S)
    (second : RawCompletePhysicalPermutationFamilyChain T)
    (htarget : S.Perm T) :
    rawCompletePhysicalPermutationForcingChain owner lambda sourceBasis first =
      rawCompletePhysicalPermutationForcingChain owner lambda sourceBasis second := by
  apply rawCompletePhysicalPermutationForcingChain_eq_of_root_visiblePrimes_perm
    owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor first second
  exact (RawCompletePhysicalPermutationFamilyChain.family_visiblePrimes_perm first).trans
    (htarget.trans
      (RawCompletePhysicalPermutationFamilyChain.family_visiblePrimes_perm second).symm)

/-- The canonical raw forcing sum may be evaluated along any chosen ordering
of its visible primes.  The recursive family deletion remains literal; only
the target list order is changed. -/
theorem canonicalRawPermutationForcingChain_eq_of_order
    {rho iota kappa tau iotaR kappaR tauR nu mu sigma : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
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
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (T : List CCM24VisiblePrime)
    (horder : (canonicalFamily owner).visiblePrimes.Perm T) :
    rawCompletePhysicalPermutationForcingChain owner lambda sourceBasis
        (canonicalRawCompletePhysicalPermutationFamilyChain owner) =
      rawCompletePhysicalPermutationForcingChain owner lambda sourceBasis
        (rawCompletePhysicalPermutationFamilyChainOf (canonicalFamily owner) horder) := by
  exact rawCompletePhysicalPermutationForcingChain_eq_of_targetList_perm
    owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor
    (canonicalRawCompletePhysicalPermutationFamilyChain owner)
    (rawCompletePhysicalPermutationFamilyChainOf (canonicalFamily owner) horder)
    horder

/-- The canonical real Gate has an equivalent raw forcing readout along every
permutation of the canonical visible-prime list.  This gives future
compact-support analysis freedom to choose an order without changing the
scalar that must be bounded. -/
theorem canonicalRealGate3UAt_iff_abs_permutationForcingChainOf_le
    {rho iota kappa tau iotaR kappaR tauR nu mu sigma : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
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
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (T : List CCM24VisiblePrime)
    (horder : (canonicalFamily owner).visiblePrimes.Perm T)
    (bound : Real) :
    canonicalRealGate3UAt owner lambda sourceBasis bound <->
      |rawCompletePhysicalPermutationForcingChain owner lambda sourceBasis
        (rawCompletePhysicalPermutationFamilyChainOf (canonicalFamily owner)
          horder)| <= bound := by
  rw [canonicalRealGate3UAt_iff_abs_permutationForcingChain_le owner lambda
    a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor bound,
    canonicalRawPermutationForcingChain_eq_of_order owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      pairedBoundaryBasis sourceBasis hfactor T horder]

end CCM24FiniteSCausalMarkovRawPermutationOrderInvariance
end CCM25Concrete
end Source
end ConnesWeilRH
