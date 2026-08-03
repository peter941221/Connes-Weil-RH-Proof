/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCausalMarkovPermutationLedger
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCausalMarkovRawGateReadout

/-!
# Permutation-aware raw cumulative forcing ledger

The deletion of a prime-power block changes `Finset.toList` only up to
permutation.  This module therefore indexes the cumulative ledger by a
literal target list while storing actual finite families whose visible lists
are merely `List.Perm`-equal to that target.

The resulting recursion is a genuine finite telescoping identity.  It does
not estimate the signed forcing and does not prove Gate 3U.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCausalMarkovRawPermutationCumulativeLedger

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
open CCM24FiniteSCausalMarkovRawBase
open CCM24FiniteSCausalMarkovPermutationLedger
open CCM24FiniteSCausalMarkovRawGateReadout
open CCM24FiniteSGramResponse
open CCM24FiniteSProjectionTrace
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- A chain indexed by a literal target list.  Every actual family stored at a
node is only required to expose that target list up to permutation. -/
inductive RawCompletePhysicalPermutationFamilyChain :
    List CCM24VisiblePrime -> Type
  | nil (family : FinitePrimePowerFamily)
      (hvisible : family.visiblePrimes.Perm []) :
      RawCompletePhysicalPermutationFamilyChain []
  | cons (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
      (family : FinitePrimePowerFamily)
      (hvisible : family.visiblePrimes.Perm (p :: S))
      (tail : RawCompletePhysicalPermutationFamilyChain S) :
      RawCompletePhysicalPermutationFamilyChain (p :: S)

namespace RawCompletePhysicalPermutationFamilyChain

/-- The actual finite family stored at one chain node. -/
def family : {S : List CCM24VisiblePrime} ->
    RawCompletePhysicalPermutationFamilyChain S -> FinitePrimePowerFamily
  | [], .nil family _ => family
  | _ :: _, .cons _ _ family _ _ => family

/-- The stored family's visible list is permutation-equivalent to its index. -/
theorem family_visiblePrimes_perm : {S : List CCM24VisiblePrime} ->
    (chain : RawCompletePhysicalPermutationFamilyChain S) ->
    (family chain).visiblePrimes.Perm S
  | [], .nil _ hvisible => hvisible
  | _ :: _, .cons _ _ _ hvisible _ => hvisible

end RawCompletePhysicalPermutationFamilyChain

/-- The signed forcing sum along a permutation-aware chain. -/
noncomputable def rawCompletePhysicalPermutationForcingChain
    {rho : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda)) :
    {S : List CCM24VisiblePrime} ->
      RawCompletePhysicalPermutationFamilyChain S -> ℝ
  | [], _ => 0
  | p :: S, .cons _ _ family _ tail =>
      rawCompletePhysicalForcing owner lambda p S family tail.family sourceBasis +
        rawCompletePhysicalPermutationForcingChain owner lambda sourceBasis tail

/-- The raw physical trace is exactly the signed forcing sum along the actual
permutation-aware deletion chain. -/
theorem rawCompletePhysicalHermitianTrace_eq_permutationForcingChain
    {rho ι κ tau ιr κr taur nu mu sigma : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (a c : ℝ) (hac : a <= c)
    (hsupp : Function.support owner.sourceTest.test <= Set.Icc a c)
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
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    {S : List CCM24VisiblePrime}
    (chain : RawCompletePhysicalPermutationFamilyChain S) :
    rawCompletePhysicalHermitianTrace owner lambda chain.family a c hac hsupp
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis sourceBasis hfactor =
      rawCompletePhysicalPermutationForcingChain owner lambda sourceBasis chain := by
  induction chain with
  | nil family hvisible =>
      have hnil : family.visiblePrimes = [] := by
        apply List.length_eq_zero_iff.mp
        simpa using hvisible.length_eq
      simpa [RawCompletePhysicalPermutationFamilyChain.family,
        rawCompletePhysicalPermutationForcingChain] using
        (rawCompletePhysicalHermitianTrace_eq_zero_of_visiblePrimes_nil
          owner lambda family hnil a c hac hsupp
          negativeBasis positiveBasis outputBasis reflectedNegativeBasis
          reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
          sourceBasis hfactor)
  | cons p S family hvisible tail ih =>
      calc
        rawCompletePhysicalHermitianTrace owner lambda family a c hac hsupp
            reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
            globalBasis sourceBasis hfactor =
          rawCompletePhysicalHermitianTrace owner lambda tail.family
              a c hac hsupp reflectedNegativeBasis reflectedPositiveBasis
              reflectedOutputBasis globalBasis sourceBasis hfactor +
            rawCompletePhysicalForcing owner lambda p S family tail.family
              sourceBasis :=
          rawCompletePhysicalHermitianTrace_cons_eq_add_forcing_of_visiblePrimeLists_perm
            owner lambda p S family tail.family hvisible tail.family_visiblePrimes_perm
            a c hac hsupp negativeBasis positiveBasis outputBasis
            reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
            globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor
        _ = rawCompletePhysicalForcing owner lambda p S family tail.family
              sourceBasis + rawCompletePhysicalPermutationForcingChain owner lambda
                sourceBasis tail := by
          rw [ih]
          ring
        _ = rawCompletePhysicalPermutationForcingChain owner lambda sourceBasis
              (.cons p S family hvisible tail) := rfl

/-- Recursively construct a permutation-aware chain by deleting all terms at
the head visible prime.  The recursion is on the target list, not on the
choice-dependent order of `Finset.toList`. -/
noncomputable def rawCompletePhysicalPermutationFamilyChainOf :
    {S : List CCM24VisiblePrime} ->
      (family : FinitePrimePowerFamily) ->
      family.visiblePrimes.Perm S ->
      RawCompletePhysicalPermutationFamilyChain S
  | [], family, hvisible =>
      .nil family hvisible
  | p :: S, family, hvisible =>
      .cons p S family hvisible
        (rawCompletePhysicalPermutationFamilyChainOf
          (removeVisiblePrime family p)
          (removeVisiblePrime_visiblePrimes_perm_tail family p S hvisible))

/-- Recursive construction preserves the actual root family at every target
list shape. -/
theorem rawCompletePhysicalPermutationFamilyChainOf_family
    {S : List CCM24VisiblePrime} (family : FinitePrimePowerFamily)
    (hvisible : family.visiblePrimes.Perm S) :
    (rawCompletePhysicalPermutationFamilyChainOf family hvisible).family = family := by
  cases S <;> rfl

/-- The actual canonical selected family has a concrete permutation-aware
term-deletion chain, with no global list-to-family choice function. -/
noncomputable def canonicalRawCompletePhysicalPermutationFamilyChain
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    RawCompletePhysicalPermutationFamilyChain
      (canonicalFamily owner).visiblePrimes :=
  rawCompletePhysicalPermutationFamilyChainOf (canonicalFamily owner)
    (List.Perm.refl _)

/-- The root family of the canonical deletion chain is definitionally the
canonical arithmetic family. -/
theorem canonicalRawCompletePhysicalPermutationFamilyChain_family
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    (canonicalRawCompletePhysicalPermutationFamilyChain owner).family =
      canonicalFamily owner := by
  exact rawCompletePhysicalPermutationFamilyChainOf_family
    (canonicalFamily owner) (List.Perm.refl _)

/-- The literal canonical raw trace is the signed forcing sum of its actual
term-deletion tower. -/
theorem rawCompletePhysicalHermitianTrace_canonical_eq_permutationForcingChain
    {rho ι κ tau ιr κr taur nu mu sigma : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (a c : ℝ) (hac : a <= c)
    (hsupp : Function.support owner.sourceTest.test <= Set.Icc a c)
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
    rawCompletePhysicalHermitianTrace owner lambda (canonicalFamily owner)
        a c hac hsupp reflectedNegativeBasis reflectedPositiveBasis
        reflectedOutputBasis globalBasis sourceBasis hfactor =
      rawCompletePhysicalPermutationForcingChain owner lambda sourceBasis
        (canonicalRawCompletePhysicalPermutationFamilyChain owner) := by
  simpa only [canonicalRawCompletePhysicalPermutationFamilyChain,
    rawCompletePhysicalPermutationFamilyChainOf_family] using
    (rawCompletePhysicalHermitianTrace_eq_permutationForcingChain owner lambda
      a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor
      (rawCompletePhysicalPermutationFamilyChainOf (canonicalFamily owner)
        (List.Perm.refl _)))

/-- The canonical real Gate is precisely the absolute signed forcing sum over
the actual term-deletion tower.  A bound for this one scalar reaches Gate 3U
without a lower-factor conversion. -/
theorem canonicalRealGate3UAt_iff_abs_permutationForcingChain_le
    {rho ι κ tau ιr κr taur nu mu sigma : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (a c : ℝ) (hac : a <= c)
    (hsupp : Function.support owner.sourceTest.test <= Set.Icc a c)
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
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (bound : ℝ) :
    canonicalRealGate3UAt owner lambda sourceBasis bound ↔
      |rawCompletePhysicalPermutationForcingChain owner lambda sourceBasis
        (canonicalRawCompletePhysicalPermutationFamilyChain owner)| <= bound := by
  rw [canonicalRealGate3UAt_iff_abs_rawCompletePhysicalHermitianTrace_le owner
    lambda a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor bound,
    rawCompletePhysicalHermitianTrace_canonical_eq_permutationForcingChain
      owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor]

end CCM24FiniteSCausalMarkovRawPermutationCumulativeLedger
end CCM25Concrete
end Source
end ConnesWeilRH
