/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCausalMarkovPermutationInvariance

/-!
# Permutation-aware raw one-prime ledger

`FinitePrimePowerFamily.visiblePrimes` is represented by `Finset.toList`, so
deleting a prime-power block produces a family whose visible list is only a
permutation of the expected literal tail.  This module upgrades the raw
one-prime ledger to that exact situation.

The theorem keeps the same complete Markov-coboundary/remainder forcing as
Proof 797.  It supplies no forcing bound and does not turn a list permutation
into a Gate 3U estimate.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCausalMarkovPermutationLedger

open MeasureTheory
open scoped BigOperators InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSActualBandSourceRemainder
open CCM24FiniteSBandTrace
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSCausalMarkovCompletedFirstDifference
open CCM24FiniteSCausalMarkovCompletedPhysicalDifference
open CCM24FiniteSCausalMarkovPermutationInvariance
open CCM24FiniteSCausalMarkovRawBase
open CCM24FiniteSCoframeResponse
open CCM24FiniteSGramResponse
open CCM24FiniteSProjectionTrace
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- Delete every prime-power term at one visible prime while preserving the
arithmetic side conditions on the surviving actual family. -/
noncomputable def removeVisiblePrime
    (family : FinitePrimePowerFamily) (p : CCM24VisiblePrime) :
    FinitePrimePowerFamily where
  terms := family.terms.filter fun pm => pm.1 ≠ p.1
  prime := fun pm hpm => family.prime pm (Finset.mem_filter.mp hpm).1
  exponent_ne_zero := fun pm hpm =>
    family.exponent_ne_zero pm (Finset.mem_filter.mp hpm).1

/-- Membership in the visible places of the deleted family is exactly
membership in the old visible places away from the deleted prime. -/
theorem mem_removeVisiblePrime_visiblePrimes_iff
    (family : FinitePrimePowerFamily) (p q : CCM24VisiblePrime) :
    q ∈ (removeVisiblePrime family p).visiblePrimes ↔
      q ≠ p ∧ q ∈ family.visiblePrimes := by
  constructor
  · intro hq
    rw [FinitePrimePowerFamily.visiblePrimes, Finset.mem_toList,
      Finset.mem_image] at hq
    obtain ⟨pm, -, hpmq⟩ := hq
    have hfilter : pm.1 ∈ family.terms.filter fun term => term.1 ≠ p.1 := by
      simpa [removeVisiblePrime] using pm.2
    have hterm : pm.1 ∈ family.terms := (Finset.mem_filter.mp hfilter).1
    have hprimeNe : pm.1.1 ≠ p.1 := (Finset.mem_filter.mp hfilter).2
    refine ⟨?_, ?_⟩
    · intro hqeq
      apply hprimeNe
      have hvalue := congrArg Subtype.val hpmq
      simpa [hqeq] using hvalue
    · rw [FinitePrimePowerFamily.visiblePrimes, Finset.mem_toList,
        Finset.mem_image]
      refine ⟨⟨pm.1, hterm⟩, Finset.mem_attach _ _, ?_⟩
      apply Subtype.ext
      exact congrArg Subtype.val hpmq
  · rintro ⟨hqne, hq⟩
    rw [FinitePrimePowerFamily.visiblePrimes, Finset.mem_toList,
      Finset.mem_image] at hq ⊢
    obtain ⟨pm, -, hpmq⟩ := hq
    have hvalue : pm.1.1 = q.1 := congrArg Subtype.val hpmq
    have hprimeNe : pm.1.1 ≠ p.1 := by
      intro hprime
      apply hqne
      apply Subtype.ext
      calc
        q.1 = pm.1.1 := hvalue.symm
        _ = p.1 := hprime
    have hfilter : pm.1 ∈ family.terms.filter fun term => term.1 ≠ p.1 :=
      Finset.mem_filter.mpr ⟨pm.2, hprimeNe⟩
    refine ⟨⟨pm.1, hfilter⟩, Finset.mem_attach _ _, ?_⟩
    apply Subtype.ext
    exact hvalue

/-- Removing one visible prime changes the arbitrary `Finset.toList`
representative only by erasing that prime up to permutation. -/
theorem removeVisiblePrime_visiblePrimes_perm_erase
    (family : FinitePrimePowerFamily) (p : CCM24VisiblePrime) :
    (removeVisiblePrime family p).visiblePrimes.Perm
      (family.visiblePrimes.erase p) := by
  apply List.perm_of_nodup_nodup_toFinset_eq
  · exact FinitePrimePowerFamily.visiblePrimes_nodup _
  · exact (FinitePrimePowerFamily.visiblePrimes_nodup family).erase _
  ext q
  simp only [List.mem_toFinset]
  rw [(FinitePrimePowerFamily.visiblePrimes_nodup family).mem_erase_iff]
  exact mem_removeVisiblePrime_visiblePrimes_iff family p q

/-- If a family represents `p :: S` up to permutation, deleting all its
`p`-power terms represents the suffix `S` up to permutation. -/
theorem removeVisiblePrime_visiblePrimes_perm_tail
    (family : FinitePrimePowerFamily) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime)
    (hvisible : family.visiblePrimes.Perm (p :: S)) :
    (removeVisiblePrime family p).visiblePrimes.Perm S := by
  have htargetNodup : (p :: S).Nodup :=
    hvisible.nodup_iff.mp (FinitePrimePowerFamily.visiblePrimes_nodup family)
  have htargetSplit : p ∉ S ∧ S.Nodup := by
    simpa only [List.nodup_cons] using htargetNodup
  have herase : (family.visiblePrimes.erase p).Perm S := by
    apply List.perm_of_nodup_nodup_toFinset_eq
    · exact (FinitePrimePowerFamily.visiblePrimes_nodup family).erase _
    · exact htargetSplit.2
    ext q
    simp only [List.mem_toFinset]
    constructor
    · intro hq
      have hq' : q ≠ p ∧ q ∈ family.visiblePrimes :=
        (FinitePrimePowerFamily.visiblePrimes_nodup family).mem_erase_iff.mp hq
      have hqcons : q ∈ p :: S := hvisible.mem_iff.mp hq'.2
      simpa [hq'.1] using hqcons
    · intro hq
      have hqcons : q ∈ p :: S := by simp [hq]
      have hqfamily : q ∈ family.visiblePrimes := hvisible.mem_iff.mpr hqcons
      have hqne : q ≠ p := by
        intro hqeq
        subst q
        exact htargetSplit.1 hq
      exact (FinitePrimePowerFamily.visiblePrimes_nodup family).mem_erase_iff.mpr
        ⟨hqne, hqfamily⟩
  exact (removeVisiblePrime_visiblePrimes_perm_erase family p).trans herase

/-- The source endpoint increment has the same completed ledger when the old
family is represented by a permutation of the literal suffix. -/
theorem sourceBandGramIncrement_eq_coboundary_sub_remainder_of_visiblePrimeList_perm
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (newFamily oldFamily : FinitePrimePowerFamily)
    (hnew : newFamily.visiblePrimes = p :: S)
    (hold : oldFamily.visiblePrimes.Perm S) :
    sourceBandGramIncrement owner lambda newFamily oldFamily =
      normalizedListActualBandSoninCoboundary owner lambda p S -
        sourceActualBandFiniteEulerRemainderIncrement owner lambda newFamily oldFamily := by
  have hremainder :
      sourceActualBandFiniteEulerRemainderIncrement owner lambda newFamily oldFamily =
        normalizedListActualBandSoninCoboundary owner lambda p S -
          sourceBandGramIncrement owner lambda newFamily oldFamily := by
    unfold sourceActualBandFiniteEulerRemainderIncrement sourceBandGramIncrement
      sourceActualBandFiniteEulerRemainderResponse
    calc
      _ = (sourceActualBandFiniteEulerSoninResponse owner lambda newFamily -
            sourceActualBandFiniteEulerSoninResponse owner lambda oldFamily) -
          (sourceBandGramResponse owner lambda newFamily -
            sourceBandGramResponse owner lambda oldFamily) := by
        abel
      _ = _ := by
        rw [sourceActualBandFiniteEulerSoninResponse_sub_eq_coboundary_of_visiblePrimeList_perm
          owner lambda p S newFamily oldFamily hnew hold]
  rw [hremainder]
  abel

/-- The endpoint ledger with both family lists represented only up to
permutation. -/
theorem sourceBandGramIncrement_eq_coboundary_sub_remainder_of_visiblePrimeLists_perm
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (newFamily oldFamily : FinitePrimePowerFamily)
    (hnew : newFamily.visiblePrimes.Perm (p :: S))
    (hold : oldFamily.visiblePrimes.Perm S) :
    sourceBandGramIncrement owner lambda newFamily oldFamily =
      normalizedListActualBandSoninCoboundary owner lambda p S -
        sourceActualBandFiniteEulerRemainderIncrement owner lambda newFamily oldFamily := by
  have hremainder :
      sourceActualBandFiniteEulerRemainderIncrement owner lambda newFamily oldFamily =
        normalizedListActualBandSoninCoboundary owner lambda p S -
          sourceBandGramIncrement owner lambda newFamily oldFamily := by
    unfold sourceActualBandFiniteEulerRemainderIncrement sourceBandGramIncrement
      sourceActualBandFiniteEulerRemainderResponse
    calc
      _ = (sourceActualBandFiniteEulerSoninResponse owner lambda newFamily -
            sourceActualBandFiniteEulerSoninResponse owner lambda oldFamily) -
          (sourceBandGramResponse owner lambda newFamily -
            sourceBandGramResponse owner lambda oldFamily) := by
        abel
      _ = _ := by
        rw [sourceActualBandFiniteEulerSoninResponse_sub_eq_coboundary_of_visiblePrimeLists_perm
          owner lambda p S newFamily oldFamily hnew hold]
  rw [hremainder]
  abel

/-- The trace-level completed ledger remains legal for a permutation-aware
suffix because the two actual family endpoints supply the trace-class
witnesses. -/
theorem
    ordinaryTraceAlong_sourceBandGramIncrement_eq_coboundary_sub_remainder_of_visiblePrimeList_perm
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (newFamily oldFamily : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hnew : newFamily.visiblePrimes = p :: S)
    (hold : oldFamily.visiblePrimes.Perm S)
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
    rw [← sourceActualBandFiniteEulerSoninResponse_sub_eq_coboundary_of_visiblePrimeList_perm
      owner lambda p S newFamily oldFamily hnew hold]
    exact isTraceClassAlong_sub sourceBasis _ _ hfirstNew hfirstOld
  have hremainders : IsTraceClassAlong sourceBasis
      (sourceActualBandFiniteEulerRemainderIncrement owner lambda newFamily oldFamily) := by
    unfold sourceActualBandFiniteEulerRemainderIncrement
    exact isTraceClassAlong_sub sourceBasis _ _ hremainderNew hremainderOld
  rw [sourceBandGramIncrement_eq_coboundary_sub_remainder_of_visiblePrimeList_perm
    owner lambda p S newFamily oldFamily hnew hold]
  exact ordinaryTraceAlong_sub sourceBasis _ _ hcoboundary hremainders

/-- Trace legality for the stronger two-sided permutation-aware ledger. -/
theorem
    ordinaryTraceAlong_sourceBandGramIncrement_eq_coboundary_sub_remainder_of_visiblePrimeLists_perm
    {rho : Type*} (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (newFamily oldFamily : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hnew : newFamily.visiblePrimes.Perm (p :: S))
    (hold : oldFamily.visiblePrimes.Perm S)
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
    rw [← sourceActualBandFiniteEulerSoninResponse_sub_eq_coboundary_of_visiblePrimeLists_perm
      owner lambda p S newFamily oldFamily hnew hold]
    exact isTraceClassAlong_sub sourceBasis _ _ hfirstNew hfirstOld
  have hremainders : IsTraceClassAlong sourceBasis
      (sourceActualBandFiniteEulerRemainderIncrement owner lambda newFamily oldFamily) := by
    unfold sourceActualBandFiniteEulerRemainderIncrement
    exact isTraceClassAlong_sub sourceBasis _ _ hremainderNew hremainderOld
  rw [sourceBandGramIncrement_eq_coboundary_sub_remainder_of_visiblePrimeLists_perm
    owner lambda p S newFamily oldFamily hnew hold]
  exact ordinaryTraceAlong_sub sourceBasis _ _ hcoboundary hremainders

set_option maxHeartbeats 1200000 in
-- The complete physical trace readbacks unfold all four boundary coordinates.
/-- The raw completed physical trace evolves by the same literal forcing if
the old actual family exposes a permutation of the expected tail.  This is
the one-prime ledger needed by an actual term-deletion tower. -/
theorem rawCompletePhysicalHermitianTrace_cons_eq_add_forcing_of_visiblePrimeLists_perm
    {rho ι κ tau ιr κr taur nu mu sigma : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (newFamily oldFamily : FinitePrimePowerFamily)
    (hnew : newFamily.visiblePrimes.Perm (p :: S))
    (hold : oldFamily.visiblePrimes.Perm S)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
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
    rawCompletePhysicalHermitianTrace owner lambda newFamily a c hac hsupp
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis sourceBasis hfactor =
      rawCompletePhysicalHermitianTrace owner lambda oldFamily a c hac hsupp
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis sourceBasis hfactor +
      rawCompletePhysicalForcing owner lambda p S newFamily oldFamily
        sourceBasis := by
  have hphysicalNew :=
    completePhysicalHermitianTrace_eq_neg_sourceBandGramRealTrace owner lambda
      newFamily a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor
  have hphysicalOld :=
    completePhysicalHermitianTrace_eq_neg_sourceBandGramRealTrace owner lambda
      oldFamily a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor
  have hphysicalNewRe := congrArg Complex.re hphysicalNew
  have hphysicalOldRe := congrArg Complex.re hphysicalOld
  simp only [Complex.neg_re, Complex.ofReal_re] at hphysicalNewRe hphysicalOldRe
  have hendpointNew := sourceBandGramResponse_isTraceClassAlong owner lambda
    newFamily a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor
  have hendpointOld := sourceBandGramResponse_isTraceClassAlong owner lambda
    oldFamily a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor
  have hendpointIncrementTrace :
      ordinaryTraceAlong sourceBasis
          (sourceBandGramIncrement owner lambda newFamily oldFamily) =
        ordinaryTraceAlong sourceBasis
          (sourceBandGramResponse owner lambda newFamily) -
          ordinaryTraceAlong sourceBasis
            (sourceBandGramResponse owner lambda oldFamily) := by
    unfold sourceBandGramIncrement
    exact ordinaryTraceAlong_sub sourceBasis _ _ hendpointNew hendpointOld
  have hledger :=
    ordinaryTraceAlong_sourceBandGramIncrement_eq_coboundary_sub_remainder_of_visiblePrimeLists_perm
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
  have hrawTrace :
      ordinaryTraceAlong sourceBasis
          (sourceBandGramResponse owner lambda newFamily) -
          ordinaryTraceAlong sourceBasis
            (sourceBandGramResponse owner lambda oldFamily) =
        ordinaryTraceAlong sourceBasis
            (normalizedListActualBandSoninCoboundary owner lambda p S) -
          ordinaryTraceAlong sourceBasis
            (sourceActualBandFiniteEulerRemainderIncrement owner lambda
              newFamily oldFamily) := by
    rw [← hendpointIncrementTrace]
    exact hledger
  have hrawTraceRe := congrArg Complex.re hrawTrace
  simp only [Complex.sub_re] at hrawTraceRe
  unfold rawCompletePhysicalHermitianTrace rawCompletePhysicalForcing
  rw [hphysicalNewRe, hphysicalOldRe]
  linarith

/-- Compatibility wrapper for the earlier exact-new-list interface. -/
theorem rawCompletePhysicalHermitianTrace_cons_eq_add_forcing_of_visiblePrimeList_perm
    {rho ι κ tau ιr κr taur nu mu sigma : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (newFamily oldFamily : FinitePrimePowerFamily)
    (hnew : newFamily.visiblePrimes = p :: S)
    (hold : oldFamily.visiblePrimes.Perm S)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
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
    rawCompletePhysicalHermitianTrace owner lambda newFamily a c hac hsupp
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis sourceBasis hfactor =
      rawCompletePhysicalHermitianTrace owner lambda oldFamily a c hac hsupp
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis sourceBasis hfactor +
      rawCompletePhysicalForcing owner lambda p S newFamily oldFamily
        sourceBasis := by
  exact rawCompletePhysicalHermitianTrace_cons_eq_add_forcing_of_visiblePrimeLists_perm
    owner lambda p S newFamily oldFamily (List.Perm.of_eq hnew) hold a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    pairedBoundaryBasis sourceBasis hfactor

end CCM24FiniteSCausalMarkovPermutationLedger
end CCM25Concrete
end Source
end ConnesWeilRH
