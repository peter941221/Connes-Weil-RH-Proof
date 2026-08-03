/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCausalMarkovPermutationInvariance
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCausalMarkovRawPermutationCumulativeLedger
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCausalMarkovRawRenewalBridge

/-!
# Operator-level cumulative ledger for the raw renewal forcing

Proof 805 identifies one raw forcing with the real trace of one signed
inverse-lower-factor physical renewal difference.  This module assembles
those differences along an actual permutation-aware deletion tower before
taking any trace.  The resulting finite operator sum telescopes to the
negative root renewal response and is invariant under every compatible
deletion order.

This is a same-object bookkeeping result.  It does not estimate the operator
sum, its trace, or the Gate 3U scalar.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCausalMarkovRawRenewalCumulativeLedger

open MeasureTheory
open scoped BigOperators InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSActualBandSourceRemainder
open CCM24FiniteSBandTrace
open CCM24FiniteSCanonicalCompletedResponse
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSCausalMarkovPermutationInvariance
open CCM24FiniteSCausalMarkovRawBase
open CCM24FiniteSCausalMarkovRawPermutationCumulativeLedger
open CCM24FiniteSCausalMarkovRawRenewalBridge
open CCM24FiniteSGramResponse
open CCM24FiniteSPhysicalLeakage
open CCM24FiniteSProjectionTrace
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The actual family at the terminal node of a permutation-aware deletion
tower.  Its visible-prime list is empty, even though intermediate lists are
stored only up to permutation. -/
def rawPhysicalRenewalTerminalFamily :
    {S : List CCM24VisiblePrime} ->
      RawCompletePhysicalPermutationFamilyChain S -> FinitePrimePowerFamily
  | [], .nil family _ => family
  | _ :: _, .cons _ _ _ _ tail => rawPhysicalRenewalTerminalFamily tail

/-- The terminal family of every permutation-aware deletion tower has no
visible prime. -/
theorem rawPhysicalRenewalTerminalFamily_visiblePrimes_eq_nil :
    {S : List CCM24VisiblePrime} ->
      (chain : RawCompletePhysicalPermutationFamilyChain S) ->
      (rawPhysicalRenewalTerminalFamily chain).visiblePrimes = []
  | [], .nil family hvisible => by
      apply List.length_eq_zero_iff.mp
      simpa using hvisible.length_eq
  | _ :: _, .cons _ _ _ _ tail =>
      rawPhysicalRenewalTerminalFamily_visiblePrimes_eq_nil tail

/-- The complete inverse-lower-factor renewal response vanishes at the
terminal empty-place family. -/
theorem inverseLowerFactorPhysicalRenewalResponse_eq_zero_of_visiblePrimes_nil
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (hvisible : family.visiblePrimes = []) :
    inverseLowerFactorPhysicalRenewalResponse owner lambda family = 0 := by
  have hresponse : sourceBandGramResponse owner lambda family = 0 := by
    rw [sourceBandGramResponse_eq_neg_physical_leakage,
      sourcePhysicalCoframeLeakage_eq_zero_of_visiblePrimes_nil
        lambda family hvisible]
    simp
  rw [inverseLowerFactorPhysicalRenewalResponse_eq_sourceBandGramResponse,
    hresponse]

/-- The signed renewal-response sum along a literal deletion tower.  Each
summand keeps both adjacent full physical renewal responses inside one
operator subtraction. -/
noncomputable def rawPhysicalRenewalPermutationForcingResponseChain
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) :
    {S : List CCM24VisiblePrime} ->
      RawCompletePhysicalPermutationFamilyChain S ->
        sourceSoninCarrier lambda →L[ℂ] sourceSoninCarrier lambda
  | [], _ => 0
  | _ :: _, .cons _ _ family _ tail =>
      rawPhysicalRenewalForcingResponse owner lambda family tail.family +
        rawPhysicalRenewalPermutationForcingResponseChain owner lambda tail

/-- Before a trace is taken, the full renewal-response sum telescopes to the
terminal response minus the root response. -/
theorem rawPhysicalRenewalPermutationForcingResponseChain_eq_terminal_sub_root
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    {S : List CCM24VisiblePrime}
    (chain : RawCompletePhysicalPermutationFamilyChain S) :
    rawPhysicalRenewalPermutationForcingResponseChain owner lambda chain =
      inverseLowerFactorPhysicalRenewalResponse owner lambda
          (rawPhysicalRenewalTerminalFamily chain) -
        inverseLowerFactorPhysicalRenewalResponse owner lambda chain.family := by
  induction chain with
  | nil family hvisible =>
      simp [rawPhysicalRenewalPermutationForcingResponseChain,
        rawPhysicalRenewalTerminalFamily,
        RawCompletePhysicalPermutationFamilyChain.family]
  | cons p S family hvisible tail ih =>
      change
        (inverseLowerFactorPhysicalRenewalResponse owner lambda tail.family -
            inverseLowerFactorPhysicalRenewalResponse owner lambda family) +
          rawPhysicalRenewalPermutationForcingResponseChain owner lambda tail =
        inverseLowerFactorPhysicalRenewalResponse owner lambda
            (rawPhysicalRenewalTerminalFamily tail) -
          inverseLowerFactorPhysicalRenewalResponse owner lambda family
      rw [ih]
      abel

/-- The empty terminal response removes the terminal endpoint, leaving one
negative complete renewal response for the root family. -/
theorem rawPhysicalRenewalPermutationForcingResponseChain_eq_neg_root
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    {S : List CCM24VisiblePrime}
    (chain : RawCompletePhysicalPermutationFamilyChain S) :
    rawPhysicalRenewalPermutationForcingResponseChain owner lambda chain =
      -inverseLowerFactorPhysicalRenewalResponse owner lambda chain.family := by
  rw [rawPhysicalRenewalPermutationForcingResponseChain_eq_terminal_sub_root]
  have hterminal :=
    inverseLowerFactorPhysicalRenewalResponse_eq_zero_of_visiblePrimes_nil
      owner lambda (rawPhysicalRenewalTerminalFamily chain)
      (rawPhysicalRenewalTerminalFamily_visiblePrimes_eq_nil chain)
  rw [hterminal]
  simp

/-- Compatible deletion towers with permutation-equivalent root visible lists
have the same signed renewal-response operator before any trace or real part.
-/
theorem rawPhysicalRenewalPermutationForcingResponseChain_eq_of_root_visiblePrimes_perm
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    {S T : List CCM24VisiblePrime}
    (first : RawCompletePhysicalPermutationFamilyChain S)
    (second : RawCompletePhysicalPermutationFamilyChain T)
    (hroot : first.family.visiblePrimes.Perm second.family.visiblePrimes) :
    rawPhysicalRenewalPermutationForcingResponseChain owner lambda first =
      rawPhysicalRenewalPermutationForcingResponseChain owner lambda second := by
  calc
    rawPhysicalRenewalPermutationForcingResponseChain owner lambda first =
        -inverseLowerFactorPhysicalRenewalResponse owner lambda first.family :=
      rawPhysicalRenewalPermutationForcingResponseChain_eq_neg_root
        owner lambda first
    _ = -(sourceBandGramResponse owner lambda first.family) := by
      rw [inverseLowerFactorPhysicalRenewalResponse_eq_sourceBandGramResponse]
    _ = -(sourceBandGramResponse owner lambda second.family) := by
      rw [sourceBandGramResponse_eq_of_visiblePrimes_perm owner lambda
        first.family second.family hroot]
    _ = -inverseLowerFactorPhysicalRenewalResponse owner lambda second.family := by
      rw [inverseLowerFactorPhysicalRenewalResponse_eq_sourceBandGramResponse]
    _ = rawPhysicalRenewalPermutationForcingResponseChain owner lambda second :=
      (rawPhysicalRenewalPermutationForcingResponseChain_eq_neg_root
        owner lambda second).symm

/-- The cumulative signed renewal response inherits trace legality from the
one root renewal response, after operator-level telescoping has occurred. -/
theorem rawPhysicalRenewalPermutationForcingResponseChain_isTraceClassAlong
    {rho iota kappa tau iotaR kappaR tauR nu mu : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    {S : List CCM24VisiblePrime}
    (chain : RawCompletePhysicalPermutationFamilyChain S)
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
      (rawPhysicalRenewalPermutationForcingResponseChain owner lambda chain) := by
  rw [rawPhysicalRenewalPermutationForcingResponseChain_eq_neg_root]
  exact CCM24FiniteSProjectionTrace.PositiveTrace.isTraceClassAlong_neg sourceBasis _
    (inverseLowerFactorPhysicalRenewalResponse_isTraceClassAlong owner lambda
      chain.family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor)

/-- The scalar raw forcing chain is the real ordinary trace of the one
operator-level cumulative renewal ledger.  Thus all cancellation is retained
until after the cumulative operator has been formed. -/
theorem rawCompletePhysicalPermutationForcingChain_eq_rawPhysicalRenewalResponseChainTrace_re
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
      norm (sourceProlateHilbertSchmidtFactor lambda (globalBasis i)) ^ 2)
    {S : List CCM24VisiblePrime}
    (chain : RawCompletePhysicalPermutationFamilyChain S) :
    rawCompletePhysicalPermutationForcingChain owner lambda sourceBasis chain =
      (ordinaryTraceAlong sourceBasis
        (rawPhysicalRenewalPermutationForcingResponseChain owner lambda chain)).re := by
  calc
    rawCompletePhysicalPermutationForcingChain owner lambda sourceBasis chain =
        rawCompletePhysicalHermitianTrace owner lambda chain.family a c hac hsupp
          reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
          globalBasis sourceBasis hfactor :=
      (rawCompletePhysicalHermitianTrace_eq_permutationForcingChain owner lambda
        a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor chain).symm
    _ = -inverseLowerFactorPhysicalRenewalTrace owner lambda chain.family
          sourceBasis :=
      rawCompletePhysicalHermitianTrace_eq_neg_inverseLowerFactorPhysicalRenewalTrace
        owner lambda chain.family a c hac hsupp negativeBasis positiveBasis
          outputBasis reflectedNegativeBasis reflectedPositiveBasis
          reflectedOutputBasis globalBasis boundaryBasis sourceBasis hfactor
    _ = (ordinaryTraceAlong sourceBasis
          (rawPhysicalRenewalPermutationForcingResponseChain owner lambda chain)).re := by
      rw [rawPhysicalRenewalPermutationForcingResponseChain_eq_neg_root,
        CCM24FiniteSProjectionTrace.PositiveTrace.ordinaryTraceAlong_neg]
      simp [inverseLowerFactorPhysicalRenewalTrace]

end CCM24FiniteSCausalMarkovRawRenewalCumulativeLedger
end CCM25Concrete
end Source
end ConnesWeilRH
