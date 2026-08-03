/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCausalMarkovRawBase

/-!
# Raw cumulative finite-S forcing ledger

The raw completed physical trace has a zero-prime base point and an exact
unscaled one-prime increment.  This module closes the finite-list bookkeeping:
along any compatible finite-family chain, the literal raw trace is the signed
sum of those same recombined forcings.

No absolute value, lower-factor normalization, or branchwise estimate occurs
here.  A Gate 3U proof must bound this signed cumulative source quantity using
the actual Hardy--prolate geometry before its first absolute value.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCausalMarkovRawCumulativeLedger

open MeasureTheory
open scoped BigOperators InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSActualBandSourceRemainder
open CCM24FiniteSBandTrace
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSCausalMarkovRawBase
open CCM24FiniteSCoframeResponse
open CCM24FiniteSGramResponse
open CCM24FiniteSGramOrderingBridge
open CCM24FiniteSPhysicalLeakage
open CCM24FiniteSProjectionTrace
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/- A concrete compatible chain holds only the families needed by one finite
visible-prime list and its suffixes.  A global map over all lists would be
uninhabited because visible-prime lists are nodup while arbitrary lists need
not be. -/
inductive RawCompletePhysicalFamilyChain :
    List CCM24VisiblePrime -> Type
  | nil (family : FinitePrimePowerFamily)
      (hvisible : family.visiblePrimes = []) :
      RawCompletePhysicalFamilyChain []
  | cons (p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)
      (family : FinitePrimePowerFamily)
      (hvisible : family.visiblePrimes = p :: S)
      (tail : RawCompletePhysicalFamilyChain S) :
      RawCompletePhysicalFamilyChain (p :: S)

namespace RawCompletePhysicalFamilyChain

/-- The actual family stored at one node of a finite compatible chain. -/
def family : {S : List CCM24VisiblePrime} ->
    RawCompletePhysicalFamilyChain S -> FinitePrimePowerFamily
  | [], .nil family _ => family
  | _ :: _, .cons _ _ family _ _ => family

/-- Every stored family has exactly the visible-prime list indexing its node. -/
theorem family_visiblePrimes : {S : List CCM24VisiblePrime} ->
    (chain : RawCompletePhysicalFamilyChain S) ->
    (family chain).visiblePrimes = S
  | [], .nil _ hvisible => hvisible
  | _ :: _, .cons _ _ _ hvisible _ => hvisible

end RawCompletePhysicalFamilyChain

/-- The literal signed sum of raw one-prime forcings along a concrete
compatible finite-family chain.  Every term retains the actual new and old
finite prime-power families required by the completed remainder. -/
noncomputable def rawCompletePhysicalForcingChain
    {rho : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda)) :
    {S : List CCM24VisiblePrime} -> RawCompletePhysicalFamilyChain S -> ℝ
  | [], _ => 0
  | p :: S, .cons _ _ family _ tail =>
      rawCompletePhysicalForcing owner lambda p S family tail.family sourceBasis +
        rawCompletePhysicalForcingChain owner lambda sourceBasis tail

/-- A concrete compatible finite-family chain turns the raw completed physical
trace into its exact signed cumulative forcing ledger. This is a finite
telescoping identity; it deliberately supplies no norm or sign estimate. -/
theorem rawCompletePhysicalHermitianTrace_eq_forcingChain
    {rho iota kappa tau iotaR kappaR tauR nu mu sigma : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
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
    (pairedBoundaryBasis : HilbertBasis sigma ℂ (actualBandPairCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    {S : List CCM24VisiblePrime} (chain : RawCompletePhysicalFamilyChain S) :
    rawCompletePhysicalHermitianTrace owner lambda chain.family a c hac hsupp
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis sourceBasis hfactor =
      rawCompletePhysicalForcingChain owner lambda sourceBasis chain := by
  induction chain with
  | nil family hvisible =>
      simpa [RawCompletePhysicalFamilyChain.family,
        rawCompletePhysicalForcingChain] using
        (rawCompletePhysicalHermitianTrace_eq_zero_of_visiblePrimes_nil
          owner lambda family hvisible a c hac hsupp
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
          rawCompletePhysicalHermitianTrace_cons_eq_add_forcing owner lambda p S
            family tail.family hvisible tail.family_visiblePrimes a c hac hsupp
            negativeBasis positiveBasis outputBasis reflectedNegativeBasis
            reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
            pairedBoundaryBasis sourceBasis hfactor
        _ = rawCompletePhysicalForcing owner lambda p S family tail.family
              sourceBasis + rawCompletePhysicalForcingChain owner lambda
                sourceBasis tail := by
          rw [ih]
          ring
        _ = rawCompletePhysicalForcingChain owner lambda sourceBasis
              (.cons p S family hvisible tail) := rfl

end CCM24FiniteSCausalMarkovRawCumulativeLedger
end CCM25Concrete
end Source
end ConnesWeilRH
