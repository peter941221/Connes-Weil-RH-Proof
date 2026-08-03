/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCausalMarkovCompletedPhysicalDifference
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSEmptyPhysicalReadout
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalObliqueShearKernelReduction

/-!
# Raw base ledger for the finite-S completed physical trace

The lower-factor-square normalization is useful for the Markov contraction,
but the support-polynomial Gate concerns the raw completed physical scalar.
This module supplies its exact zero-prime base point and its unscaled
one-prime increment.  It does not estimate the increment.

Consequently, any valid raw Gate 3U argument must control the signed sum of
the same recombined Markov/remainder forcings.  It cannot obtain a bound by
dividing an estimate for the normalized recurrence by the lower factor.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCausalMarkovRawBase

open MeasureTheory
open scoped BigOperators InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSActualBandSourceRemainder
open CCM24FiniteSBandTrace
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSCausalMarkovCompletedPhysicalDifference
open CCM24FiniteSCausalMarkovCompletedFirstDifference
open CCM24FiniteSCoframeResponse
open CCM24FiniteSEmptyPhysicalReadout
open CCM24FiniteSGramResponse
open CCM24FiniteSGramOrderingBridge
open CCM24FiniteSPhysicalLeakage
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGatePhysicalObliqueShearKernelReduction
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The raw real scalar that Proof 788 identifies with the unnormalized
completed physical Gate trace. -/
noncomputable def rawCompletePhysicalHermitianTrace
    {rho ιr κr taur nu : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis taur ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis nu ℂ finiteSCarrier)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) : ℝ :=
  (completePhysicalHermitianTrace owner lambda family a c hac hsupp
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis sourceBasis hfactor).re

/-- The literal raw forcing from the one-prime completed physical ledger.
Both terms belong to the same signed source trace and must remain recombined
until compact root support has acted. -/
noncomputable def rawCompletePhysicalForcing
    {rho : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime)
    (newFamily oldFamily : FinitePrimePowerFamily)
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda)) : ℝ :=
  -(ordinaryTraceAlong sourceBasis
      (normalizedListActualBandSoninCoboundary owner lambda p S)).re +
    (ordinaryTraceAlong sourceBasis
      (sourceActualBandFiniteEulerRemainderIncrement owner lambda
        newFamily oldFamily)).re

/-- With no visible finite place, the actual three-branch physical leakage is
zero on the source carrier. -/
theorem sourcePhysicalCoframeLeakage_eq_zero_of_visiblePrimes_nil
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (hvisible : family.visiblePrimes = []) :
    sourcePhysicalCoframeLeakage lambda family = 0 := by
  rw [← sourceSoninCoframeLeakage_eq_physical,
    sourceSoninCoframeLeakage_eq_coframe_sub_inclusion,
    finiteEulerMetricCoframe_eq_sourceInclusion_of_visiblePrimes_nil
      lambda family hvisible,
    sub_self]

/-- The actual finite-S target has no zero-prime offset.  This is an operator
identity, before a trace, norm, or support estimate is considered. -/
theorem finiteEulerTargetCommutatorResponse_eq_zero_of_visiblePrimes_nil
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (hvisible : family.visiblePrimes = []) :
    finiteEulerTargetCommutatorResponse owner lambda family = 0 := by
  rw [finiteEulerTargetCommutatorResponse_eq_physicalCoframeLeakage,
    finiteEulerPhysicalCoframeLeakageResponse,
    sourcePhysicalCoframeLeakage_eq_zero_of_visiblePrimes_nil
      lambda family hvisible]
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℂ
  intro v
  simp only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply]
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp

/-- The raw completed physical scalar has the same zero-prime base point.
This removes a possible hidden constant from the raw forcing ledger. -/
theorem rawCompletePhysicalHermitianTrace_eq_zero_of_visiblePrimes_nil
    {rho ι κ tau ιr κr taur nu mu : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (hvisible : family.visiblePrimes = [])
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
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    rawCompletePhysicalHermitianTrace owner lambda family a c hac hsupp
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis sourceBasis hfactor = 0 := by
  have hresponse : sourceBandGramResponse owner lambda family = 0 := by
    rw [sourceBandGramResponse_eq_neg_physical_leakage,
      sourcePhysicalCoframeLeakage_eq_zero_of_visiblePrimes_nil
        lambda family hvisible]
    simp
  unfold rawCompletePhysicalHermitianTrace
  rw [completePhysicalHermitianTrace_eq_neg_sourceBandGramRealTrace owner lambda
    family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor, hresponse]
  unfold ordinaryTraceAlong
  simp

/-- The raw completed physical trace evolves by the literal unscaled forcing.
This is the same source-complete Markov/remainder difference as Proof 793,
with no lower factor introduced or divided out. -/
theorem rawCompletePhysicalHermitianTrace_cons_eq_add_forcing
    {rho ι κ tau ιr κr taur nu mu sigma : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (newFamily oldFamily : FinitePrimePowerFamily)
    (hnew : newFamily.visiblePrimes = p :: S)
    (hold : oldFamily.visiblePrimes = S)
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
  have hledger :=
    completePhysicalHermitianTrace_re_sub_eq_neg_coboundary_re_add_remainder
      owner lambda p S newFamily oldFamily hnew hold a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      pairedBoundaryBasis sourceBasis hfactor
  unfold rawCompletePhysicalHermitianTrace rawCompletePhysicalForcing
  linarith

end CCM24FiniteSCausalMarkovRawBase
end CCM25Concrete
end Source
end ConnesWeilRH
