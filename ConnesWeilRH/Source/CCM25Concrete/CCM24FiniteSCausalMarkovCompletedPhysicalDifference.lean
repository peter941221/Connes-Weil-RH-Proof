/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCausalMarkovCompletedTraceDifference
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalHardyProlateCompletedHermitianTrace

/-!
# Physical one-prime difference of the completed Hardy--prolate trace

The Gate-facing physical scalar is the completed Hardy--prolate Hermitian
trace. This module gives its exact one-prime difference before an absolute
value is taken. The difference is the negative real Markov coboundary trace
plus the real completed-remainder increment.

This identifies the only possible location of the extra half-power
cancellation. It asserts no bound, sign, or Gate 3U conclusion.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCausalMarkovCompletedPhysicalDifference

open MeasureTheory
open scoped BigOperators InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSActualBandSourceRemainder
open CCM24FiniteSBandTrace
open CCM24FiniteSCanonicalRealGate
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSGramResponse
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGatePhysicalCanonicalCompletedKernelTraceLegality
open CCM24FiniteSGatePhysicalHardyProlateCompletedBoundaryKernel
open CCM24FiniteSGatePhysicalHardyProlateCompletedHermitianTrace
open CCM24FiniteSGatePhysicalTargetHermitianPrefix
open CCM24FiniteSCausalMarkovCompletedFirstDifference
open CCM24FiniteSCausalMarkovCompletedTraceDifference
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The exact completed Hardy--prolate Hermitian scalar used by the physical
Gate readout. Its summands remain recombined before their real part is taken. -/
noncomputable def completePhysicalHermitianTrace
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
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) : ℂ :=
  ∑' i, ((finiteEulerCausalHardyProlateCompletePhysicalBoundaryPairing
    owner lambda family a c hac hsupp reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
    (sourceBasis i) (sourceBasis i)).re : ℂ)

/-- The completed physical Hermitian trace is the negative real raw endpoint
trace. This is an exact readback, not a norm estimate. -/
theorem completePhysicalHermitianTrace_eq_neg_sourceBandGramRealTrace
    {rho ι κ tau ιr κr taur nu mu : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
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
    completePhysicalHermitianTrace owner lambda family a c hac hsupp
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis sourceBasis hfactor =
      -((ordinaryTraceAlong sourceBasis
        (sourceBandGramResponse owner lambda family)).re : ℂ) := by
  have hcomplete :=
    ordinaryTraceAlong_targetHermitianResponse_eq_completePhysicalBoundaryPairing_re
      owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis sourceBasis hfactor
  have htargetClass :=
    finiteEulerTargetCommutatorResponse_isTraceClassAlong_completedKernel
      owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor
  have hhermitian := ordinaryTraceAlong_targetHermitianResponse_eq_target_re
    owner lambda family sourceBasis htargetClass
  unfold completePhysicalHermitianTrace
  rw [← hcomplete, hhermitian,
    ordinaryTraceAlong_targetCommutator_re_eq_neg_sourceBand_re owner lambda
      family sourceBasis, Complex.ofReal_neg]

set_option maxHeartbeats 1200000 in
-- This declaration combines two full physical trace readbacks before linarith.
/-- The literal completed physical trace has the same one-prime cancellation
ledger as the actual source endpoint. The two summands on the right must stay
coupled until compact root support has been used. -/
theorem completePhysicalHermitianTrace_re_sub_eq_neg_coboundary_re_add_remainder
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
    (completePhysicalHermitianTrace owner lambda newFamily a c hac hsupp
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis sourceBasis hfactor).re -
      (completePhysicalHermitianTrace owner lambda oldFamily a c hac hsupp
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis sourceBasis hfactor).re =
      -(ordinaryTraceAlong sourceBasis
        (normalizedListActualBandSoninCoboundary owner lambda p S)).re +
        (ordinaryTraceAlong sourceBasis
          (sourceActualBandFiniteEulerRemainderIncrement owner lambda
            newFamily oldFamily)).re := by
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
    ordinaryTraceAlong_sourceBandGramIncrement_eq_coboundary_sub_remainder
      owner lambda p S newFamily oldFamily hnew hold a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      pairedBoundaryBasis sourceBasis hfactor
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
  rw [hphysicalNewRe, hphysicalOldRe]
  linarith

/-- The lower-factor-square normalization of the physical Hermitian trace.
This is the scalar which Proof 788 identifies with the normalized Gate
readout, up to the fixed sign. -/
noncomputable def normalizedCompletePhysicalHermitianTrace
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
  (finiteEulerLowerFactor family.visiblePrimes) ^ 2 *
    (completePhysicalHermitianTrace owner lambda family a c hac hsupp
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis sourceBasis hfactor).re

set_option maxHeartbeats 1200000 in
-- The normalized recurrence expands two completed physical traces and one
-- trace-legal forcing term on the same source basis.
/-- Exact stable recurrence for the lower-factor-square completed physical
trace. The forcing term is still the recombined Markov/remainder difference. -/
theorem normalizedCompletePhysicalHermitianTrace_cons_eq_contract_add_forcing
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
    normalizedCompletePhysicalHermitianTrace owner lambda newFamily a c hac hsupp
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis sourceBasis hfactor =
      (1 - ccm24PrimeEulerCoefficient p) ^ 2 *
        normalizedCompletePhysicalHermitianTrace owner lambda oldFamily a c hac
          hsupp reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
          globalBasis sourceBasis hfactor +
        (finiteEulerLowerFactor newFamily.visiblePrimes) ^ 2 *
          (-(ordinaryTraceAlong sourceBasis
            (normalizedListActualBandSoninCoboundary owner lambda p S)).re +
            (ordinaryTraceAlong sourceBasis
              (sourceActualBandFiniteEulerRemainderIncrement owner lambda
                newFamily oldFamily)).re) := by
  let newTrace :=
    (completePhysicalHermitianTrace owner lambda newFamily a c hac hsupp
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis sourceBasis hfactor).re
  let oldTrace :=
    (completePhysicalHermitianTrace owner lambda oldFamily a c hac hsupp
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis sourceBasis hfactor).re
  let forcing :=
    -(ordinaryTraceAlong sourceBasis
      (normalizedListActualBandSoninCoboundary owner lambda p S)).re +
      (ordinaryTraceAlong sourceBasis
        (sourceActualBandFiniteEulerRemainderIncrement owner lambda
          newFamily oldFamily)).re
  have htrace : newTrace - oldTrace = forcing := by
    simpa only [newTrace, oldTrace, forcing] using
      (completePhysicalHermitianTrace_re_sub_eq_neg_coboundary_re_add_remainder
        owner lambda p S newFamily oldFamily hnew hold a c hac hsupp
        negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
        pairedBoundaryBasis sourceBasis hfactor)
  have hnewTrace : newTrace = oldTrace + forcing := by
    linarith
  have hlower : finiteEulerLowerFactor newFamily.visiblePrimes =
      (1 - ccm24PrimeEulerCoefficient p) *
        finiteEulerLowerFactor oldFamily.visiblePrimes := by
    rw [hnew, hold]
    rfl
  change (finiteEulerLowerFactor newFamily.visiblePrimes) ^ 2 * newTrace =
    (1 - ccm24PrimeEulerCoefficient p) ^ 2 *
      ((finiteEulerLowerFactor oldFamily.visiblePrimes) ^ 2 * oldTrace) +
    (finiteEulerLowerFactor newFamily.visiblePrimes) ^ 2 * forcing
  rw [hnewTrace, hlower]
  ring

end CCM24FiniteSCausalMarkovCompletedPhysicalDifference
end CCM25Concrete
end Source
end ConnesWeilRH
