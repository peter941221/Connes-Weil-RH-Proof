/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCausalMarkovCompletedPhysicalDifference
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSGatePhysicalLowerFactorPersistence
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSNormalizedEndpointSupportBound

/-!
# Support bound for the scaled completed Markov forcing

The one-prime completed forcing is the difference of the normalized physical
endpoints after the new lower-factor square is retained.  This module moves
the existing compact-root support estimate to that exact forcing scalar.

The bound is deliberately for the lower-factor-square scaled forcing.  It
does not bound the raw forcing, and therefore does not prove Gate 3U.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSCausalMarkovCompletedForcingSupportBound

open MeasureTheory
open scoped BigOperators InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.CompactRootHalfLinePair
open CC20Concrete.PositiveTrace
open CCM24FiniteSActualBandSourceRemainder
open CCM24FiniteSBandTrace
open CCM24FiniteSCanonicalRealGate
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSCausalMarkovCompletedFirstDifference
open CCM24FiniteSCausalMarkovCompletedPhysicalDifference
open CCM24FiniteSGatePhysicalLowerFactorPersistence
open CCM24FiniteSGramResponse
open CCM24FiniteSNormalizedEndpointSupportBound
open CCM24FiniteSNormalizedPhysicalResponse
open CCM24FiniteSProjectionTrace
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The lower-factor-square completed physical trace is exactly the negative
real normalized source-band trace.  The completed physical kernel remains
one object throughout this readback. -/
theorem normalizedCompletePhysicalHermitianTrace_eq_neg_normalizedSourceBandGramTrace_re
    {rho iota kappa tau iotaR kappaR tauR nu mu : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
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
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    normalizedCompletePhysicalHermitianTrace owner lambda family a c hac hsupp
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis sourceBasis hfactor =
      -(ordinaryTraceAlong sourceBasis
        (normalizedSourceBandGramResponse owner lambda family)).re := by
  unfold normalizedCompletePhysicalHermitianTrace
  rw [completePhysicalHermitianTrace_eq_neg_sourceBandGramRealTrace owner lambda
    family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor]
  simp only [Complex.neg_re, Complex.ofReal_re]
  rw [normalizedSourceBandGramRealTrace_eq_lowerFactorSq_mul_raw owner lambda
    family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor]
  ring

/-- Compact root support bounds the lower-factor-square completed physical
trace uniformly in the finite family.  This is an endpoint bound, not the
lower-factor-square decay required by the raw Gate 3U contract. -/
theorem abs_normalizedCompletePhysicalHermitianTrace_le_supportEnergy
    {rho iota kappa tau iotaR kappaR tauR nu mu : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
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
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    |normalizedCompletePhysicalHermitianTrace owner lambda family a c hac hsupp
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis sourceBasis hfactor| <=
      (6 + 2 * (∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
          (globalBasis i)‖ ^ 2)) *
        ((c - a) ^ 2 * SchwartzMap.seminorm Complex 0 0 owner.sourceTest.test ^ 2) := by
  rw [normalizedCompletePhysicalHermitianTrace_eq_neg_normalizedSourceBandGramTrace_re
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor, abs_neg]
  exact (Complex.abs_re_le_norm _).trans
    (normalizedSourceBandGramTrace_norm_le_supportEnergy owner lambda family
      a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor)

set_option maxHeartbeats 2000000 in
-- Combining the recurrence with two completed physical endpoint bounds is elaboration intensive.
/-- The exact completed Markov/remainder forcing has a support-first bound
after multiplication by the new lower-factor square.  The two forcing terms
are not estimated separately: the proof first rewrites their sum as a
difference of two complete Hardy--prolate endpoints. -/
theorem lowerFactorSq_completePhysicalForcing_abs_le_supportEnergy
    {rho iota kappa tau iotaR kappaR tauR nu mu sigma : Type*}
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (p : CCM24VisiblePrime)
    (S : List CCM24VisiblePrime) (newFamily oldFamily : FinitePrimePowerFamily)
    (hnew : newFamily.visiblePrimes = p :: S)
    (hold : oldFamily.visiblePrimes = S)
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
    |(finiteEulerLowerFactor newFamily.visiblePrimes) ^ 2 *
        (-(ordinaryTraceAlong sourceBasis
          (normalizedListActualBandSoninCoboundary owner lambda p S)).re +
          (ordinaryTraceAlong sourceBasis
            (sourceActualBandFiniteEulerRemainderIncrement owner lambda
              newFamily oldFamily)).re)| <=
      (1 + (1 - ccm24PrimeEulerCoefficient p) ^ 2) *
        ((6 + 2 * (∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
            (globalBasis i)‖ ^ 2)) *
          ((c - a) ^ 2 * SchwartzMap.seminorm Complex 0 0 owner.sourceTest.test ^ 2)) := by
  let newTrace := normalizedCompletePhysicalHermitianTrace owner lambda newFamily
    a c hac hsupp reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis sourceBasis hfactor
  let oldTrace := normalizedCompletePhysicalHermitianTrace owner lambda oldFamily
    a c hac hsupp reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis sourceBasis hfactor
  let forcing :=
    -(ordinaryTraceAlong sourceBasis
      (normalizedListActualBandSoninCoboundary owner lambda p S)).re +
      (ordinaryTraceAlong sourceBasis
        (sourceActualBandFiniteEulerRemainderIncrement owner lambda
          newFamily oldFamily)).re
  let energy :=
    (6 + 2 * (∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
        (globalBasis i)‖ ^ 2)) *
      ((c - a) ^ 2 * SchwartzMap.seminorm Complex 0 0 owner.sourceTest.test ^ 2)
  have hrec : newTrace = (1 - ccm24PrimeEulerCoefficient p) ^ 2 * oldTrace +
      (finiteEulerLowerFactor newFamily.visiblePrimes) ^ 2 * forcing := by
    simpa only [newTrace, oldTrace, forcing] using
      (normalizedCompletePhysicalHermitianTrace_cons_eq_contract_add_forcing
        owner lambda p S newFamily oldFamily hnew hold a c hac hsupp
        negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
        pairedBoundaryBasis sourceBasis hfactor)
  have hforcing : (finiteEulerLowerFactor newFamily.visiblePrimes) ^ 2 *
      forcing = newTrace - (1 - ccm24PrimeEulerCoefficient p) ^ 2 * oldTrace := by
    linarith
  have hnewTrace : |newTrace| <= energy := by
    dsimp only [newTrace, energy]
    exact abs_normalizedCompletePhysicalHermitianTrace_le_supportEnergy
      owner lambda newFamily a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor
  have holdTrace : |oldTrace| <= energy := by
    dsimp only [oldTrace, energy]
    exact abs_normalizedCompletePhysicalHermitianTrace_le_supportEnergy
      owner lambda oldFamily a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor
  have hprimeContractionSq :
      0 <= (1 - ccm24PrimeEulerCoefficient p) ^ 2 := sq_nonneg _
  change |(finiteEulerLowerFactor newFamily.visiblePrimes) ^ 2 * forcing| <=
    (1 + (1 - ccm24PrimeEulerCoefficient p) ^ 2) * energy
  rw [hforcing]
  calc
    |newTrace - (1 - ccm24PrimeEulerCoefficient p) ^ 2 * oldTrace| <=
        |newTrace| + |(1 - ccm24PrimeEulerCoefficient p) ^ 2 * oldTrace| :=
      abs_sub _ _
    _ = |newTrace| + (1 - ccm24PrimeEulerCoefficient p) ^ 2 * |oldTrace| := by
      rw [abs_mul, abs_of_nonneg hprimeContractionSq]
    _ <= energy + (1 - ccm24PrimeEulerCoefficient p) ^ 2 * energy := by
      exact add_le_add hnewTrace
        (mul_le_mul_of_nonneg_left holdTrace hprimeContractionSq)
    _ = (1 + (1 - ccm24PrimeEulerCoefficient p) ^ 2) * energy := by ring

end CCM24FiniteSCausalMarkovCompletedForcingSupportBound
end CCM25Concrete
end Source
end ConnesWeilRH
