/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCanonicalRealGate
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRawEndpointSupportBound

/-!
# Lower-factor persistence at the raw Gate 3U endpoint

The normalized source-band response is the raw response multiplied by the
square of the finite Euler lower factor.  This module records the corresponding
real-trace identity and its exact Gate consequence: a raw Gate bound by `B`
is equivalent to a normalized real trace bound by `lowerFactor^2 * B`.

Thus a family-uniform bound for the normalized trace alone does not close the
raw Gate.  The missing producer must supply the matching lower-factor-square
decay while retaining the completed physical cancellation.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSGatePhysicalLowerFactorPersistence

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSCanonicalCompletedResponse
open CCM24FiniteSCanonicalRealGate
open CCM24FiniteSBandTrace
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSGramResponse
open CCM24FiniteSNormalizedPhysicalResponse
open CCM24FiniteSProjectionTrace
open CCM24FiniteSRawEndpointSupportBound
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- Taking real parts of the exact raw/normalized trace identity exposes the
positive lower-factor square without any estimate. -/
theorem normalizedSourceBandGramRealTrace_eq_lowerFactorSq_mul_raw
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ ρ : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (ordinaryTraceAlong sourceBasis
        (normalizedSourceBandGramResponse owner lambda family)).re =
      (finiteEulerLowerFactor family.visiblePrimes) ^ 2 *
        (ordinaryTraceAlong sourceBasis
          (sourceBandGramResponse owner lambda family)).re := by
  have hraw := sourceBandGramTrace_eq_inv_lowerFactorSq_mul_normalizedTrace
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor
  have hlower : (finiteEulerLowerFactor family.visiblePrimes : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (ne_of_gt (finiteEulerLowerFactor_pos family.visiblePrimes))
  have hnormal :
      ordinaryTraceAlong sourceBasis
          (normalizedSourceBandGramResponse owner lambda family) =
        (finiteEulerLowerFactor family.visiblePrimes : ℂ) ^ 2 *
          ordinaryTraceAlong sourceBasis
            (sourceBandGramResponse owner lambda family) := by
    calc
      ordinaryTraceAlong sourceBasis
          (normalizedSourceBandGramResponse owner lambda family) =
          (finiteEulerLowerFactor family.visiblePrimes : ℂ) ^ 2 *
            (((finiteEulerLowerFactor family.visiblePrimes : ℂ) ^ 2)⁻¹ *
              ordinaryTraceAlong sourceBasis
                (normalizedSourceBandGramResponse owner lambda family)) := by
          rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hlower), one_mul]
      _ = (finiteEulerLowerFactor family.visiblePrimes : ℂ) ^ 2 *
          ordinaryTraceAlong sourceBasis
            (sourceBandGramResponse owner lambda family) := by
          rw [hraw]
  have hnormalRe := congrArg Complex.re hnormal
  have hscalarRe :
      ((finiteEulerLowerFactor family.visiblePrimes : ℂ) ^ 2).re =
        (finiteEulerLowerFactor family.visiblePrimes) ^ 2 := by
    simp [pow_two]
  have hscalarIm :
      ((finiteEulerLowerFactor family.visiblePrimes : ℂ) ^ 2).im = 0 := by
    simp [pow_two]
  rw [Complex.mul_re, hscalarRe, hscalarIm, zero_mul, sub_zero] at hnormalRe
  exact hnormalRe

/-- The raw real source-band bound is equivalent to lower-factor-square decay
of the normalized real trace.  This is the exact missing Gate 3U producer
contract; a merely uniform normalized bound is weaker. -/
theorem sourceBandGramRealTrace_bound_iff_normalized_lowerFactorSq_decay
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ ρ : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (bound : ℝ) :
    |(ordinaryTraceAlong sourceBasis
        (sourceBandGramResponse owner lambda family)).re| ≤ bound ↔
      |(ordinaryTraceAlong sourceBasis
        (normalizedSourceBandGramResponse owner lambda family)).re| ≤
        (finiteEulerLowerFactor family.visiblePrimes) ^ 2 * bound := by
  rw [normalizedSourceBandGramRealTrace_eq_lowerFactorSq_mul_raw owner lambda
    family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor]
  have hlowerSq : 0 < (finiteEulerLowerFactor family.visiblePrimes) ^ 2 :=
    sq_pos_of_pos (finiteEulerLowerFactor_pos family.visiblePrimes)
  rw [abs_mul, abs_of_pos hlowerSq]
  exact (mul_le_mul_iff_right₀ hlowerSq).symm

/-- A producer for lower-factor-square normalized trace decay closes the
canonical raw real Gate exactly, without dividing any estimate by the lower
factor. -/
theorem canonicalRealGate3UAt_of_normalizedSourceBandRealTrace_decay
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ ρ : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (reflectedNegativeBasis : HilbertBasis ιr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (reflectedPositiveBasis : HilbertBasis κr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (reflectedOutputBasis : HilbertBasis τr ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (bound : ℝ)
    (hdecay :
      |(ordinaryTraceAlong sourceBasis
        (normalizedSourceBandGramResponse owner lambda
          (canonicalFamily owner))).re| ≤
        (finiteEulerLowerFactor (canonicalFamily owner).visiblePrimes) ^ 2 *
          bound) :
    canonicalRealGate3UAt owner lambda sourceBasis bound := by
  rw [canonicalRealGate3UAt_iff_sourceBandRealBound]
  exact
    (sourceBandGramRealTrace_bound_iff_normalized_lowerFactorSq_decay owner
      lambda (canonicalFamily owner) a c hac hsupp negativeBasis positiveBasis
      outputBasis reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor bound).mpr hdecay

end CCM24FiniteSGatePhysicalLowerFactorPersistence
end CCM25Concrete
end Source
end ConnesWeilRH
