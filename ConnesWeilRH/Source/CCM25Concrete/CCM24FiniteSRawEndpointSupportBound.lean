/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSNormalizedEndpointSupportBound
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSSourceFirstJetSupportBound
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCanonicalCompletedResponse

/-!
# Raw endpoint and quadratic-remainder support bounds

The normalized endpoint estimate can be converted back to the raw endpoint
only by paying the inverse square of the finite Euler lower factor.  This
module records that conversion exactly, combines it with the actual paired
first-jet estimate, and specializes the resulting quadratic-remainder bound
to the canonical selected family.

The bound is unconditional for every fixed finite family, but it is not
uniform in that family.  The explicit inverse lower-factor cost is precisely
the cancellation which Gate 3U still has to remove on the complete signed
raw response.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSRawEndpointSupportBound

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSBandTrace
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSActualBandSourceRemainder
open CCM24FiniteSNormalizedPhysicalResponse
open CCM24FiniteSNormalizedEndpointSupportBound
open CCM24FiniteSSourceFirstJetSupportBound
open CCM24FiniteSCanonicalCompletedResponse
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-- The raw endpoint trace is exactly the normalized endpoint trace divided
by the square of the positive finite Euler lower factor. -/
theorem sourceBandGramTrace_eq_inv_lowerFactorSq_mul_normalizedTrace
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
    ordinaryTraceAlong sourceBasis (sourceBandGramResponse owner lambda family) =
      (((finiteEulerLowerFactor family.visiblePrimes : ℂ) ^ 2)⁻¹) *
        ordinaryTraceAlong sourceBasis
          (normalizedSourceBandGramResponse owner lambda family) := by
  have hclass := sourceBandGramResponse_isTraceClassAlong owner lambda family
    a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor
  have htrace := ordinaryTraceAlong_smul sourceBasis
    ((finiteEulerLowerFactor family.visiblePrimes : ℂ) ^ 2)
    (sourceBandGramResponse owner lambda family) hclass
  rw [← normalizedSourceBandGramResponse] at htrace
  have hlower : (finiteEulerLowerFactor family.visiblePrimes : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (ne_of_gt (finiteEulerLowerFactor_pos family.visiblePrimes))
  have hlowerSq :
      (finiteEulerLowerFactor family.visiblePrimes : ℂ) ^ 2 ≠ 0 :=
    pow_ne_zero 2 hlower
  rw [htrace]
  calc
    ordinaryTraceAlong sourceBasis (sourceBandGramResponse owner lambda family) =
        1 * ordinaryTraceAlong sourceBasis
          (sourceBandGramResponse owner lambda family) := by ring
    _ = (((finiteEulerLowerFactor family.visiblePrimes : ℂ) ^ 2)⁻¹ *
          (finiteEulerLowerFactor family.visiblePrimes : ℂ) ^ 2) *
        ordinaryTraceAlong sourceBasis
          (sourceBandGramResponse owner lambda family) := by
      rw [inv_mul_cancel₀ hlowerSq]
    _ = (((finiteEulerLowerFactor family.visiblePrimes : ℂ) ^ 2)⁻¹) *
        ((finiteEulerLowerFactor family.visiblePrimes : ℂ) ^ 2 *
          ordinaryTraceAlong sourceBasis
            (sourceBandGramResponse owner lambda family)) := by ring

/-- The raw endpoint inherits the normalized support estimate with the exact
inverse lower-factor-square cost exposed. -/
theorem sourceBandGramTrace_norm_le_invLowerFactorSq_supportEnergy
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
    ‖ordinaryTraceAlong sourceBasis
        (sourceBandGramResponse owner lambda family)‖ ≤
      ((finiteEulerLowerFactor family.visiblePrimes) ^ 2)⁻¹ *
        (6 + 2 * (∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
          (globalBasis i)‖ ^ 2)) *
        ((c - a) ^ 2 *
          SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) := by
  rw [sourceBandGramTrace_eq_inv_lowerFactorSq_mul_normalizedTrace owner lambda
    family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor]
  have hlower : 0 < finiteEulerLowerFactor family.visiblePrimes :=
    finiteEulerLowerFactor_pos family.visiblePrimes
  have hnormalized := normalizedSourceBandGramTrace_norm_le_supportEnergy
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hlower]
  simpa only [mul_assoc] using
    (mul_le_mul_of_nonneg_left hnormalized
      (inv_nonneg.mpr (sq_nonneg (finiteEulerLowerFactor family.visiblePrimes))))

set_option maxHeartbeats 2000000 in
-- The source subtraction uses the actual first-jet and raw endpoint
-- trace-class owners; the inverse lower factor is introduced only afterward.
/-- The actual quadratic remainder has a fixed-family support bound.  Its
only nonuniform term is the explicit inverse Euler lower-factor square. -/
theorem sourceActualBandFiniteEulerRemainderTrace_norm_le_invLowerFactorSq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ σ ρ : Type*}
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
    (pairedBoundaryBasis : HilbertBasis σ ℂ (actualBandPairCarrier a c))
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    ‖ordinaryTraceAlong sourceBasis
        (sourceActualBandFiniteEulerRemainderResponse owner lambda family)‖ ≤
      ((12 + 4 * (∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
          (globalBasis i)‖ ^ 2)) +
        ((finiteEulerLowerFactor family.visiblePrimes) ^ 2)⁻¹ *
          (6 + 2 * (∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
            (globalBasis i)‖ ^ 2))) *
        ((c - a) ^ 2 *
          SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) := by
  let first := sourceActualBandFiniteEulerSoninResponse owner lambda family
  let endpoint := sourceBandGramResponse owner lambda family
  let P := (c - a) ^ 2 *
    SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2
  let H := ∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
    (globalBasis i)‖ ^ 2
  let lowerInv := ((finiteEulerLowerFactor family.visiblePrimes) ^ 2)⁻¹
  have hfirstClass := sourceActualBandFiniteEulerSoninResponse_isTraceClassAlong
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor
  have hendpointClass := sourceBandGramResponse_isTraceClassAlong owner lambda
    family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor
  have htrace :
      ordinaryTraceAlong sourceBasis
          (sourceActualBandFiniteEulerRemainderResponse owner lambda family) =
        ordinaryTraceAlong sourceBasis first -
          ordinaryTraceAlong sourceBasis endpoint := by
    rw [sourceActualBandFiniteEulerRemainderResponse]
    exact ordinaryTraceAlong_sub sourceBasis first endpoint
      hfirstClass hendpointClass
  have hfirst := sourceActualBandFiniteEulerSoninTrace_norm_le_supportEnergy
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor
  have hendpoint :=
    sourceBandGramTrace_norm_le_invLowerFactorSq_supportEnergy owner lambda
      family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor
  rw [htrace]
  calc
    _ ≤ ‖ordinaryTraceAlong sourceBasis first‖ +
        ‖ordinaryTraceAlong sourceBasis endpoint‖ := norm_sub_le _ _
    _ ≤ (12 + 4 * H) * P + lowerInv * (6 + 2 * H) * P := by
      exact add_le_add (by simpa only [first, P, H] using hfirst)
        (by simpa only [endpoint, P, H, lowerInv] using hendpoint)
    _ = ((12 + 4 * H) + lowerInv * (6 + 2 * H)) * P := by ring
    _ = ((12 + 4 * (∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
          (globalBasis i)‖ ^ 2)) +
        ((finiteEulerLowerFactor family.visiblePrimes) ^ 2)⁻¹ *
          (6 + 2 * (∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
            (globalBasis i)‖ ^ 2))) *
        ((c - a) ^ 2 *
          SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) := by
      rfl

/-- Canonical endpoint assembly: the completed canonical response inherits
the fixed-family quadratic-remainder bound on the exact selected family. -/
theorem canonicalCompletedResponseTrace_norm_le_invLowerFactorSq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ σ ρ : Type*}
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
    (pairedBoundaryBasis : HilbertBasis σ ℂ (actualBandPairCarrier a c))
    (sourceBasis : HilbertBasis ρ ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    ‖ordinaryTraceAlong sourceBasis
        (canonicalActualBandCompletedRelativeResponse owner lambda)‖ ≤
      ((12 + 4 * (∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
          (globalBasis i)‖ ^ 2)) +
        ((finiteEulerLowerFactor (canonicalFamily owner).visiblePrimes) ^ 2)⁻¹ *
          (6 + 2 * (∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
            (globalBasis i)‖ ^ 2))) *
        ((c - a) ^ 2 *
          SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) := by
  rw [← canonicalSourceRemainder_eq_canonicalCompletedResponse owner lambda]
  exact sourceActualBandFiniteEulerRemainderTrace_norm_le_invLowerFactorSq
    owner lambda (canonicalFamily owner) a c hac hsupp negativeBasis
    positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
    reflectedOutputBasis globalBasis boundaryBasis pairedBoundaryBasis
    sourceBasis hfactor

end CCM24FiniteSRawEndpointSupportBound
end CCM25Concrete
end Source
end ConnesWeilRH
