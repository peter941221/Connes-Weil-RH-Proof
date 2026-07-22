/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRootCompletedDetectorRenewalRootPairing
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedQuotientContractionBound

/-!
# A finite-family-uniform bound for the completed detector trace

Proof 476 forms the complete finite-Euler corner before expanding its causal
renewal law.  This module uses that ordering to remove the visible finite
prime family from the first quantitative bound: the band projection, Sonin
projection, and normalized finite-Euler inverse are all contractions, so the
completed trace is controlled by the two fixed energies of the original
three-branch physical pair.

The fixed physical energies still have to be bounded by the required
support--Sobolev polynomial.  No renewal sums are exchanged here.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSRootCompletedDetectorUniformTrace

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSProjectionTrace
open CCM24FiniteSInverseMetric
open CCM24FiniteSBandTrace
open CCM24FiniteSFixedQuotientCarrier
open CCM24FiniteSFixedQuotientContractionBound
open CCM24FiniteSCommonBoundaryPair
open CCM24SourceProlateTrace
open CCM24FiniteSRootCompletedFirstJet
open CCM24FiniteSRootCompletedDetectorRenewalRootPairing

set_option maxHeartbeats 800000 in
-- The nested concrete pair type makes elaboration exceed the project default.
/-- The complete finite-Euler trace is bounded by one fixed geometric energy,
independently of the visible finite prime family.  The absolute value is taken
only after the complete three-branch trace product has been formed. -/
theorem sourceRootCompletedFiniteEulerTrace_norm_le_fixedPhysicalGeometricEnergy
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν μ : Type*}
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
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    let fixedPair := sourceThreeBranchPairData owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
    ‖ordinaryTraceAlong globalBasis
        (sourceRootCompletedFixedQuotientCorner owner lambda
          (radialSupportProjection lambda ∘L
            normalizedFiniteEulerInverse family ∘L
            radialSupportProjection lambda))‖ ≤
      Real.sqrt (∑' i, ‖fixedPair.left (globalBasis i)‖ ^ 2) *
        Real.sqrt (∑' i, ‖fixedPair.right (globalBasis i)‖ ^ 2) := by
  dsimp only
  let fixedPair := sourceThreeBranchPairData owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
  let rightBounded := sourceSoninProjection lambda ∘L
    normalizedFiniteEulerInverse family ∘L sourceBandProjection lambda
  have hBand : ‖sourceBandProjection lambda‖ ≤ 1 :=
    IsStarProjection.norm_le _ (sourceBandProjection_isStarProjection lambda)
  have hSonin : ‖sourceSoninProjection lambda‖ ≤ 1 :=
    IsStarProjection.norm_le _ (sourceSoninProjection_isStarProjection lambda)
  have hInverse : ‖normalizedFiniteEulerInverse family‖ ≤ 1 :=
    norm_normalizedFiniteEulerInverse_le_one family
  have hSoninInverse :
      ‖sourceSoninProjection lambda ∘L
          normalizedFiniteEulerInverse family‖ ≤ 1 := by
    calc
      _ ≤ ‖sourceSoninProjection lambda‖ *
          ‖normalizedFiniteEulerInverse family‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul hSonin hInverse (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul _
  have hRightBounded : ‖rightBounded‖ ≤ 1 := by
    dsimp only [rightBounded]
    calc
      _ ≤ ‖sourceSoninProjection lambda ∘L
            normalizedFiniteEulerInverse family‖ *
          ‖sourceBandProjection lambda‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 :=
        mul_le_mul hSoninInverse hBand (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul _
  have hLeftEnergy := boundedSandwich_left_tsum_le_of_norm_le_one
    boundaryBasis fixedPair (sourceBandProjection lambda) rightBounded hBand
  have hRightEnergy := boundedSandwich_right_tsum_le_of_norm_le_one
    boundaryBasis fixedPair (sourceBandProjection lambda) rightBounded
      hRightBounded
  have hPairLeft :
      (∑' i, ‖(sourceRootCompletedFiniteEulerPairData owner lambda family a c
        hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis boundaryBasis hfactor).left (globalBasis i)‖ ^ 2) ≤
        ∑' i, ‖fixedPair.left (globalBasis i)‖ ^ 2 := by
    simpa only [sourceRootCompletedFiniteEulerPairData,
      CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.smulRight,
      rightBounded, fixedPair] using hLeftEnergy
  have hPairRight :
      (∑' i, ‖(sourceRootCompletedFiniteEulerPairData owner lambda family a c
        hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis boundaryBasis hfactor).right (globalBasis i)‖ ^ 2) ≤
        ∑' i, ‖fixedPair.right (globalBasis i)‖ ^ 2 := by
    simpa only [sourceRootCompletedFiniteEulerPairData,
      CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.smulRight,
      ContinuousLinearMap.smul_apply, norm_smul, norm_neg, norm_one, one_mul,
      mul_pow,
      rightBounded,
      fixedPair] using hRightEnergy
  rw [← sourceRootCompletedFiniteEulerPairData_traceProduct_eq owner lambda
    family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis hfactor]
  exact
    (ordinaryTraceAlong_traceProduct_norm_le_geometricEnergy
      (sourceRootCompletedFiniteEulerPairData owner lambda family a c hac
        hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
        hfactor)).trans
      (mul_le_mul (Real.sqrt_le_sqrt hPairLeft)
        (Real.sqrt_le_sqrt hPairRight) (Real.sqrt_nonneg _)
        (Real.sqrt_nonneg _))

end CCM24FiniteSRootCompletedDetectorUniformTrace
end CCM25Concrete
end Source
end ConnesWeilRH
