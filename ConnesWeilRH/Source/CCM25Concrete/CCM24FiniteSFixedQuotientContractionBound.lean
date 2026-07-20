/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedQuotientBandConsumer

/-!
# Contraction bound for the fixed-quotient first jet

The normalized finite-Euler inverse and every projection/inclusion surrounding
it are contractions.  This module keeps the complete four-coordinate physical
pair assembled and proves that its Hilbert--Schmidt square energy cannot grow
when it is moved to the genuine quotient-band carrier.

The resulting estimate is uniform in the visible finite family.  It applies
only to the fixed-quotient first-jet owner; it does not identify that owner
with the complete Burnol endpoint response or prove Gate 3U.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSFixedQuotientContractionBound

open MeasureTheory
open CC20Concrete
open scoped InnerProduct InnerProductSpace
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSInverseMetric
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSInputSideTraceConsumer
open CCM24FiniteSFixedQuotientCarrier
open CCM24FiniteSFixedQuotientBandConsumer
open CCM24FiniteSTwoSidedRootRecombination
open CCM24SourceProlateTrace

noncomputable local instance sourceBandCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceBandCarrier lambda) :=
  (sourceBandClosedRange lambda).isClosed.completeSpace_coe

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

theorem boundedPrecomp_left_tsum_le_of_norm_le_one
    {ι κ mu H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (targetBasis : HilbertBasis κ ℂ G)
    (newSourceBasis : HilbertBasis mu ℂ K)
    (data : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis)
    (leftBounded rightBounded : K →L[ℂ] H)
    (hleft : ‖leftBounded‖ ≤ 1) :
    (∑' i, ‖(CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.boundedPrecomp
        targetBasis newSourceBasis data leftBounded rightBounded).left
        (newSourceBasis i)‖ ^ 2) ≤
      ∑' i, ‖data.left (sourceBasis i)‖ ^ 2 := by
  have henergy := CC20Concrete.PositiveTrace.tsum_normSq_precomp_le
    sourceBasis targetBasis newSourceBasis data.left leftBounded
      data.left_summable_normSq
  have hnormSq : ‖leftBounded‖ ^ 2 ≤ (1 : ℝ) := by
    nlinarith [sq_nonneg (‖leftBounded‖ - 1), norm_nonneg leftBounded]
  have hnonneg : 0 ≤ ∑' i, ‖data.left (sourceBasis i)‖ ^ 2 :=
    tsum_nonneg fun i => sq_nonneg _
  calc
    _ ≤ ‖leftBounded‖ ^ 2 *
        (∑' i, ‖data.left (sourceBasis i)‖ ^ 2) := by
      simpa only [
        CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.boundedPrecomp]
        using henergy
    _ ≤ 1 * (∑' i, ‖data.left (sourceBasis i)‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hnormSq hnonneg
    _ = _ := one_mul _

theorem boundedPrecomp_right_tsum_le_of_norm_le_one
    {ι κ mu H K G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (targetBasis : HilbertBasis κ ℂ G)
    (newSourceBasis : HilbertBasis mu ℂ K)
    (data : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis)
    (leftBounded rightBounded : K →L[ℂ] H)
    (hright : ‖rightBounded‖ ≤ 1) :
    (∑' i, ‖(CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.boundedPrecomp
        targetBasis newSourceBasis data leftBounded rightBounded).right
        (newSourceBasis i)‖ ^ 2) ≤
      ∑' i, ‖data.right (sourceBasis i)‖ ^ 2 := by
  have henergy := CC20Concrete.PositiveTrace.tsum_normSq_precomp_le
    sourceBasis targetBasis newSourceBasis data.right rightBounded
      data.right_summable_normSq
  have hnormSq : ‖rightBounded‖ ^ 2 ≤ (1 : ℝ) := by
    nlinarith [sq_nonneg (‖rightBounded‖ - 1), norm_nonneg rightBounded]
  have hnonneg : 0 ≤ ∑' i, ‖data.right (sourceBasis i)‖ ^ 2 :=
    tsum_nonneg fun i => sq_nonneg _
  calc
    _ ≤ ‖rightBounded‖ ^ 2 *
        (∑' i, ‖data.right (sourceBasis i)‖ ^ 2) := by
      simpa only [
        CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.boundedPrecomp]
        using henergy
    _ ≤ 1 * (∑' i, ‖data.right (sourceBasis i)‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hnormSq hnonneg
    _ = _ := one_mul _

theorem boundedSandwich_left_tsum_le_of_norm_le_one
    {ι κ H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (targetBasis : HilbertBasis κ ℂ G)
    (data : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis)
    (leftBounded rightBounded : H →L[ℂ] H)
    (hleft : ‖leftBounded‖ ≤ 1) :
    (∑' i, ‖(data.boundedSandwich targetBasis leftBounded rightBounded).left
        (sourceBasis i)‖ ^ 2) ≤
      ∑' i, ‖data.left (sourceBasis i)‖ ^ 2 := by
  have hadjoint : ‖leftBounded.adjoint‖ ≤ 1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact hleft
  simpa only [
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.boundedSandwich]
    using boundedPrecomp_left_tsum_le_of_norm_le_one targetBasis sourceBasis
      data leftBounded.adjoint rightBounded hadjoint

theorem boundedSandwich_right_tsum_le_of_norm_le_one
    {ι κ H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (targetBasis : HilbertBasis κ ℂ G)
    (data : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis)
    (leftBounded rightBounded : H →L[ℂ] H)
    (hright : ‖rightBounded‖ ≤ 1) :
    (∑' i, ‖(data.boundedSandwich targetBasis leftBounded rightBounded).right
        (sourceBasis i)‖ ^ 2) ≤
      ∑' i, ‖data.right (sourceBasis i)‖ ^ 2 := by
  simpa only [
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.boundedSandwich]
    using boundedPrecomp_right_tsum_le_of_norm_le_one targetBasis sourceBasis
      data leftBounded.adjoint rightBounded hright

/-- The literal band-to-Sonin Euler input is a contraction uniformly in the
visible finite family. -/
theorem norm_sourceBandFiniteEulerSoninInput_le_one
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    ‖sourceBandFiniteEulerSoninInput lambda family‖ ≤ 1 := by
  have hSourceAdjoint : ‖(sourceInclusion lambda)†‖ ≤ 1 := by
    have hadjoint : ‖(sourceInclusion lambda)†‖ = ‖sourceInclusion lambda‖ :=
      ContinuousLinearMap.adjoint.norm_map _
    rw [hadjoint]
    exact Submodule.norm_subtypeL_le _
  have hSupport : ‖radialSupportProjection lambda‖ ≤ 1 :=
    IsStarProjection.norm_le _ (radialSupportProjection_isStarProjection lambda)
  have hInverse : ‖normalizedFiniteEulerInverse family‖ ≤ 1 :=
    norm_normalizedFiniteEulerInverse_le_one family
  have hBandInclusion : ‖sourceBandInclusion lambda‖ ≤ 1 :=
    Submodule.norm_subtypeL_le _
  have hFirst :
      ‖(sourceInclusion lambda)† ∘L radialSupportProjection lambda‖ ≤ 1 := by
    calc
      _ ≤ ‖(sourceInclusion lambda)†‖ *
          ‖radialSupportProjection lambda‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul hSourceAdjoint hSupport (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul _
  have hSecond :
      ‖(sourceInclusion lambda)† ∘L radialSupportProjection lambda ∘L
          normalizedFiniteEulerInverse family‖ ≤ 1 := by
    calc
      _ ≤ ‖(sourceInclusion lambda)† ∘L radialSupportProjection lambda‖ *
          ‖normalizedFiniteEulerInverse family‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul hFirst hInverse (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul _
  have hThird :
      ‖(sourceInclusion lambda)† ∘L radialSupportProjection lambda ∘L
          normalizedFiniteEulerInverse family ∘L
          radialSupportProjection lambda‖ ≤ 1 := by
    calc
      _ ≤ ‖(sourceInclusion lambda)† ∘L radialSupportProjection lambda ∘L
            normalizedFiniteEulerInverse family‖ *
          ‖radialSupportProjection lambda‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul hSecond hSupport (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul _
  unfold sourceBandFiniteEulerSoninInput
  calc
    _ ≤ ‖(sourceInclusion lambda)† ∘L radialSupportProjection lambda ∘L
          normalizedFiniteEulerInverse family ∘L
          radialSupportProjection lambda‖ *
        ‖sourceBandInclusion lambda‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul hThird hBandInclusion
      (norm_nonneg (sourceBandInclusion lambda)) (by norm_num)
    _ = 1 := one_mul _

set_option maxHeartbeats 4000000 in
-- The theorem unfolds the fixed four-coordinate pair through two carrier
-- changes while preserving the family-independent energy majorant.
/-- The normalized finite-Euler fixed-quotient first jet is bounded by the
square energy of the fixed physical boundary pair, independently of the
visible finite family. -/
theorem sourceBandFiniteEulerFixedQuotientFirstJet_ordinaryTrace_norm_le_fixedPhysicalEnergy
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ tau ιr κr taur nu mu rho : Type*}
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
    (bandBasis : HilbertBasis rho ℂ (sourceBandCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    let fixedPair :=
      fixedPhysicalPairData owner lambda a c hac hsupp negativeBasis
        positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
        reflectedOutputBasis globalBasis boundaryBasis hfactor
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong bandBasis
        (sourceBandFiniteEulerFixedQuotientFirstJetInputSideProducer owner lambda
          family a c hac hsupp negativeBasis positiveBasis outputBasis
          reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
          globalBasis boundaryBasis bandBasis hfactor).response‖ ≤
      (1 / 2 : ℝ) *
        ((∑' i, ‖fixedPair.left (globalBasis i)‖ ^ 2) +
          ∑' i, ‖fixedPair.right (globalBasis i)‖ ^ 2) := by
  dsimp only
  let fixedPair :=
    fixedPhysicalPairData owner lambda a c hac hsupp negativeBasis
      positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis boundaryBasis hfactor
  let transport := radialSupportProjection lambda ∘L
    normalizedFiniteEulerInverse family ∘L radialSupportProjection lambda
  let inner := sourceCompression (radialSupportProjection lambda)
    (sourceFourierSupportProjection lambda) (sourceProlateRemainder lambda)
  let firstPair := sourceFixedQuotientFirstJetPairData owner lambda a c hac
    hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      hfactor transport
  let bandPair :=
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.boundedPrecomp
      boundaryBasis bandBasis firstPair (sourceBandInclusion lambda)
        (sourceBandInclusion lambda)
  have hFirstPair : firstPair = fixedPair.boundedSandwich boundaryBasis
      (sourceBandProjection lambda)
      (inner ∘L transport ∘L sourceBandProjection lambda) := by
    rfl
  have hproducer :
      (sourceBandFiniteEulerFixedQuotientFirstJetInputSideProducer owner lambda
        family a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis boundaryBasis bandBasis hfactor).response =
      (inputSideRootS2ProducerOfPairData bandPair).response := by
    rfl
  have hBand : ‖sourceBandProjection lambda‖ ≤ 1 :=
    IsStarProjection.norm_le _ (sourceBandProjection_isStarProjection lambda)
  have hBandInclusion : ‖sourceBandInclusion lambda‖ ≤ 1 :=
    Submodule.norm_subtypeL_le _
  have hSupport : ‖radialSupportProjection lambda‖ ≤ 1 :=
    IsStarProjection.norm_le _ (radialSupportProjection_isStarProjection lambda)
  have hInverse : ‖normalizedFiniteEulerInverse family‖ ≤ 1 :=
    norm_normalizedFiniteEulerInverse_le_one family
  have hSupportInverse :
      ‖radialSupportProjection lambda ∘L
          normalizedFiniteEulerInverse family‖ ≤ 1 := by
    calc
      _ ≤ ‖radialSupportProjection lambda‖ *
          ‖normalizedFiniteEulerInverse family‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul hSupport hInverse (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul _
  have hTransport : ‖transport‖ ≤ 1 := by
    dsimp only [transport]
    calc
      _ ≤ ‖radialSupportProjection lambda ∘L
            normalizedFiniteEulerInverse family‖ *
          ‖radialSupportProjection lambda‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 :=
        mul_le_mul hSupportInverse hSupport (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul _
  have hInnerEq : inner = sourceSoninProjection lambda := by
    dsimp only [inner]
    simpa only [ContinuousLinearMap.mul_def] using
      (sourceSoninProjection_eq_compression_sub_prolate lambda).symm
  have hInner : ‖inner‖ ≤ 1 := by
    rw [hInnerEq]
    exact IsStarProjection.norm_le _ (sourceSoninProjection_isStarProjection lambda)
  have hInnerTransport : ‖inner ∘L transport‖ ≤ 1 := by
    calc
      _ ≤ ‖inner‖ * ‖transport‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul hInner hTransport (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul _
  have hRightSandwich :
      ‖inner ∘L transport ∘L sourceBandProjection lambda‖ ≤ 1 := by
    calc
      _ ≤ ‖inner ∘L transport‖ * ‖sourceBandProjection lambda‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul hInnerTransport hBand (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul _
  have hBandLeft := boundedPrecomp_left_tsum_le_of_norm_le_one
    boundaryBasis bandBasis firstPair (sourceBandInclusion lambda)
      (sourceBandInclusion lambda) hBandInclusion
  have hBandRight := boundedPrecomp_right_tsum_le_of_norm_le_one
    boundaryBasis bandBasis firstPair (sourceBandInclusion lambda)
      (sourceBandInclusion lambda) hBandInclusion
  have hFirstLeft := boundedSandwich_left_tsum_le_of_norm_le_one
    boundaryBasis fixedPair (sourceBandProjection lambda)
      (inner ∘L transport ∘L sourceBandProjection lambda) hBand
  have hFirstRight := boundedSandwich_right_tsum_le_of_norm_le_one
    boundaryBasis fixedPair (sourceBandProjection lambda)
      (inner ∘L transport ∘L sourceBandProjection lambda) hRightSandwich
  have hLeft :
      (∑' i, ‖bandPair.left (bandBasis i)‖ ^ 2) ≤
        ∑' i, ‖fixedPair.left (globalBasis i)‖ ^ 2 := by
    have hBandToFirst :
        (∑' i, ‖bandPair.left (bandBasis i)‖ ^ 2) ≤
          ∑' i, ‖firstPair.left (globalBasis i)‖ ^ 2 := by
      simpa only [bandPair] using hBandLeft
    rw [hFirstPair] at hBandToFirst
    exact hBandToFirst.trans hFirstLeft
  have hRight :
      (∑' i, ‖bandPair.right (bandBasis i)‖ ^ 2) ≤
        ∑' i, ‖fixedPair.right (globalBasis i)‖ ^ 2 := by
    have hBandToFirst :
        (∑' i, ‖bandPair.right (bandBasis i)‖ ^ 2) ≤
          ∑' i, ‖firstPair.right (globalBasis i)‖ ^ 2 := by
      simpa only [bandPair] using hBandRight
    rw [hFirstPair] at hBandToFirst
    exact hBandToFirst.trans hFirstRight
  rw [hproducer]
  exact (inputSideRootS2ProducerOfPairData_ordinaryTrace_norm_le bandPair).trans
    (mul_le_mul_of_nonneg_left (add_le_add hLeft hRight) (by norm_num))

end CCM24FiniteSFixedQuotientContractionBound
end CCM25Concrete
end Source
end ConnesWeilRH
