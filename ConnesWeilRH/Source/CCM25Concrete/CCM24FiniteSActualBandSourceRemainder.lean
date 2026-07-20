/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualBandFirstJetTrace

/-!
# Actual band first jet on the source Sonin carrier

Proof 439 owns the correctly oriented normalized-inverse first jet on the
ambient common-log carrier.  The nonlinear Gram response already has a legal
owner on the source Sonin carrier.  This module transports the first-jet pair
through the genuine Sonin inclusion and forms a same-carrier remainder pair.

The result is an exact trace ledger.  It does not estimate the nonlinear
remainder or identify it with a branchwise absolute-value bound.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSActualBandSourceRemainder

open CC20Concrete
open MeasureTheory
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSBandTrace
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSInverseMetric
open CCM24FiniteSInputSideTraceConsumer
open CCM24FiniteSFixedQuotientContractionBound
open CCM24FiniteSFixedQuotientCarrier
open CCM24FiniteSActualBandFirstJetTrace
open CCM24FiniteSRootCompletedFirstJet
open CCM24SourceProlateTrace
open CC20Concrete.CompactRootHalfLinePair
open scoped InnerProduct InnerProductSpace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace
      (CCM24FiniteSGramResponse.sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

noncomputable abbrev actualBandPairCarrier (a c : ℝ) :=
  WithLp 2 (commonBoundaryCarrier a c × commonBoundaryCarrier a c)

/-! ## Ambient pair energy -/

theorem actualBandCommutatorPairData_left_basisEnergy_le_two_source
    {ι κ H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (targetBasis : HilbertBasis κ ℂ G)
    (sourceData :
      CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
        (G := G) sourceBasis)
    (band inner transport transportAdjoint : H →L[ℂ] H)
    (hInner : ‖inner‖ ≤ 1)
    (hReverse : ‖inner ∘L transportAdjoint ∘L band‖ ≤ 1) :
    (∑' i, ‖(actualBandCommutatorPairData targetBasis sourceData band
      inner transport transportAdjoint).left (sourceBasis i)‖ ^ 2) ≤
      2 * (∑' i, ‖sourceData.left (sourceBasis i)‖ ^ 2) := by
  let forwardBase := sourceData.boundedSandwich targetBasis inner
    (band ∘L transport ∘L inner)
  let forward := forwardBase.smulRight (-1)
  let reverse := sourceData.boundedSandwich targetBasis
    (inner ∘L transportAdjoint ∘L band) inner
  let pair := CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.l2Sum
    forward reverse
  have hPair :
      actualBandCommutatorPairData targetBasis sourceData band inner transport
        transportAdjoint = pair := by
    rfl
  rw [hPair, l2Sum_left_basisEnergy_eq_add]
  have hForward := boundedSandwich_left_tsum_le_of_norm_le_one
    targetBasis sourceData inner (band ∘L transport ∘L inner) hInner
  have hReverse := boundedSandwich_left_tsum_le_of_norm_le_one
    targetBasis sourceData (inner ∘L transportAdjoint ∘L band) inner hReverse
  have hForward' :
      (∑' i, ‖forward.left (sourceBasis i)‖ ^ 2) ≤
        ∑' i, ‖sourceData.left (sourceBasis i)‖ ^ 2 := by
    simpa only [forward,
      CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.smulRight] using
      hForward
  have hReverse' :
      (∑' i, ‖reverse.left (sourceBasis i)‖ ^ 2) ≤
        ∑' i, ‖sourceData.left (sourceBasis i)‖ ^ 2 := by
    simpa only [reverse] using hReverse
  linarith

theorem actualBandCommutatorPairData_right_basisEnergy_le_two_source
    {ι κ H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (targetBasis : HilbertBasis κ ℂ G)
    (sourceData :
      CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
        (G := G) sourceBasis)
    (band inner transport transportAdjoint : H →L[ℂ] H)
    (hInner : ‖inner‖ ≤ 1)
    (hForward : ‖band ∘L transport ∘L inner‖ ≤ 1) :
    (∑' i, ‖(actualBandCommutatorPairData targetBasis sourceData band
      inner transport transportAdjoint).right (sourceBasis i)‖ ^ 2) ≤
      2 * (∑' i, ‖sourceData.right (sourceBasis i)‖ ^ 2) := by
  let forwardBase := sourceData.boundedSandwich targetBasis inner
    (band ∘L transport ∘L inner)
  let forward := forwardBase.smulRight (-1)
  let reverse := sourceData.boundedSandwich targetBasis
    (inner ∘L transportAdjoint ∘L band) inner
  let pair := CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.l2Sum
    forward reverse
  have hPair :
      actualBandCommutatorPairData targetBasis sourceData band inner transport
        transportAdjoint = pair := by
    rfl
  rw [hPair, l2Sum_right_basisEnergy_eq_add]
  have hForward := boundedSandwich_right_tsum_le_of_norm_le_one
    targetBasis sourceData inner (band ∘L transport ∘L inner) hForward
  have hReverse := boundedSandwich_right_tsum_le_of_norm_le_one
    targetBasis sourceData (inner ∘L transportAdjoint ∘L band) inner hInner
  have hForward' :
      (∑' i, ‖forward.right (sourceBasis i)‖ ^ 2) ≤
        ∑' i, ‖sourceData.right (sourceBasis i)‖ ^ 2 := by
    have hEnergy :
        (∑' i, ‖forward.right (sourceBasis i)‖ ^ 2) =
          ∑' i, ‖forwardBase.right (sourceBasis i)‖ ^ 2 := by
      apply tsum_congr
      intro i
      simp only [forward,
        CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.smulRight,
        neg_smul, one_smul, ContinuousLinearMap.neg_apply, norm_neg]
    rw [hEnergy]
    exact hForward
  have hReverse' :
      (∑' i, ‖reverse.right (sourceBasis i)‖ ^ 2) ≤
        ∑' i, ‖sourceData.right (sourceBasis i)‖ ^ 2 := by
    simpa only [reverse] using hReverse
  linarith

/-! ## Pullback to the source Sonin carrier -/

noncomputable def sourceActualBandFiniteEulerSoninResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    CCM24FiniteSGramResponse.sourceSoninCarrier lambda →L[ℂ]
      CCM24FiniteSGramResponse.sourceSoninCarrier lambda :=
  (CCM24FiniteSGramResponse.sourceInclusion lambda)† ∘L
    sourceActualBandFiniteEulerPairedResponse owner lambda family ∘L
      CCM24FiniteSGramResponse.sourceInclusion lambda

noncomputable def sourceActualBandFiniteEulerSoninPairData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ tau ιr κr taur nu mu sigma rho : Type*}
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
    (pairedBoundaryBasis : HilbertBasis sigma ℂ
      (actualBandPairCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ
      (CCM24FiniteSGramResponse.sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := actualBandPairCarrier a c) sourceBasis :=
  CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.boundedPrecomp
    pairedBoundaryBasis sourceBasis
    (sourceActualBandFiniteEulerPairData owner lambda family a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      hfactor)
    (CCM24FiniteSGramResponse.sourceInclusion lambda)
    (CCM24FiniteSGramResponse.sourceInclusion lambda)

theorem sourceActualBandFiniteEulerSoninPairData_traceProduct_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ tau ιr κr taur nu mu sigma rho : Type*}
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
    (pairedBoundaryBasis : HilbertBasis sigma ℂ
      (actualBandPairCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ
      (CCM24FiniteSGramResponse.sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (sourceActualBandFiniteEulerSoninPairData owner lambda family a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      pairedBoundaryBasis sourceBasis hfactor).traceProduct =
      sourceActualBandFiniteEulerSoninResponse owner lambda family := by
  rw [sourceActualBandFiniteEulerSoninPairData,
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.boundedPrecomp_traceProduct_eq,
    sourceActualBandFiniteEulerPairData_traceProduct_eq owner lambda family
      a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis hfactor]
  rfl

theorem sourceActualBandFiniteEulerSoninResponse_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ tau ιr κr taur nu mu sigma rho : Type*}
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
    (pairedBoundaryBasis : HilbertBasis sigma ℂ
      (actualBandPairCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ
      (CCM24FiniteSGramResponse.sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    CC20Concrete.PositiveTrace.IsTraceClassAlong sourceBasis
      (sourceActualBandFiniteEulerSoninResponse owner lambda family) := by
  rw [← sourceActualBandFiniteEulerSoninPairData_traceProduct_eq owner lambda
    family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor]
  exact (sourceActualBandFiniteEulerSoninPairData owner lambda family a c hac
    hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    pairedBoundaryBasis sourceBasis hfactor).traceProduct_isTraceClassAlong

set_option maxHeartbeats 800000 in
-- The source pullback unfolds the four-coordinate physical pair through two
-- Hilbert--Schmidt carrier changes; keep this local to the elaboration only.
/-- Pullback through the isometric Sonin inclusion preserves the family-free
fixed physical energy bound. -/
theorem sourceActualBandFiniteEulerSonin_ordinaryTrace_norm_le_fixedEnergy
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ tau ιr κr taur nu mu sigma rho : Type*}
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
    (pairedBoundaryBasis : HilbertBasis sigma ℂ
      (actualBandPairCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ
      (CCM24FiniteSGramResponse.sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    let fixedPair :=
      fixedPhysicalPairData owner lambda a c hac hsupp negativeBasis
        positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
        reflectedOutputBasis globalBasis boundaryBasis hfactor
    ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        (sourceActualBandFiniteEulerSoninResponse owner lambda family)‖ ≤
      (∑' i, ‖fixedPair.left (globalBasis i)‖ ^ 2) +
        ∑' i, ‖fixedPair.right (globalBasis i)‖ ^ 2 := by
  dsimp only
  let fixedPair :=
    fixedPhysicalPairData owner lambda a c hac hsupp negativeBasis
      positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis boundaryBasis hfactor
  let ambientPair :=
    actualBandCommutatorPairData boundaryBasis fixedPair
      (sourceBandProjection lambda) (sourceSoninProjection lambda)
      (normalizedFiniteEulerInverse family)
      (ContinuousLinearMap.adjoint (normalizedFiniteEulerInverse family))
  let sourcePair :=
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.boundedPrecomp
      pairedBoundaryBasis sourceBasis ambientPair
      (CCM24FiniteSGramResponse.sourceInclusion lambda)
      (CCM24FiniteSGramResponse.sourceInclusion lambda)
  have hInner : ‖sourceSoninProjection lambda‖ ≤ 1 :=
    IsStarProjection.norm_le _ (sourceSoninProjection_isStarProjection lambda)
  have hBand : ‖sourceBandProjection lambda‖ ≤ 1 :=
    IsStarProjection.norm_le _ (sourceBandProjection_isStarProjection lambda)
  have hInverse : ‖normalizedFiniteEulerInverse family‖ ≤ 1 :=
    norm_normalizedFiniteEulerInverse_le_one family
  have hInverseAdjoint :
      ‖ContinuousLinearMap.adjoint
        (normalizedFiniteEulerInverse family)‖ ≤ 1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact hInverse
  have hBandInverse :
      ‖sourceBandProjection lambda ∘L
          normalizedFiniteEulerInverse family‖ ≤ 1 := by
    calc
      _ ≤ ‖sourceBandProjection lambda‖ *
          ‖normalizedFiniteEulerInverse family‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul hBand hInverse (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul _
  have hForward :
      ‖sourceBandProjection lambda ∘L normalizedFiniteEulerInverse family ∘L
          sourceSoninProjection lambda‖ ≤ 1 := by
    calc
      _ ≤ ‖sourceBandProjection lambda ∘L
            normalizedFiniteEulerInverse family‖ *
          ‖sourceSoninProjection lambda‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul hBandInverse hInner (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul _
  have hInnerInverseAdjoint :
      ‖sourceSoninProjection lambda ∘L
          ContinuousLinearMap.adjoint
            (normalizedFiniteEulerInverse family)‖ ≤ 1 := by
    calc
      _ ≤ ‖sourceSoninProjection lambda‖ *
          ‖ContinuousLinearMap.adjoint
            (normalizedFiniteEulerInverse family)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 :=
        mul_le_mul hInner hInverseAdjoint (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul _
  have hReverse :
      ‖sourceSoninProjection lambda ∘L
          ContinuousLinearMap.adjoint (normalizedFiniteEulerInverse family) ∘L
          sourceBandProjection lambda‖ ≤ 1 := by
    calc
      _ ≤ ‖sourceSoninProjection lambda ∘L
            ContinuousLinearMap.adjoint
              (normalizedFiniteEulerInverse family)‖ *
          ‖sourceBandProjection lambda‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 :=
        mul_le_mul hInnerInverseAdjoint hBand (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul _
  have hAmbientLeft :
      (∑' i, ‖ambientPair.left (globalBasis i)‖ ^ 2) ≤
        2 * (∑' i, ‖fixedPair.left (globalBasis i)‖ ^ 2) := by
    dsimp only [ambientPair]
    exact actualBandCommutatorPairData_left_basisEnergy_le_two_source
      (H := finiteSCarrier) (G := commonBoundaryCarrier a c)
      (sourceBasis := globalBasis)
      boundaryBasis fixedPair (sourceBandProjection lambda)
      (sourceSoninProjection lambda) (normalizedFiniteEulerInverse family)
      (ContinuousLinearMap.adjoint (normalizedFiniteEulerInverse family))
      hInner hReverse
  have hAmbientRight :
      (∑' i, ‖ambientPair.right (globalBasis i)‖ ^ 2) ≤
        2 * (∑' i, ‖fixedPair.right (globalBasis i)‖ ^ 2) := by
    dsimp only [ambientPair]
    exact actualBandCommutatorPairData_right_basisEnergy_le_two_source
      (H := finiteSCarrier) (G := commonBoundaryCarrier a c)
      (sourceBasis := globalBasis)
      boundaryBasis fixedPair (sourceBandProjection lambda)
      (sourceSoninProjection lambda) (normalizedFiniteEulerInverse family)
      (ContinuousLinearMap.adjoint (normalizedFiniteEulerInverse family))
      hInner hForward
  have hInclusion :
      ‖CCM24FiniteSGramResponse.sourceInclusion lambda‖ ≤ 1 :=
    Submodule.norm_subtypeL_le _
  have hSourceLeft :
      (∑' i, ‖sourcePair.left (sourceBasis i)‖ ^ 2) ≤
        ∑' i, ‖ambientPair.left (globalBasis i)‖ ^ 2 := by
    dsimp only [sourcePair]
    exact boundedPrecomp_left_tsum_le_of_norm_le_one pairedBoundaryBasis
      (H := finiteSCarrier)
      (K := CCM24FiniteSGramResponse.sourceSoninCarrier lambda)
      (G := actualBandPairCarrier a c) (sourceBasis := globalBasis)
      sourceBasis ambientPair
      (CCM24FiniteSGramResponse.sourceInclusion lambda)
      (CCM24FiniteSGramResponse.sourceInclusion lambda) hInclusion
  have hSourceRight :
      (∑' i, ‖sourcePair.right (sourceBasis i)‖ ^ 2) ≤
        ∑' i, ‖ambientPair.right (globalBasis i)‖ ^ 2 := by
    dsimp only [sourcePair]
    exact boundedPrecomp_right_tsum_le_of_norm_le_one pairedBoundaryBasis
      (H := finiteSCarrier)
      (K := CCM24FiniteSGramResponse.sourceSoninCarrier lambda)
      (G := actualBandPairCarrier a c) (sourceBasis := globalBasis)
      sourceBasis ambientPair
      (CCM24FiniteSGramResponse.sourceInclusion lambda)
      (CCM24FiniteSGramResponse.sourceInclusion lambda) hInclusion
  have hAmbientTraceProduct :
      ambientPair.traceProduct =
        sourceActualBandFiniteEulerPairedResponse owner lambda family := by
    change
      (sourceActualBandFiniteEulerPairData owner lambda family a c hac hsupp
        negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
        hfactor).traceProduct = _
    exact sourceActualBandFiniteEulerPairData_traceProduct_eq owner lambda
      family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis hfactor
  have hSourceTraceProduct :
      sourcePair.traceProduct =
        sourceActualBandFiniteEulerSoninResponse owner lambda family := by
    dsimp only [sourcePair]
    rw [CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.boundedPrecomp_traceProduct_eq,
      hAmbientTraceProduct]
    rfl
  rw [← hSourceTraceProduct]
  change ‖CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
      sourcePair.traceProduct‖ ≤ _
  have hTrace := inputSideRootS2ProducerOfPairData_ordinaryTrace_norm_le
    sourcePair
  rw [inputSideRootS2ProducerOfPairData_response_eq] at hTrace
  calc
    _ ≤ (1 / 2 : ℝ) *
        ((∑' i, ‖sourcePair.left (sourceBasis i)‖ ^ 2) +
          ∑' i, ‖sourcePair.right (sourceBasis i)‖ ^ 2) := hTrace
    _ ≤ (1 / 2 : ℝ) *
        ((∑' i, ‖ambientPair.left (globalBasis i)‖ ^ 2) +
          ∑' i, ‖ambientPair.right (globalBasis i)‖ ^ 2) := by
      gcongr
    _ ≤ (∑' i, ‖fixedPair.left (globalBasis i)‖ ^ 2) +
        ∑' i, ‖fixedPair.right (globalBasis i)‖ ^ 2 := by
      nlinarith

/-! ## Same-carrier pair subtraction -/

noncomputable def pairDifferenceData
    {ι H G K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {sourceBasis : HilbertBasis ι ℂ H}
    (first : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis)
    (endpoint : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := K) sourceBasis) :
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := WithLp 2 (G × K)) sourceBasis :=
  CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.l2Sum first
    (endpoint.smulRight (-1))

theorem pairDifferenceData_traceProduct_eq
    {ι H G K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {sourceBasis : HilbertBasis ι ℂ H}
    (first : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := G) sourceBasis)
    (endpoint : CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := K) sourceBasis) :
    (pairDifferenceData first endpoint).traceProduct =
      first.traceProduct - endpoint.traceProduct := by
  rw [pairDifferenceData,
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.l2Sum_traceProduct_eq_add,
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData.smulRight_traceProduct_eq]
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.add_apply, neg_smul, one_smul,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply]
  rw [sub_eq_add_neg]

/-! ## Actual nonlinear remainder on the source Sonin carrier -/

noncomputable def sourceActualBandFiniteEulerRemainderResponse
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    CCM24FiniteSGramResponse.sourceSoninCarrier lambda →L[ℂ]
      CCM24FiniteSGramResponse.sourceSoninCarrier lambda :=
  sourceActualBandFiniteEulerSoninResponse owner lambda family -
    sourceBandGramResponse owner lambda family

noncomputable def sourceActualBandFiniteEulerRemainderPairData
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ tau ιr κr taur nu mu sigma rho : Type*}
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
    (pairedBoundaryBasis : HilbertBasis sigma ℂ
      (actualBandPairCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ
      (CCM24FiniteSGramResponse.sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    CC20Concrete.PositiveTrace.BasisHilbertSchmidtPairData
      (G := WithLp 2
        (actualBandPairCarrier a c × commonBoundaryCarrier a c)) sourceBasis :=
  pairDifferenceData
    (sourceActualBandFiniteEulerSoninPairData owner lambda family a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      pairedBoundaryBasis sourceBasis hfactor)
    (sourceThreeBranchSourcePairData owner lambda family a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis hfactor)

theorem sourceActualBandFiniteEulerRemainderPairData_traceProduct_eq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ tau ιr κr taur nu mu sigma rho : Type*}
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
    (pairedBoundaryBasis : HilbertBasis sigma ℂ
      (actualBandPairCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ
      (CCM24FiniteSGramResponse.sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (sourceActualBandFiniteEulerRemainderPairData owner lambda family a c hac
      hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      pairedBoundaryBasis sourceBasis hfactor).traceProduct =
      sourceActualBandFiniteEulerRemainderResponse owner lambda family := by
  rw [sourceActualBandFiniteEulerRemainderPairData,
    pairDifferenceData_traceProduct_eq,
    sourceActualBandFiniteEulerSoninPairData_traceProduct_eq owner lambda
      family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor,
    sourceThreeBranchSourcePairData_traceProduct_eq owner lambda family
      a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis sourceBasis hfactor]
  rfl

theorem sourceActualBandFiniteEulerRemainderResponse_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ tau ιr κr taur nu mu sigma rho : Type*}
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
    (pairedBoundaryBasis : HilbertBasis sigma ℂ
      (actualBandPairCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ
      (CCM24FiniteSGramResponse.sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    CC20Concrete.PositiveTrace.IsTraceClassAlong sourceBasis
      (sourceActualBandFiniteEulerRemainderResponse owner lambda family) := by
  rw [← sourceActualBandFiniteEulerRemainderPairData_traceProduct_eq owner
    lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor]
  exact (sourceActualBandFiniteEulerRemainderPairData owner lambda family a c
    hac hsupp negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
    pairedBoundaryBasis sourceBasis hfactor).traceProduct_isTraceClassAlong

theorem sourceBandGramResponse_eq_soninFirstJet_sub_remainder
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily) :
    sourceBandGramResponse owner lambda family =
      sourceActualBandFiniteEulerSoninResponse owner lambda family -
        sourceActualBandFiniteEulerRemainderResponse owner lambda family := by
  unfold sourceActualBandFiniteEulerRemainderResponse
  abel

theorem ordinaryTraceAlong_sourceBandGramResponse_eq_first_sub_remainder
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ tau ιr κr taur nu mu sigma rho : Type*}
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
    (pairedBoundaryBasis : HilbertBasis sigma ℂ
      (actualBandPairCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ
      (CCM24FiniteSGramResponse.sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        (sourceBandGramResponse owner lambda family) =
      CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
        (sourceActualBandFiniteEulerSoninResponse owner lambda family) -
        CC20Concrete.PositiveTrace.ordinaryTraceAlong sourceBasis
          (sourceActualBandFiniteEulerRemainderResponse owner lambda family) := by
  rw [sourceBandGramResponse_eq_soninFirstJet_sub_remainder]
  exact CC20Concrete.PositiveTrace.ordinaryTraceAlong_sub sourceBasis _ _
    (sourceActualBandFiniteEulerSoninResponse_isTraceClassAlong owner lambda
      family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor)
    (sourceActualBandFiniteEulerRemainderResponse_isTraceClassAlong owner
      lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis pairedBoundaryBasis sourceBasis hfactor)

end CCM24FiniteSActualBandSourceRemainder
end CCM25Concrete
end Source
end ConnesWeilRH
