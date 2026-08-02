/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedPhysicalSourceInput

/-!
# Fixed physical kernel bridge

The fixed physical input is a Gram square root of the complete three-branch
pair.  Its dense-range producer needs the common kernel of both Gram legs to
vanish.  This module reduces that condition to the two actual translated
compact boundary legs already present in the outer physical branch.

The reduction is algebraic: a zero in an `L2` product is a zero in each
coordinate, and the right leg of the signed outer pair contains the two
translated boundary legs without a support or norm estimate.  The remaining
joint injectivity statement is deliberately kept as the analytic source
obligation; no Fourier multiplier injectivity is substituted for it.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSFixedPhysicalKernelBridge

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSFixedPhysicalSourceInput
open CCM24FiniteSGramResponse
open CCM24FiniteSProjectionTrace
open CCM24RadialBoundaryPairTransport
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

/-! ## Product-coordinate kernel facts -/

theorem l2Sum_right_eq_zero_iff
    {ι H G K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    {sourceBasis : HilbertBasis ι ℂ H}
    (first : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (second : BasisHilbertSchmidtPairData (G := K) sourceBasis)
    (x : H) :
    (BasisHilbertSchmidtPairData.l2Sum first second).right x = 0 ↔
      first.right x = 0 ∧ second.right x = 0 := by
  constructor
  · intro hx
    change (WithLp.prodContinuousLinearEquiv 2 ℂ G K).symm
        (first.right x, second.right x) = 0 at hx
    have hcoords := congrArg (WithLp.prodContinuousLinearEquiv 2 ℂ G K) hx
    have hcoords' : (first.right x, second.right x) = (0, 0) := by
      simpa using hcoords
    exact ⟨by simpa using congrArg Prod.fst hcoords',
      by simpa using congrArg Prod.snd hcoords'⟩
  · rintro ⟨hfirst, hsecond⟩
    change (WithLp.prodContinuousLinearEquiv 2 ℂ G K).symm
        (first.right x, second.right x) = 0
    rw [hfirst, hsecond]
    simp

theorem boundedAdjointSub_right_eq_zero_iff
    {ι κ H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (targetBasis : HilbertBasis κ ℂ G)
    (data : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (leftBounded rightBounded : H →L[ℂ] H) (x : H) :
    (data.boundedAdjointSub targetBasis leftBounded rightBounded).right x = 0 ↔
      data.left (rightBounded x) = 0 ∧ data.right (rightBounded x) = 0 := by
  rw [BasisHilbertSchmidtPairData.boundedAdjointSub,
    l2Sum_right_eq_zero_iff]
  constructor
  · rintro ⟨hfirst, hsecond⟩
    constructor
    · simpa only [BasisHilbertSchmidtPairData.boundedSandwich,
        BasisHilbertSchmidtPairData.swap,
        ContinuousLinearMap.comp_apply] using hfirst
    · have hsecond' : -data.right (rightBounded x) = 0 := by
        simpa only [BasisHilbertSchmidtPairData.boundedSandwich,
          BasisHilbertSchmidtPairData.smulRight,
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
          neg_one_smul, ContinuousLinearMap.neg_apply] using hsecond
      exact neg_eq_zero.mp hsecond'
  · rintro ⟨hleft, hright⟩
    constructor
    · simpa only [BasisHilbertSchmidtPairData.boundedSandwich,
        BasisHilbertSchmidtPairData.swap,
        ContinuousLinearMap.comp_apply] using hleft
    · have hsecond' : -data.right (rightBounded x) = 0 :=
        neg_eq_zero.mpr hright
      simpa only [BasisHilbertSchmidtPairData.boundedSandwich,
        BasisHilbertSchmidtPairData.smulRight,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
        neg_one_smul, ContinuousLinearMap.neg_apply] using hsecond'

/-! ## The outer branch exposes the two translated boundary legs -/

theorem outerCommutatorPairData_right_eq_zero_imp_translated_boundary_legs_eq_zero
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (x : finiteSCarrier)
    (hx : (outerCommutatorPairData owner lambda a c hac hsupp negativeBasis
      positiveBasis outputBasis globalBasis).right x = 0) :
    (translatedCompactRootPairData owner lambda a c negativeBasis
      positiveBasis outputBasis globalBasis).left x = 0 ∧
      (translatedCompactRootPairData owner lambda a c negativeBasis
        positiveBasis outputBasis globalBasis).right x = 0 := by
  exact (boundedAdjointSub_right_eq_zero_iff outputBasis
    (translatedCompactRootPairData owner lambda a c negativeBasis
      positiveBasis outputBasis globalBasis)
    (radialSupportProjection lambda ∘L sourceFourierSupportProjection lambda)
    (ContinuousLinearMap.id ℂ finiteSCarrier) x).mp hx

set_option maxHeartbeats 4000000 in
-- The dependent three-branch carrier needs more elaboration time for the
-- definitional reduction from the nested `l2Sum` owner.
theorem sourceThreeBranchPairData_right_eq_zero_imp_translated_boundary_legs_eq_zero
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν : Type*}
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
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (x : finiteSCarrier)
    (hx : (sourceThreeBranchPairData owner lambda a c hac hsupp negativeBasis
      positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis hfactor).right x = 0) :
    (translatedCompactRootPairData owner lambda a c negativeBasis
      positiveBasis outputBasis globalBasis).left x = 0 ∧
      (translatedCompactRootPairData owner lambda a c negativeBasis
        positiveBasis outputBasis globalBasis).right x = 0 := by
  let outer := outerCommutatorPairData owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis globalBasis
  let reflected := reflectedOuterCommutatorPairData owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis globalBasis
  let remainder := secondSupportProlateRemainderPairData owner lambda a c hac
    hsupp reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis hfactor
  have houterSum :
      (BasisHilbertSchmidtPairData.l2Sum outer reflected).right x = 0 := by
    change (BasisHilbertSchmidtPairData.l2Sum
      (BasisHilbertSchmidtPairData.l2Sum outer reflected) remainder).right x = 0 at hx
    have hsplit :=
      (l2Sum_right_eq_zero_iff
        (BasisHilbertSchmidtPairData.l2Sum outer reflected) remainder x).mp
      hx
    exact hsplit.1
  have houter : outer.right x = 0 :=
    (l2Sum_right_eq_zero_iff outer reflected x).mp houterSum |>.1
  exact outerCommutatorPairData_right_eq_zero_imp_translated_boundary_legs_eq_zero
    owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis globalBasis x
    (by exact houter)

/-! ## Source-carrier reduction -/

theorem fixedSourceThreeBranchPairData_right_eq_zero_imp_translated_boundary_legs_eq_zero
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν mu rho : Type*}
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
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (x : sourceSoninCarrier lambda)
    (hx : (fixedSourceThreeBranchPairData owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis hfactor).right x = 0) :
    (translatedCompactRootPairData owner lambda a c negativeBasis
      positiveBasis outputBasis globalBasis).left (sourceInclusion lambda x) = 0 ∧
      (translatedCompactRootPairData owner lambda a c negativeBasis
        positiveBasis outputBasis globalBasis).right (sourceInclusion lambda x) = 0 := by
  have hbase :
      (sourceThreeBranchPairData owner lambda a c hac hsupp negativeBasis
        positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
        reflectedOutputBasis globalBasis hfactor).right (sourceInclusion lambda x) = 0 := by
    simpa only [fixedSourceThreeBranchPairData,
      BasisHilbertSchmidtPairData.boundedPrecomp,
      ContinuousLinearMap.comp_apply] using hx
  exact sourceThreeBranchPairData_right_eq_zero_imp_translated_boundary_legs_eq_zero
    owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis globalBasis
    hfactor (sourceInclusion lambda x) hbase

/-! ## The narrowed analytic producer contract -/

theorem fixedPhysicalSourceInput_denseRange_of_translated_boundary_pair_injective
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ιr κr τr ν mu rho : Type*}
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
    (boundaryBasis : HilbertBasis mu ℂ (commonBoundaryCarrier a c))
    (sourceBasis : HilbertBasis rho ℂ (sourceSoninCarrier lambda))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (hkernel : ∀ x : sourceSoninCarrier lambda,
      (translatedCompactRootPairData owner lambda a c negativeBasis
        positiveBasis outputBasis globalBasis).left (sourceInclusion lambda x) = 0 →
      (translatedCompactRootPairData owner lambda a c negativeBasis
        positiveBasis outputBasis globalBasis).right (sourceInclusion lambda x) = 0 →
      x = 0) :
    DenseRange (fixedPhysicalSourceInput owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      sourceBasis hfactor) := by
  apply fixedPhysicalSourceInput_denseRange_of_common_kernel_zero
    owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis globalBasis
    boundaryBasis sourceBasis hfactor
  intro x hleft hright
  have hboundary :=
    fixedSourceThreeBranchPairData_right_eq_zero_imp_translated_boundary_legs_eq_zero
      owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis globalBasis
      boundaryBasis sourceBasis hfactor x hright
  exact hkernel x hboundary.1 hboundary.2

end CCM24FiniteSFixedPhysicalKernelBridge
end CCM25Concrete
end Source
end ConnesWeilRH
