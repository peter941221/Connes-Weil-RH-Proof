/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRootCompletedDetectorPhysicalDiagonal

/-!
# Primitive compact-root outer pairing

The outer and reflected-outer coordinates of Proof 470 are reduced to the
single primitive `translatedCompactRootPairData`.  Their four-term
antisymmetrization is formed before the coupled second-support/prolate
remainder is reattached, and no absolute value is taken.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSRootCompletedDetectorPrimitiveOuter

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSProjectionTrace
open CCM24FiniteSBandTrace
open CCM24FiniteSFixedQuotientCarrier
open CCM24FiniteSCommonBoundaryPair
open CCM24RadialBoundaryPairTransport
open CCM24SourceProlateTrace
open CCM24FiniteSRootCompletedDetectorTrace
open CCM24FiniteSRootCompletedDetectorPhysicalDiagonal

/-- The reverse inner product of an `L2`-sum pair is the sum of its reverse
coordinate pairings. -/
theorem l2Sum_reverse_inner_pairing_eq_add
    {H G K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {ι : Type*} {basis : HilbertBasis ι ℂ H}
    (first : BasisHilbertSchmidtPairData (G := G) basis)
    (second : BasisHilbertSchmidtPairData (G := K) basis)
    (x y : H) :
    inner ℂ
        ((BasisHilbertSchmidtPairData.l2Sum first second).right x)
        ((BasisHilbertSchmidtPairData.l2Sum first second).left y) =
      inner ℂ (first.right x) (first.left y) +
        inner ℂ (second.right x) (second.left y) := by
  unfold BasisHilbertSchmidtPairData.l2Sum
  simp [ContinuousLinearMap.comp_apply, WithLp.prod_inner_apply]

/-- Forward pairing of the signed adjoint-minus-forward pair owner. -/
theorem boundedAdjointSub_inner_pairing_eq_sub
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {ι κ : Type*} {basis : HilbertBasis ι ℂ H}
    (targetBasis : HilbertBasis κ ℂ G)
    (data : BasisHilbertSchmidtPairData (G := G) basis)
    (leftBounded rightBounded : H →L[ℂ] H) (x y : H) :
    inner ℂ
        ((data.boundedAdjointSub targetBasis leftBounded rightBounded).left x)
        ((data.boundedAdjointSub targetBasis leftBounded rightBounded).right y) =
      inner ℂ (data.right (leftBounded.adjoint x))
          (data.left (rightBounded y)) -
        inner ℂ (data.left (leftBounded.adjoint x))
          (data.right (rightBounded y)) := by
  rw [BasisHilbertSchmidtPairData.boundedAdjointSub,
    l2Sum_inner_pairing_eq_add]
  simp only [BasisHilbertSchmidtPairData.swap,
    BasisHilbertSchmidtPairData.boundedSandwich,
    BasisHilbertSchmidtPairData.smulRight,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    neg_one_smul, inner_neg_right, sub_eq_add_neg]

/-- Reverse pairing of the same signed pair owner. -/
theorem boundedAdjointSub_reverse_inner_pairing_eq_sub
    {H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {ι κ : Type*} {basis : HilbertBasis ι ℂ H}
    (targetBasis : HilbertBasis κ ℂ G)
    (data : BasisHilbertSchmidtPairData (G := G) basis)
    (leftBounded rightBounded : H →L[ℂ] H) (x y : H) :
    inner ℂ
        ((data.boundedAdjointSub targetBasis leftBounded rightBounded).right x)
        ((data.boundedAdjointSub targetBasis leftBounded rightBounded).left y) =
      inner ℂ (data.left (rightBounded x))
          (data.right (leftBounded.adjoint y)) -
        inner ℂ (data.right (rightBounded x))
          (data.left (leftBounded.adjoint y)) := by
  rw [BasisHilbertSchmidtPairData.boundedAdjointSub,
    l2Sum_reverse_inner_pairing_eq_add]
  simp only [BasisHilbertSchmidtPairData.swap,
    BasisHilbertSchmidtPairData.boundedSandwich,
    BasisHilbertSchmidtPairData.smulRight,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    neg_one_smul, inner_neg_left, sub_eq_add_neg]

/-- The four-term antisymmetrized pairing of the one primitive translated
compact-root pair. -/
noncomputable def sourceTranslatedCompactRootOuterReflectedPairing
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval a c))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval a c))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (x y : finiteSCarrier) : ℂ :=
  let rootPair := translatedCompactRootPairData owner lambda a c negativeBasis
    positiveBasis outputBasis globalBasis
  let prefixOperator := radialSupportProjection lambda ∘L
    sourceFourierSupportProjection lambda
  (inner ℂ (rootPair.right (prefixOperator.adjoint x)) (rootPair.left y) -
      inner ℂ (rootPair.left (prefixOperator.adjoint x)) (rootPair.right y)) -
    (inner ℂ (rootPair.left x)
        (rootPair.right (prefixOperator.adjoint y)) -
      inner ℂ (rootPair.right x)
        (rootPair.left (prefixOperator.adjoint y)))

/-- The outer and reflected-outer physical coordinates are exactly the
four-term primitive compact-root antisymmetrization. -/
theorem outer_add_reflected_inner_eq_translatedCompactRootPairing
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
    (x y : finiteSCarrier) :
    let outer := outerCommutatorPairData owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis globalBasis
    let reflected := reflectedOuterCommutatorPairData owner lambda a c hac
      hsupp negativeBasis positiveBasis outputBasis globalBasis
    inner ℂ (outer.left x) (outer.right y) +
        inner ℂ (reflected.left x) (reflected.right y) =
      sourceTranslatedCompactRootOuterReflectedPairing owner lambda a c
        negativeBasis positiveBasis outputBasis globalBasis x y := by
  dsimp only
  rw [reflectedOuterCommutatorPairData]
  simp only [BasisHilbertSchmidtPairData.swap,
    BasisHilbertSchmidtPairData.smulRight,
    ContinuousLinearMap.neg_apply, neg_one_smul, inner_neg_right]
  rw [outerCommutatorPairData,
    boundedAdjointSub_inner_pairing_eq_sub,
    boundedAdjointSub_reverse_inner_pairing_eq_sub]
  simp only [ContinuousLinearMap.id_apply]
  rfl

/-- Proof 470's complete physical pairing is the primitive outer/reflected
compact-root bracket plus the still-coupled second-support/prolate remainder. -/
theorem sourceThreeBranchPhysicalPairing_eq_primitiveOuter_add_remainder
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
    (x y : finiteSCarrier) :
    sourceThreeBranchPhysicalPairing owner lambda a c hac hsupp negativeBasis
        positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor x y =
      sourceTranslatedCompactRootOuterReflectedPairing owner lambda a c
          negativeBasis positiveBasis outputBasis globalBasis x y +
        inner ℂ
          ((secondSupportProlateRemainderPairData owner lambda a c hac hsupp
            reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
            globalBasis hfactor).left x)
          ((secondSupportProlateRemainderPairData owner lambda a c hac hsupp
            reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
            globalBasis hfactor).right y) := by
  rw [sourceThreeBranchPhysicalPairing]
  rw [outer_add_reflected_inner_eq_translatedCompactRootPairing owner lambda
    a c hac hsupp negativeBasis positiveBasis outputBasis globalBasis x y]

/-- The completed diagonal with the primitive outer/reflected bracket exposed
and the second-support/prolate remainder kept whole. -/
noncomputable def rootCompletedDetectorTranslationPrimitiveDiagonal
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (displacement : ℝ)
    (a c : ℝ) (hac : a ≤ c)
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
    (index : ν) : ℂ :=
  let x := sourceBandProjection lambda (globalBasis index)
  let y := (cc20GlobalLogTranslation (-displacement)).toContinuousLinearMap x
  (-1 : ℂ) * (sourceTranslatedCompactRootOuterReflectedPairing owner lambda a c
        negativeBasis positiveBasis outputBasis globalBasis x y +
      inner ℂ
        ((secondSupportProlateRemainderPairData owner lambda a c hac hsupp
          reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
          globalBasis hfactor).left x)
        ((secondSupportProlateRemainderPairData owner lambda a c hac hsupp
          reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
          globalBasis hfactor).right y))

theorem rootCompletedDetectorTranslationPhysicalDiagonal_eq_primitive
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (displacement : ℝ)
    (a c : ℝ) (hac : a ≤ c)
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
    (index : ν) :
    rootCompletedDetectorTranslationPhysicalDiagonal owner lambda displacement
        a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis hfactor index =
      rootCompletedDetectorTranslationPrimitiveDiagonal owner lambda
        displacement a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis hfactor index := by
  rw [rootCompletedDetectorTranslationPhysicalDiagonal,
    rootCompletedDetectorTranslationPrimitiveDiagonal]
  rw [sourceThreeBranchPhysicalPairing_eq_primitiveOuter_add_remainder owner
    lambda a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis hfactor]
  simp

/-- The atom trace is one `tsum` of the primitive outer/reflected bracket plus
the coupled second-support/prolate remainder. -/
theorem rootCompletedDetectorSoninTranslationTrace_eq_primitiveDiagonal_tsum
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (displacement : ℝ)
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
    rootCompletedDetectorSoninTranslationTrace owner lambda displacement
        globalBasis =
      ∑' index, rootCompletedDetectorTranslationPrimitiveDiagonal owner lambda
        displacement a c hac hsupp negativeBasis positiveBasis outputBasis
        reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
        globalBasis hfactor index := by
  rw [rootCompletedDetectorSoninTranslationTrace_eq_physicalDiagonal_tsum
    owner lambda displacement a c hac hsupp negativeBasis positiveBasis
    outputBasis reflectedNegativeBasis reflectedPositiveBasis
    reflectedOutputBasis globalBasis boundaryBasis hfactor]
  apply tsum_congr
  exact rootCompletedDetectorTranslationPhysicalDiagonal_eq_primitive owner
    lambda displacement a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis hfactor

end CCM24FiniteSRootCompletedDetectorPrimitiveOuter
end CCM25Concrete
end Source
end ConnesWeilRH
