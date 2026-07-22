/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSReflectedRootEnergy

/-!
# Quantitative energy of the three compact physical boundary branches

The signed adjoint-minus-forward boundary owner is an orthogonal `L2` sum.
This module proves its two energy inequalities once and applies them to the
outer, reflected-outer, and genuine second-support compact root pairs.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSPhysicalBoundaryEnergy

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSProjectionTrace
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSFixedQuotientContractionBound
open CCM24FiniteSRootCompletedFirstJet
open CCM24FiniteSCompactRootEnergy
open CCM24FiniteSReflectedRootEnergy
open CCM24RadialBoundaryPairTransport
open CCM24ReflectedCompactRoot

/-- For a contracted signed adjoint-minus-forward owner, its left energy is
at most the sum of the two original leg energies. -/
theorem boundedAdjointSub_left_basisEnergy_le_add
    {ι κ H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (targetBasis : HilbertBasis κ ℂ G)
    (data : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (leftBounded rightBounded : H →L[ℂ] H)
    (hleft : ‖leftBounded‖ ≤ 1) :
    (∑' i, ‖(data.boundedAdjointSub targetBasis leftBounded rightBounded).left
        (sourceBasis i)‖ ^ 2) ≤
      (∑' i, ‖data.right (sourceBasis i)‖ ^ 2) +
        ∑' i, ‖data.left (sourceBasis i)‖ ^ 2 := by
  have hswap := boundedSandwich_left_tsum_le_of_norm_le_one targetBasis
    data.swap leftBounded rightBounded hleft
  have hforward := boundedSandwich_left_tsum_le_of_norm_le_one targetBasis
    data leftBounded rightBounded hleft
  rw [BasisHilbertSchmidtPairData.boundedAdjointSub,
    l2Sum_left_basisEnergy_eq_add]
  simpa only [BasisHilbertSchmidtPairData.swap,
    BasisHilbertSchmidtPairData.smulRight] using add_le_add hswap hforward

/-- For a contracted signed adjoint-minus-forward owner, its right energy is
at most the sum of the two original leg energies. -/
theorem boundedAdjointSub_right_basisEnergy_le_add
    {ι κ H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (targetBasis : HilbertBasis κ ℂ G)
    (data : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (leftBounded rightBounded : H →L[ℂ] H)
    (hright : ‖rightBounded‖ ≤ 1) :
    (∑' i, ‖(data.boundedAdjointSub targetBasis leftBounded rightBounded).right
        (sourceBasis i)‖ ^ 2) ≤
      (∑' i, ‖data.left (sourceBasis i)‖ ^ 2) +
        ∑' i, ‖data.right (sourceBasis i)‖ ^ 2 := by
  have hswap := boundedSandwich_right_tsum_le_of_norm_le_one targetBasis
    data.swap leftBounded rightBounded hright
  have hforward := boundedSandwich_right_tsum_le_of_norm_le_one targetBasis
    data leftBounded rightBounded hright
  rw [BasisHilbertSchmidtPairData.boundedAdjointSub,
    l2Sum_right_basisEnergy_eq_add]
  simpa only [BasisHilbertSchmidtPairData.swap,
    BasisHilbertSchmidtPairData.smulRight,
    ContinuousLinearMap.smul_apply, norm_smul, norm_neg, norm_one, one_mul,
    mul_pow] using add_le_add hswap hforward

private theorem norm_id_finiteSCarrier_le_one :
    ‖ContinuousLinearMap.id ℂ finiteSCarrier‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simp only [ContinuousLinearMap.id_apply, one_mul, le_refl]

private theorem norm_radialFourierPrefix_le_one (lambda : CCM24SoninScale) :
    ‖radialSupportProjection lambda ∘L
        sourceFourierSupportProjection lambda‖ ≤ 1 := by
  have hRadial : ‖radialSupportProjection lambda‖ ≤ 1 :=
    IsStarProjection.norm_le _ (radialSupportProjection_isStarProjection lambda)
  have hFourier : ‖sourceFourierSupportProjection lambda‖ ≤ 1 :=
    IsStarProjection.norm_le _
      (sourceFourierSupportProjection_isStarProjection lambda)
  calc
    _ ≤ ‖radialSupportProjection lambda‖ *
        ‖sourceFourierSupportProjection lambda‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul hRadial hFourier (norm_nonneg _) (by norm_num)
    _ = 1 := one_mul _

/-- The completed outer commutator's left leg costs at most twice the
primitive compact-root support energy. -/
theorem outerCommutatorPairData_left_basisEnergy_le_supportPolynomial
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
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    (∑' i, ‖(outerCommutatorPairData owner lambda a c hac hsupp negativeBasis
        positiveBasis outputBasis globalBasis).left (globalBasis i)‖ ^ 2) ≤
      2 * ((c - a) ^ 2 *
        SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) := by
  let data := translatedCompactRootPairData owner lambda a c negativeBasis
    positiveBasis outputBasis globalBasis
  have hgeneric := boundedAdjointSub_left_basisEnergy_le_add outputBasis data
    (radialSupportProjection lambda ∘L sourceFourierSupportProjection lambda)
    (ContinuousLinearMap.id ℂ finiteSCarrier)
    (norm_radialFourierPrefix_le_one lambda)
  have hleft :=
    translatedCompactRootPairData_left_basisEnergy_le_supportPolynomial owner
      lambda a c hac negativeBasis positiveBasis outputBasis globalBasis
  have hright :=
    translatedCompactRootPairData_right_basisEnergy_le_supportPolynomial owner
      lambda a c hac negativeBasis positiveBasis outputBasis globalBasis
  calc
    _ ≤ (∑' i, ‖data.right (globalBasis i)‖ ^ 2) +
        ∑' i, ‖data.left (globalBasis i)‖ ^ 2 := by
      simpa only [outerCommutatorPairData, data] using hgeneric
    _ ≤ ((c - a) ^ 2 *
          SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) +
        ((c - a) ^ 2 *
          SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) :=
      add_le_add hright hleft
    _ = 2 * ((c - a) ^ 2 *
        SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) := by ring

/-- The completed outer commutator's right leg has the same bound. -/
theorem outerCommutatorPairData_right_basisEnergy_le_supportPolynomial
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
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    (∑' i, ‖(outerCommutatorPairData owner lambda a c hac hsupp negativeBasis
        positiveBasis outputBasis globalBasis).right (globalBasis i)‖ ^ 2) ≤
      2 * ((c - a) ^ 2 *
        SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) := by
  let data := translatedCompactRootPairData owner lambda a c negativeBasis
    positiveBasis outputBasis globalBasis
  have hgeneric := boundedAdjointSub_right_basisEnergy_le_add outputBasis data
    (radialSupportProjection lambda ∘L sourceFourierSupportProjection lambda)
    (ContinuousLinearMap.id ℂ finiteSCarrier)
    norm_id_finiteSCarrier_le_one
  have hleft :=
    translatedCompactRootPairData_left_basisEnergy_le_supportPolynomial owner
      lambda a c hac negativeBasis positiveBasis outputBasis globalBasis
  have hright :=
    translatedCompactRootPairData_right_basisEnergy_le_supportPolynomial owner
      lambda a c hac negativeBasis positiveBasis outputBasis globalBasis
  calc
    _ ≤ (∑' i, ‖data.left (globalBasis i)‖ ^ 2) +
        ∑' i, ‖data.right (globalBasis i)‖ ^ 2 := by
      simpa only [outerCommutatorPairData, data] using hgeneric
    _ ≤ ((c - a) ^ 2 *
          SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) +
        ((c - a) ^ 2 *
          SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) :=
      add_le_add hleft hright
    _ = 2 * ((c - a) ^ 2 *
        SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) := by ring

/-- Swapping the outer pair and placing a sign in its right leg preserves the
same left energy bound. -/
theorem reflectedOuterCommutatorPairData_left_basisEnergy_le_supportPolynomial
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
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    (∑' i, ‖(reflectedOuterCommutatorPairData owner lambda a c hac hsupp
        negativeBasis positiveBasis outputBasis globalBasis).left
        (globalBasis i)‖ ^ 2) ≤
      2 * ((c - a) ^ 2 *
        SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) := by
  simpa only [reflectedOuterCommutatorPairData,
    BasisHilbertSchmidtPairData.swap,
    BasisHilbertSchmidtPairData.smulRight] using
    outerCommutatorPairData_right_basisEnergy_le_supportPolynomial owner lambda
      a c hac hsupp negativeBasis positiveBasis outputBasis globalBasis

/-- The reflected outer right leg has the same energy bound. -/
theorem reflectedOuterCommutatorPairData_right_basisEnergy_le_supportPolynomial
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
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    (∑' i, ‖(reflectedOuterCommutatorPairData owner lambda a c hac hsupp
        negativeBasis positiveBasis outputBasis globalBasis).right
        (globalBasis i)‖ ^ 2) ≤
      2 * ((c - a) ^ 2 *
        SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) := by
  simpa only [reflectedOuterCommutatorPairData,
    BasisHilbertSchmidtPairData.swap,
    BasisHilbertSchmidtPairData.smulRight,
    ContinuousLinearMap.smul_apply, norm_smul, norm_neg, norm_one, one_mul,
    mul_pow] using
    outerCommutatorPairData_left_basisEnergy_le_supportPolynomial owner lambda
      a c hac hsupp negativeBasis positiveBasis outputBasis globalBasis

/-- The genuine second-support commutator's left leg costs at most twice the
same original-root support energy. -/
theorem secondSupportCommutatorPairData_left_basisEnergy_le_supportPolynomial
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    (∑' i, ‖(secondSupportCommutatorPairData owner lambda a c hac hsupp
        negativeBasis positiveBasis outputBasis globalBasis).left
        (globalBasis i)‖ ^ 2) ≤
      2 * ((c - a) ^ 2 *
        SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) := by
  let data := sourceSecondSupportCompactRootPairData owner lambda a c
    negativeBasis positiveBasis outputBasis globalBasis
  have hRadial : ‖radialSupportProjection lambda‖ ≤ 1 :=
    IsStarProjection.norm_le _ (radialSupportProjection_isStarProjection lambda)
  have hgeneric := boundedAdjointSub_left_basisEnergy_le_add outputBasis data
    (radialSupportProjection lambda) (radialSupportProjection lambda) hRadial
  have hleft :=
    sourceSecondSupportCompactRootPairData_left_basisEnergy_le_original owner
      lambda a c hac negativeBasis positiveBasis outputBasis globalBasis
  have hright :=
    sourceSecondSupportCompactRootPairData_right_basisEnergy_le_original owner
      lambda a c hac negativeBasis positiveBasis outputBasis globalBasis
  calc
    _ ≤ (∑' i, ‖data.right (globalBasis i)‖ ^ 2) +
        ∑' i, ‖data.left (globalBasis i)‖ ^ 2 := by
      simpa only [secondSupportCommutatorPairData, data] using hgeneric
    _ ≤ ((c - a) ^ 2 *
          SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) +
        ((c - a) ^ 2 *
          SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) :=
      add_le_add hright hleft
    _ = 2 * ((c - a) ^ 2 *
        SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) := by ring

/-- The genuine second-support commutator's right leg has the same bound. -/
theorem secondSupportCommutatorPairData_right_basisEnergy_le_supportPolynomial
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ) (hac : a ≤ c)
    (hsupp : Function.support owner.sourceTest.test ⊆ Set.Icc a c)
    {ι κ τ ν : Type*}
    (negativeBasis : HilbertBasis ι ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryNegativeInputInterval (-c) (-a)))))
    (positiveBasis : HilbertBasis κ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryPositiveInputInterval (-c) (-a)))))
    (outputBasis : HilbertBasis τ ℂ
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
    (globalBasis : HilbertBasis ν ℂ finiteSCarrier) :
    (∑' i, ‖(secondSupportCommutatorPairData owner lambda a c hac hsupp
        negativeBasis positiveBasis outputBasis globalBasis).right
        (globalBasis i)‖ ^ 2) ≤
      2 * ((c - a) ^ 2 *
        SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) := by
  let data := sourceSecondSupportCompactRootPairData owner lambda a c
    negativeBasis positiveBasis outputBasis globalBasis
  have hRadial : ‖radialSupportProjection lambda‖ ≤ 1 :=
    IsStarProjection.norm_le _ (radialSupportProjection_isStarProjection lambda)
  have hgeneric := boundedAdjointSub_right_basisEnergy_le_add outputBasis data
    (radialSupportProjection lambda) (radialSupportProjection lambda) hRadial
  have hleft :=
    sourceSecondSupportCompactRootPairData_left_basisEnergy_le_original owner
      lambda a c hac negativeBasis positiveBasis outputBasis globalBasis
  have hright :=
    sourceSecondSupportCompactRootPairData_right_basisEnergy_le_original owner
      lambda a c hac negativeBasis positiveBasis outputBasis globalBasis
  calc
    _ ≤ (∑' i, ‖data.left (globalBasis i)‖ ^ 2) +
        ∑' i, ‖data.right (globalBasis i)‖ ^ 2 := by
      simpa only [secondSupportCommutatorPairData, data] using hgeneric
    _ ≤ ((c - a) ^ 2 *
          SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) +
        ((c - a) ^ 2 *
          SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) :=
      add_le_add hleft hright
    _ = 2 * ((c - a) ^ 2 *
        SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) := by ring

end CCM24FiniteSPhysicalBoundaryEnergy
end CCM25Concrete
end Source
end ConnesWeilRH
