/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSPhysicalBoundaryEnergy

/-!
# The complete fixed physical energy bound

The compact outer and second-support branches are combined with the fixed
prolate commutator.  The resulting bound controls both energies of the exact
three-branch pair and hence the complete finite-Euler trace, uniformly in the
visible finite prime family.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSFixedPhysicalEnergyBound

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSProjectionTrace
open CCM24FiniteSInverseMetric
open CCM24SourceProlateTrace
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSRootCompletedFirstJet
open CCM24FiniteSRootCompletedDetectorUniformTrace
open CCM24FiniteSFixedQuotientContractionBound
open CCM24FiniteSPhysicalBoundaryEnergy

private theorem norm_id_finiteSCarrier_le_one :
    ‖ContinuousLinearMap.id ℂ finiteSCarrier‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simp only [ContinuousLinearMap.id_apply, one_mul, le_refl]

/-- The forward prolate pair's left energy is the fixed prolate-factor energy
up to the identity contraction. -/
theorem prolateForwardPairData_left_basisEnergy_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (∑' i, ‖(prolateForwardPairData owner lambda globalBasis hfactor).left
        (globalBasis i)‖ ^ 2) ≤
      ∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
        (globalBasis i)‖ ^ 2 := by
  exact boundedSandwich_left_tsum_le_of_norm_le_one globalBasis
    (sourceProlatePairData globalBasis lambda hfactor)
    (ContinuousLinearMap.id ℂ finiteSCarrier) (detectorOperator owner)
    norm_id_finiteSCarrier_le_one

/-- The detector costs its operator norm squared on the forward prolate
pair's right energy. -/
theorem prolateForwardPairData_right_basisEnergy_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (∑' i, ‖(prolateForwardPairData owner lambda globalBasis hfactor).right
        (globalBasis i)‖ ^ 2) ≤
      ‖detectorOperator owner‖ ^ 2 *
        ∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
          (globalBasis i)‖ ^ 2 := by
  simpa only [prolateForwardPairData, sourceProlatePairData,
    BasisHilbertSchmidtPairData.boundedSandwich] using
    (tsum_normSq_precomp_le globalBasis globalBasis globalBasis
      (sourceProlateHilbertSchmidtFactor lambda) (detectorOperator owner)
      hfactor)

/-- The detector costs its operator norm squared on the reverse prolate
pair's left energy. -/
theorem prolateReversePairData_left_basisEnergy_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (∑' i, ‖(prolateReversePairData owner lambda globalBasis hfactor).left
        (globalBasis i)‖ ^ 2) ≤
      ‖detectorOperator owner‖ ^ 2 *
        ∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
          (globalBasis i)‖ ^ 2 := by
  have hbound := tsum_normSq_precomp_le globalBasis globalBasis globalBasis
    (sourceProlateHilbertSchmidtFactor lambda) (detectorOperator owner).adjoint
    hfactor
  rw [ContinuousLinearMap.adjoint.norm_map] at hbound
  simpa only [prolateReversePairData, sourceProlatePairData,
    BasisHilbertSchmidtPairData.boundedSandwich] using hbound

/-- The reverse prolate pair's right energy is the fixed prolate-factor
energy up to the identity contraction. -/
theorem prolateReversePairData_right_basisEnergy_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (∑' i, ‖(prolateReversePairData owner lambda globalBasis hfactor).right
        (globalBasis i)‖ ^ 2) ≤
      ∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
        (globalBasis i)‖ ^ 2 := by
  exact boundedSandwich_right_tsum_le_of_norm_le_one globalBasis
    (sourceProlatePairData globalBasis lambda hfactor)
    (detectorOperator owner) (ContinuousLinearMap.id ℂ finiteSCarrier)
    norm_id_finiteSCarrier_le_one

/-- Both orientations of the prolate commutator are recombined before its
left energy is bounded. -/
theorem prolateCommutatorPairData_left_basisEnergy_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (∑' i, ‖(prolateCommutatorPairData' owner lambda globalBasis hfactor).left
        (globalBasis i)‖ ^ 2) ≤
      (1 + ‖detectorOperator owner‖ ^ 2) *
        ∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
          (globalBasis i)‖ ^ 2 := by
  have hforward := prolateForwardPairData_left_basisEnergy_le owner lambda
    globalBasis hfactor
  have hreverse := prolateReversePairData_left_basisEnergy_le owner lambda
    globalBasis hfactor
  rw [prolateCommutatorPairData', l2Sum_left_basisEnergy_eq_add]
  calc
    _ ≤ (∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
          (globalBasis i)‖ ^ 2) +
        ‖detectorOperator owner‖ ^ 2 *
          ∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
            (globalBasis i)‖ ^ 2 := by
      simpa only [BasisHilbertSchmidtPairData.smulRight] using
        add_le_add hforward hreverse
    _ = (1 + ‖detectorOperator owner‖ ^ 2) *
        ∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
          (globalBasis i)‖ ^ 2 := by ring

/-- Both orientations of the prolate commutator are recombined before its
right energy is bounded. -/
theorem prolateCommutatorPairData_right_basisEnergy_le
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (∑' i, ‖(prolateCommutatorPairData' owner lambda globalBasis hfactor).right
        (globalBasis i)‖ ^ 2) ≤
      (1 + ‖detectorOperator owner‖ ^ 2) *
        ∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
          (globalBasis i)‖ ^ 2 := by
  have hforward := prolateForwardPairData_right_basisEnergy_le owner lambda
    globalBasis hfactor
  have hreverse := prolateReversePairData_right_basisEnergy_le owner lambda
    globalBasis hfactor
  rw [prolateCommutatorPairData', l2Sum_right_basisEnergy_eq_add]
  calc
    _ ≤ ‖detectorOperator owner‖ ^ 2 *
          ∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
            (globalBasis i)‖ ^ 2 +
        ∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
          (globalBasis i)‖ ^ 2 := by
      simpa only [BasisHilbertSchmidtPairData.smulRight,
        ContinuousLinearMap.smul_apply, norm_smul, norm_neg, norm_one,
        one_mul, mul_pow] using add_le_add hforward hreverse
    _ = (1 + ‖detectorOperator owner‖ ^ 2) *
        ∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
          (globalBasis i)‖ ^ 2 := by ring

noncomputable def fixedPhysicalEnergyMajorant
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (a c : ℝ)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier) : ℝ :=
  6 * ((c - a) ^ 2 *
      SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) +
    (1 + ‖detectorOperator owner‖ ^ 2) *
      ∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
        (globalBasis i)‖ ^ 2

set_option maxHeartbeats 1000000 in
-- Expanding the nested physical `L2` sum creates a large concrete pair type.
/-- The left energy of the complete fixed three-branch pair has one explicit
majorant independent of the finite visible prime family. -/
theorem sourceThreeBranchPairData_left_basisEnergy_le_fixedMajorant
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
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (∑' i, ‖(sourceThreeBranchPairData owner lambda a c hac hsupp
        negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor).left
        (globalBasis i)‖ ^ 2) ≤
      fixedPhysicalEnergyMajorant owner lambda a c globalBasis := by
  let P := (c - a) ^ 2 *
    SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2
  let Q := (1 + ‖detectorOperator owner‖ ^ 2) *
    ∑' i, ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2
  have hOuter :=
    outerCommutatorPairData_left_basisEnergy_le_supportPolynomial owner lambda
      a c hac hsupp negativeBasis positiveBasis outputBasis globalBasis
  have hReflected :=
    reflectedOuterCommutatorPairData_left_basisEnergy_le_supportPolynomial
      owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
      globalBasis
  have hSecond :=
    secondSupportCommutatorPairData_left_basisEnergy_le_supportPolynomial
      owner lambda a c hac hsupp reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis
  have hProlate := prolateCommutatorPairData_left_basisEnergy_le owner lambda
    globalBasis hfactor
  rw [sourceThreeBranchPairData, l2Sum_left_basisEnergy_eq_add,
    l2Sum_left_basisEnergy_eq_add, secondSupportProlateRemainderPairData,
    l2Sum_left_basisEnergy_eq_add]
  calc
    _ ≤ 2 * P + 2 * P + (2 * P + Q) := by
      simpa only [BasisHilbertSchmidtPairData.smulRight, P, Q] using
        add_le_add (add_le_add hOuter hReflected)
          (add_le_add hSecond hProlate)
    _ = fixedPhysicalEnergyMajorant owner lambda a c globalBasis := by
      unfold fixedPhysicalEnergyMajorant P Q
      ring

set_option maxHeartbeats 1000000 in
-- Expanding the nested physical `L2` sum creates a large concrete pair type.
/-- The right energy of the complete fixed three-branch pair has the same
finite-family-independent majorant. -/
theorem sourceThreeBranchPairData_right_basisEnergy_le_fixedMajorant
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
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    (∑' i, ‖(sourceThreeBranchPairData owner lambda a c hac hsupp
        negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor).right
        (globalBasis i)‖ ^ 2) ≤
      fixedPhysicalEnergyMajorant owner lambda a c globalBasis := by
  let P := (c - a) ^ 2 *
    SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2
  let Q := (1 + ‖detectorOperator owner‖ ^ 2) *
    ∑' i, ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2
  have hOuter :=
    outerCommutatorPairData_right_basisEnergy_le_supportPolynomial owner lambda
      a c hac hsupp negativeBasis positiveBasis outputBasis globalBasis
  have hReflected :=
    reflectedOuterCommutatorPairData_right_basisEnergy_le_supportPolynomial
      owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
      globalBasis
  have hSecond :=
    secondSupportCommutatorPairData_right_basisEnergy_le_supportPolynomial
      owner lambda a c hac hsupp reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis
  have hProlate := prolateCommutatorPairData_right_basisEnergy_le owner lambda
    globalBasis hfactor
  rw [sourceThreeBranchPairData, l2Sum_right_basisEnergy_eq_add,
    l2Sum_right_basisEnergy_eq_add, secondSupportProlateRemainderPairData,
    l2Sum_right_basisEnergy_eq_add]
  calc
    _ ≤ 2 * P + 2 * P + (2 * P + Q) := by
      simpa only [BasisHilbertSchmidtPairData.smulRight,
        ContinuousLinearMap.smul_apply, norm_smul, norm_neg, norm_one,
        one_mul, mul_pow, P, Q] using
        add_le_add (add_le_add hOuter hReflected)
          (add_le_add hSecond hProlate)
    _ = fixedPhysicalEnergyMajorant owner lambda a c globalBasis := by
      unfold fixedPhysicalEnergyMajorant P Q
      ring

set_option maxHeartbeats 2000000 in
-- The complete concrete trace statement contains all physical basis carriers.
/-- The complete finite-Euler trace obeys the explicit fixed physical energy
majorant, uniformly in the visible finite prime family. -/
theorem sourceRootCompletedFiniteEulerTrace_norm_le_fixedPhysicalMajorant
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
    ‖ordinaryTraceAlong globalBasis
        (sourceRootCompletedFixedQuotientCorner owner lambda
          (radialSupportProjection lambda ∘L
            normalizedFiniteEulerInverse family ∘L
            radialSupportProjection lambda))‖ ≤
      fixedPhysicalEnergyMajorant owner lambda a c globalBasis := by
  let fixedPair := sourceThreeBranchPairData owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
  let M := fixedPhysicalEnergyMajorant owner lambda a c globalBasis
  have htrace :=
    sourceRootCompletedFiniteEulerTrace_norm_le_fixedPhysicalGeometricEnergy
      owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis hfactor
  have hleft := sourceThreeBranchPairData_left_basisEnergy_le_fixedMajorant
    owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis hfactor
  have hright := sourceThreeBranchPairData_right_basisEnergy_le_fixedMajorant
    owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis hfactor
  have hM : 0 ≤ M := by
    unfold M fixedPhysicalEnergyMajorant
    positivity
  calc
    _ ≤ Real.sqrt (∑' i, ‖fixedPair.left (globalBasis i)‖ ^ 2) *
        Real.sqrt (∑' i, ‖fixedPair.right (globalBasis i)‖ ^ 2) := htrace
    _ ≤ Real.sqrt M * Real.sqrt M :=
      mul_le_mul (Real.sqrt_le_sqrt hleft) (Real.sqrt_le_sqrt hright)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = M := by
      rw [← pow_two, Real.sq_sqrt hM]

end CCM24FiniteSFixedPhysicalEnergyBound
end CCM25Concrete
end Source
end ConnesWeilRH
