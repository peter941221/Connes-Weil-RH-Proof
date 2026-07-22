/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSRootConvolutionNorm
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualBandFirstJetTrace

/-!
# Support bound for the actual paired finite-Euler first jet

The homogeneous physical estimate is first made stable under arbitrary
contractive left and right sandwiches.  The actual paired first jet is then
the sum of its two causal orientations, each of which is one such sandwich.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSActualFirstJetSupportBound

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSProjectionTrace
open CCM24FiniteSInverseMetric
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSFixedQuotientCarrier
open CCM24FiniteSFixedQuotientContractionBound
open CCM24FiniteSRootCompletedFirstJet
open CCM24SourceProlateTrace
open CCM24FiniteSBandTrace
open CCM24FiniteSPhysicalBoundaryEnergy
open CCM24FiniteSProlateCommutatorTraceBound
open CCM24FiniteSHomogeneousPhysicalEnergyBound
open CCM24FiniteSRootConvolutionNorm
open CCM24FiniteSActualBandFirstJetTrace
open CCM24FiniteSTwoSidedRootRecombination

private noncomputable def chooseHilbertBasisIndex
    (G : Type*) [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] : Set G :=
  Classical.choose (exists_hilbertBasis ℂ G)

private noncomputable def chooseHilbertBasis
    (G : Type*) [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] : HilbertBasis (chooseHilbertBasisIndex G) ℂ G :=
  Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ G))

private theorem boundedSandwich_trace_norm_le_basisEnergy
    {ι κ H G : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    {sourceBasis : HilbertBasis ι ℂ H}
    (targetBasis : HilbertBasis κ ℂ G)
    (data : BasisHilbertSchmidtPairData (G := G) sourceBasis)
    (leftBounded rightBounded : H →L[ℂ] H)
    (hleft : ‖leftBounded‖ ≤ 1) (hright : ‖rightBounded‖ ≤ 1)
    (leftEnergy rightEnergy : ℝ)
    (hleftEnergy : (∑' i, ‖data.left (sourceBasis i)‖ ^ 2) ≤ leftEnergy)
    (hrightEnergy : (∑' i, ‖data.right (sourceBasis i)‖ ^ 2) ≤ rightEnergy) :
    ‖ordinaryTraceAlong sourceBasis
        (data.boundedSandwich targetBasis leftBounded rightBounded).traceProduct‖ ≤
      Real.sqrt leftEnergy * Real.sqrt rightEnergy := by
  have hleft' := boundedSandwich_left_tsum_le_of_norm_le_one targetBasis data
    leftBounded rightBounded hleft
  have hright' := boundedSandwich_right_tsum_le_of_norm_le_one targetBasis data
    leftBounded rightBounded hright
  calc
    _ ≤ Real.sqrt (∑' i,
        ‖(data.boundedSandwich targetBasis leftBounded rightBounded).left
          (sourceBasis i)‖ ^ 2) *
        Real.sqrt (∑' i,
          ‖(data.boundedSandwich targetBasis leftBounded rightBounded).right
            (sourceBasis i)‖ ^ 2) :=
      ordinaryTraceAlong_traceProduct_norm_le_geometricEnergy _
    _ ≤ Real.sqrt leftEnergy * Real.sqrt rightEnergy := by
      exact mul_le_mul (Real.sqrt_le_sqrt (hleft'.trans hleftEnergy))
        (Real.sqrt_le_sqrt (hright'.trans hrightEnergy))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- Every bounded sandwich of the fixed physical commutator has a genuine
trace-class owner. -/
theorem fixedPhysicalCommutator_boundedSandwich_isTraceClassAlong
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
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
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (leftBounded rightBounded : finiteSCarrier →L[ℂ] finiteSCarrier) :
    IsTraceClassAlong globalBasis
      (leftBounded ∘L
        fixedPhysicalCommutator (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda)
          (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
        rightBounded) := by
  let data := fixedPhysicalPairData owner lambda a c hac hsupp negativeBasis
    positiveBasis outputBasis reflectedNegativeBasis reflectedPositiveBasis
    reflectedOutputBasis globalBasis boundaryBasis hfactor
  have hclass :=
    (data.boundedSandwich boundaryBasis leftBounded rightBounded)
      |>.traceProduct_isTraceClassAlong
  rw [BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq] at hclass
  have hdata : data.traceProduct =
      fixedPhysicalCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner) := by
    dsimp only [data]
    exact fixedPhysicalPairData_traceProduct_eq owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis boundaryBasis
      hfactor (radialSupportProjection_isStarProjection lambda).isIdempotentElem
      (radialSupportProjection_comp_sourceProlateRemainder lambda)
      (sourceProlateRemainder_comp_radialSupportProjection lambda)
  rw [hdata] at hclass
  exact hclass

set_option maxHeartbeats 3000000 in
-- The signed four-branch expansion is retained until each complete sandwich
-- has its trace bound; this elaborates the nested Hilbert--Schmidt pair types.
/-- Contractive sandwiches preserve the homogeneous physical-energy bound. -/
theorem fixedPhysicalCommutator_boundedSandwich_trace_norm_le_homogeneousEnergy
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
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
    (_boundaryBasis : HilbertBasis μ ℂ (commonBoundaryCarrier a c))
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (leftBounded rightBounded : finiteSCarrier →L[ℂ] finiteSCarrier)
    (hleft : ‖leftBounded‖ ≤ 1) (hright : ‖rightBounded‖ ≤ 1) :
    ‖ordinaryTraceAlong globalBasis
        (leftBounded ∘L
          fixedPhysicalCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
          rightBounded)‖ ≤
      6 * ((c - a) ^ 2 *
        SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) +
        2 * ‖detectorOperator owner‖ *
          (∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
            (globalBasis i)‖ ^ 2) := by
  let P := (c - a) ^ 2 *
    SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2
  let H := ∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
    (globalBasis i)‖ ^ 2
  let E := radialSupportProjection lambda
  let L := leftBounded ∘L E
  let R := E ∘L rightBounded
  let outer := outerCommutatorPairData owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis globalBasis
  let reflected := reflectedOuterCommutatorPairData owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis globalBasis
  let second := secondSupportCommutatorPairData owner lambda a c hac hsupp
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis globalBasis
  let outerTargetBasis := chooseHilbertBasis (WithLp 2
    (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c)) ×
      Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c))))
  let secondTargetBasis := chooseHilbertBasis (WithLp 2
    (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a))) ×
      Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a)))))
  have hP : 0 ≤ P := by
    dsimp [P]
    positivity
  have hE : ‖E‖ ≤ 1 := by
    dsimp [E]
    exact IsStarProjection.norm_le _
      (radialSupportProjection_isStarProjection lambda)
  have hL : ‖L‖ ≤ 1 := by
    dsimp [L]
    calc
      _ ≤ ‖leftBounded‖ * ‖E‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul hleft hE (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul _
  have hR : ‖R‖ ≤ 1 := by
    dsimp [R]
    calc
      _ ≤ ‖E‖ * ‖rightBounded‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul hE hright (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul _
  have hOuterLeft := outerCommutatorPairData_left_basisEnergy_le_supportPolynomial
    owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis globalBasis
  have hOuterRight := outerCommutatorPairData_right_basisEnergy_le_supportPolynomial
    owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis globalBasis
  have hReflectedLeft :=
    reflectedOuterCommutatorPairData_left_basisEnergy_le_supportPolynomial
      owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis globalBasis
  have hReflectedRight :=
    reflectedOuterCommutatorPairData_right_basisEnergy_le_supportPolynomial
      owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis globalBasis
  have hSecondLeft := secondSupportCommutatorPairData_left_basisEnergy_le_supportPolynomial
    owner lambda a c hac hsupp reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis
  have hSecondRight := secondSupportCommutatorPairData_right_basisEnergy_le_supportPolynomial
    owner lambda a c hac hsupp reflectedNegativeBasis reflectedPositiveBasis
      reflectedOutputBasis globalBasis
  have hOuterLeft' :
      (∑' i, ‖outer.left (globalBasis i)‖ ^ 2) ≤ 2 * P := by
    simpa only [outer, P] using hOuterLeft
  have hOuterRight' :
      (∑' i, ‖outer.right (globalBasis i)‖ ^ 2) ≤ 2 * P := by
    simpa only [outer, P] using hOuterRight
  have hReflectedLeft' :
      (∑' i, ‖reflected.left (globalBasis i)‖ ^ 2) ≤ 2 * P := by
    simpa only [reflected, P] using hReflectedLeft
  have hReflectedRight' :
      (∑' i, ‖reflected.right (globalBasis i)‖ ^ 2) ≤ 2 * P := by
    simpa only [reflected, P] using hReflectedRight
  have hSecondLeft' :
      (∑' i, ‖second.left (globalBasis i)‖ ^ 2) ≤ 2 * P := by
    simpa only [second, P] using hSecondLeft
  have hSecondRight' :
      (∑' i, ‖second.right (globalBasis i)‖ ^ 2) ≤ 2 * P := by
    simpa only [second, P] using hSecondRight
  have hOuter := boundedSandwich_trace_norm_le_basisEnergy
    (sourceBasis := globalBasis) outerTargetBasis outer L R hL hR
    (2 * P) (2 * P) hOuterLeft' hOuterRight'
  have hReflected := boundedSandwich_trace_norm_le_basisEnergy
    (sourceBasis := globalBasis) outerTargetBasis reflected L R hL hR
    (2 * P) (2 * P) hReflectedLeft' hReflectedRight'
  have hSecond := boundedSandwich_trace_norm_le_basisEnergy
    (sourceBasis := globalBasis) secondTargetBasis second L R hL hR
    (2 * P) (2 * P) hSecondLeft' hSecondRight'
  have hProlate :=
    sourceProlateCommutator_boundedSandwich_trace_norm_le_detector_factorEnergy
      owner lambda globalBasis hfactor L R hL hR
  have hOuter' :
      ‖ordinaryTraceAlong globalBasis
          (L ∘L outer.traceProduct ∘L R)‖ ≤ 2 * P := by
    calc
      _ = ‖ordinaryTraceAlong globalBasis
          (outer.boundedSandwich outerTargetBasis L R).traceProduct‖ := by
        rw [BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq]
      _ ≤ Real.sqrt (2 * P) * Real.sqrt (2 * P) := hOuter
      _ = 2 * P := by
        rw [← pow_two, Real.sq_sqrt (by positivity : 0 ≤ 2 * P)]
  have hReflected' :
      ‖ordinaryTraceAlong globalBasis
          (L ∘L reflected.traceProduct ∘L R)‖ ≤ 2 * P := by
    calc
      _ = ‖ordinaryTraceAlong globalBasis
          (reflected.boundedSandwich outerTargetBasis L R).traceProduct‖ := by
        rw [BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq]
      _ ≤ Real.sqrt (2 * P) * Real.sqrt (2 * P) := hReflected
      _ = 2 * P := by
        rw [← pow_two, Real.sq_sqrt (by positivity : 0 ≤ 2 * P)]
  have hSecond' :
      ‖ordinaryTraceAlong globalBasis
          (L ∘L second.traceProduct ∘L R)‖ ≤ 2 * P := by
    calc
      _ = ‖ordinaryTraceAlong globalBasis
          (second.boundedSandwich secondTargetBasis L R).traceProduct‖ := by
        rw [BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq]
      _ ≤ Real.sqrt (2 * P) * Real.sqrt (2 * P) := hSecond
      _ = 2 * P := by
        rw [← pow_two, Real.sq_sqrt (by positivity : 0 ≤ 2 * P)]
  have hdecomp :
      leftBounded ∘L
          fixedPhysicalCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
          rightBounded =
        -(L ∘L outer.traceProduct ∘L R) -
          (L ∘L reflected.traceProduct ∘L R) -
          (L ∘L second.traceProduct ∘L R) +
          (L ∘L cc20Commutator (sourceProlateRemainder lambda)
            (detectorOperator owner) ∘L R) := by
    rw [fixedPhysicalCommutator_eq_neg_compressedThreeBranch
      (radialSupportProjection lambda)
      (sourceFourierSupportProjection lambda)
      (sourceProlateRemainder lambda) (detectorOperator owner)
      (radialSupportProjection_isStarProjection lambda).isIdempotentElem
      (radialSupportProjection_comp_sourceProlateRemainder lambda)
      (sourceProlateRemainder_comp_radialSupportProjection lambda)]
    rw [← sourceThreeBranchPairData_traceProduct_eq owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor]
    rw [sourceThreeBranchPairData,
      BasisHilbertSchmidtPairData.l2Sum_traceProduct_eq_add,
      BasisHilbertSchmidtPairData.l2Sum_traceProduct_eq_add,
      outerCommutatorPairData_traceProduct_eq owner lambda a c hac hsupp
        negativeBasis positiveBasis outputBasis globalBasis,
      reflectedOuterCommutatorPairData_traceProduct_eq owner lambda a c hac
        hsupp negativeBasis positiveBasis outputBasis globalBasis,
      secondSupportProlateRemainderPairData_traceProduct_eq owner lambda a c
        hac hsupp reflectedNegativeBasis reflectedPositiveBasis
        reflectedOutputBasis globalBasis hfactor,
      secondSupportCommutatorPairData_traceProduct_eq owner lambda a c hac
        hsupp reflectedNegativeBasis reflectedPositiveBasis
        reflectedOutputBasis globalBasis]
    dsimp only [outer, reflected, second, L, R, E]
    unfold CCM24RadialBoundaryPairTransport.sourceSecondSupportProlateRemainder
    simp only [cc20ProlateCommutatorBranch,
      ← ContinuousLinearMap.mul_def]
    noncomm_ring
  let prolateTargetBasis :=
    chooseHilbertBasis (WithLp 2 (finiteSCarrier × finiteSCarrier))
  let prolatePair :=
    (prolateCommutatorPairData' owner lambda globalBasis hfactor).boundedSandwich
      prolateTargetBasis L R
  have hOuterClass :
      IsTraceClassAlong globalBasis (L ∘L outer.traceProduct ∘L R) := by
    have hclass :=
      (outer.boundedSandwich outerTargetBasis L R).traceProduct_isTraceClassAlong
    rw [BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq] at hclass
    exact hclass
  have hReflectedClass :
      IsTraceClassAlong globalBasis (L ∘L reflected.traceProduct ∘L R) := by
    have hclass :=
      (reflected.boundedSandwich outerTargetBasis L R)
        |>.traceProduct_isTraceClassAlong
    rw [BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq] at hclass
    exact hclass
  have hSecondClass :
      IsTraceClassAlong globalBasis (L ∘L second.traceProduct ∘L R) := by
    have hclass :=
      (second.boundedSandwich secondTargetBasis L R)
        |>.traceProduct_isTraceClassAlong
    rw [BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq] at hclass
    exact hclass
  have hProlateClass : IsTraceClassAlong globalBasis
      (L ∘L cc20Commutator (sourceProlateRemainder lambda)
        (detectorOperator owner) ∘L R) := by
    have hclass := prolatePair.traceProduct_isTraceClassAlong
    rw [BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq,
      prolateCommutatorPairData'_traceProduct_eq] at hclass
    exact hclass
  have htrace :
      ordinaryTraceAlong globalBasis
          (leftBounded ∘L
            fixedPhysicalCommutator (radialSupportProjection lambda)
              (sourceFourierSupportProjection lambda)
              (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
            rightBounded) =
        -ordinaryTraceAlong globalBasis (L ∘L outer.traceProduct ∘L R) -
          ordinaryTraceAlong globalBasis (L ∘L reflected.traceProduct ∘L R) -
          ordinaryTraceAlong globalBasis (L ∘L second.traceProduct ∘L R) +
          ordinaryTraceAlong globalBasis
            (L ∘L cc20Commutator (sourceProlateRemainder lambda)
              (detectorOperator owner) ∘L R) := by
    rw [hdecomp]
    rw [ordinaryTraceAlong_add globalBasis _ _
        (CCM24FiniteSProjectionTrace.PositiveTrace.isTraceClassAlong_sub
          globalBasis _ _
          (CCM24FiniteSProjectionTrace.PositiveTrace.isTraceClassAlong_sub
            globalBasis _ _
            (CCM24FiniteSProjectionTrace.PositiveTrace.isTraceClassAlong_neg
              globalBasis _ hOuterClass) hReflectedClass) hSecondClass)
      hProlateClass]
    rw [CCM24FiniteSProjectionTrace.PositiveTrace.ordinaryTraceAlong_sub
      globalBasis _ _
      (CCM24FiniteSProjectionTrace.PositiveTrace.isTraceClassAlong_sub
        globalBasis _ _
        (CCM24FiniteSProjectionTrace.PositiveTrace.isTraceClassAlong_neg
          globalBasis _ hOuterClass) hReflectedClass) hSecondClass]
    rw [CCM24FiniteSProjectionTrace.PositiveTrace.ordinaryTraceAlong_sub
      globalBasis _ _
      (CCM24FiniteSProjectionTrace.PositiveTrace.isTraceClassAlong_neg
        globalBasis _ hOuterClass) hReflectedClass]
    rw [CCM24FiniteSProjectionTrace.PositiveTrace.ordinaryTraceAlong_neg]
  rw [htrace]
  calc
    _ ≤
      (‖ordinaryTraceAlong globalBasis (L ∘L outer.traceProduct ∘L R)‖ +
        ‖ordinaryTraceAlong globalBasis (L ∘L reflected.traceProduct ∘L R)‖) +
        ‖ordinaryTraceAlong globalBasis (L ∘L second.traceProduct ∘L R)‖ +
        ‖ordinaryTraceAlong globalBasis
          (L ∘L cc20Commutator (sourceProlateRemainder lambda)
            (detectorOperator owner) ∘L R)‖ := by
      calc
        _ ≤ ‖-ordinaryTraceAlong globalBasis
              (L ∘L outer.traceProduct ∘L R) -
              ordinaryTraceAlong globalBasis
                (L ∘L reflected.traceProduct ∘L R) -
              ordinaryTraceAlong globalBasis
                (L ∘L second.traceProduct ∘L R)‖ +
            ‖ordinaryTraceAlong globalBasis
              (L ∘L cc20Commutator (sourceProlateRemainder lambda)
                (detectorOperator owner) ∘L R)‖ := norm_add_le _ _
        _ ≤ _ := by
          apply add_le_add
          · calc
              _ ≤ ‖-ordinaryTraceAlong globalBasis
                    (L ∘L outer.traceProduct ∘L R) -
                    ordinaryTraceAlong globalBasis
                      (L ∘L reflected.traceProduct ∘L R)‖ +
                  ‖ordinaryTraceAlong globalBasis
                    (L ∘L second.traceProduct ∘L R)‖ := norm_sub_le _ _
              _ ≤ _ := by
                calc
                  _ ≤ (‖-ordinaryTraceAlong globalBasis
                          (L ∘L outer.traceProduct ∘L R)‖ +
                        ‖ordinaryTraceAlong globalBasis
                          (L ∘L reflected.traceProduct ∘L R)‖) +
                      ‖ordinaryTraceAlong globalBasis
                        (L ∘L second.traceProduct ∘L R)‖ :=
                    add_le_add (norm_sub_le _ _) (le_refl _)
                  _ = _ := by rw [norm_neg]
          · rfl
    _ ≤ 2 * P + 2 * P + 2 * P +
        2 * ‖detectorOperator owner‖ * H := by
      exact add_le_add (add_le_add (add_le_add hOuter' hReflected') hSecond')
        hProlate
    _ = 6 * ((c - a) ^ 2 *
        SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) +
        2 * ‖detectorOperator owner‖ *
          (∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
            (globalBasis i)‖ ^ 2) := by
      dsimp only [P, H]
      ring

/-- The contractive sandwich bound with the detector norm reduced to compact
root support. -/
theorem fixedPhysicalCommutator_boundedSandwich_trace_norm_le_supportEnergy
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
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
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (leftBounded rightBounded : finiteSCarrier →L[ℂ] finiteSCarrier)
    (hleft : ‖leftBounded‖ ≤ 1) (hright : ‖rightBounded‖ ≤ 1) :
    ‖ordinaryTraceAlong globalBasis
        (leftBounded ∘L
          fixedPhysicalCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
          rightBounded)‖ ≤
      (6 + 2 * (∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
          (globalBasis i)‖ ^ 2)) *
        ((c - a) ^ 2 *
          SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) := by
  let P := (c - a) ^ 2 *
    SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2
  let H := ∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
    (globalBasis i)‖ ^ 2
  have hH : 0 ≤ H := by
    dsimp [H]
    exact tsum_nonneg fun i => sq_nonneg _
  have hroot := rootConvolution_norm_le_supportLength_mul_seminorm
    owner a c hac hsupp
  have hrootSq : ‖rootConvolution owner‖ ^ 2 ≤ P := by
    have hsquare :=
      (sq_le_sq₀ (norm_nonneg _)
        (by positivity :
          0 ≤ (c - a) * SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test)).2
        hroot
    simpa only [P, mul_pow] using hsquare
  have hdetector :=
    fixedPhysicalCommutator_boundedSandwich_trace_norm_le_homogeneousEnergy
      owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis hfactor leftBounded rightBounded hleft hright
  have hdetectorRoot := detectorOperator_norm_le_rootConvolution_sq owner
  calc
    _ ≤ 6 * P + 2 * ‖detectorOperator owner‖ * H := by
      simpa only [P, H] using hdetector
    _ ≤ 6 * P + 2 * ‖rootConvolution owner‖ ^ 2 * H := by
      exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hdetectorRoot
          (by norm_num : (0 : ℝ) ≤ 2)) hH)
    _ ≤ 6 * P + 2 * P * H := by
      exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hrootSq
          (by norm_num : (0 : ℝ) ≤ 2)) hH)
    _ = (6 + 2 * H) * P := by ring
    _ = (6 + 2 * (∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
          (globalBasis i)‖ ^ 2)) *
        ((c - a) ^ 2 *
          SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) := by
      rfl

set_option maxHeartbeats 3000000 in
-- Both causal orientations are expanded through the same fixed physical
-- commutator; no infinite-dimensional trace cycle is used.
/-- The actual paired finite-Euler first jet has a family-uniform support
bound. -/
theorem sourceActualBandFiniteEulerPairedTrace_norm_le_supportEnergy
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
        (sourceActualBandFiniteEulerPairedResponse owner lambda family)‖ ≤
      (12 + 4 * (∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
          (globalBasis i)‖ ^ 2)) *
        ((c - a) ^ 2 *
          SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) := by
  let B := sourceBandProjection lambda
  let R := sourceSoninProjection lambda
  let A := normalizedFiniteEulerInverse family
  let Aadj := A.adjoint
  let F := fixedPhysicalCommutator (radialSupportProjection lambda)
    (sourceFourierSupportProjection lambda) (sourceProlateRemainder lambda)
    (detectorOperator owner)
  let leftForward := R
  let rightForward := B ∘L A ∘L R
  let leftReverse := R ∘L Aadj ∘L B
  let rightReverse := R
  let K := (6 + 2 * (∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
    (globalBasis i)‖ ^ 2)) *
      ((c - a) ^ 2 *
        SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2)
  have hB : ‖B‖ ≤ 1 := by
    dsimp [B]
    exact IsStarProjection.norm_le _ (sourceBandProjection_isStarProjection lambda)
  have hR : ‖R‖ ≤ 1 := by
    dsimp [R]
    exact IsStarProjection.norm_le _ (sourceSoninProjection_isStarProjection lambda)
  have hA : ‖A‖ ≤ 1 := by
    dsimp [A]
    exact norm_normalizedFiniteEulerInverse_le_one family
  have hAadj : ‖Aadj‖ ≤ 1 := by
    dsimp [Aadj]
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact hA
  have hrightForward : ‖rightForward‖ ≤ 1 := by
    dsimp [rightForward]
    calc
      _ ≤ ‖B ∘L A‖ * ‖R‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := by
        apply mul_le_mul
        · calc
            _ ≤ ‖B‖ * ‖A‖ := ContinuousLinearMap.opNorm_comp_le _ _
            _ ≤ 1 * 1 := mul_le_mul hB hA (norm_nonneg _) (by norm_num)
            _ = 1 := one_mul _
        · exact hR
        · exact norm_nonneg _
        · norm_num
      _ = 1 := one_mul _
  have hleftReverse : ‖leftReverse‖ ≤ 1 := by
    dsimp [leftReverse]
    calc
      _ ≤ ‖R ∘L Aadj‖ * ‖B‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := by
        apply mul_le_mul
        · calc
            _ ≤ ‖R‖ * ‖Aadj‖ := ContinuousLinearMap.opNorm_comp_le _ _
            _ ≤ 1 * 1 := mul_le_mul hR hAadj (norm_nonneg _) (by norm_num)
            _ = 1 := one_mul _
        · exact hB
        · exact norm_nonneg _
        · norm_num
      _ = 1 := one_mul _
  have hdecomp :
      sourceActualBandFiniteEulerPairedResponse owner lambda family =
        -(leftForward ∘L F ∘L rightForward) +
          (leftReverse ∘L F ∘L rightReverse) := by
    rw [sourceActualBandFiniteEulerPairedResponse]
    rw [← actualBandCommutatorPairedResponse_eq_detector B R
      (compressedDetector (radialSupportProjection lambda)
        (detectorOperator owner)) A Aadj
      (sourceSoninProjection_isStarProjection lambda).isIdempotentElem
      (by simpa only [B, R, ContinuousLinearMap.mul_def] using
        sourceBandProjection_comp_sourceSoninProjection_eq_zero lambda)
      (by simpa only [B, R, ContinuousLinearMap.mul_def] using
        sourceSoninProjection_comp_sourceBandProjection_eq_zero lambda)]
    unfold actualBandCommutatorPairedResponse
    rw [← fixedPhysicalCommutator_eq_sourceCompressedCommutator owner lambda]
    rfl
  have hForwardClass :=
    fixedPhysicalCommutator_boundedSandwich_isTraceClassAlong owner lambda
      a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis hfactor leftForward rightForward
  have hReverseClass :=
    fixedPhysicalCommutator_boundedSandwich_isTraceClassAlong owner lambda
      a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis hfactor leftReverse rightReverse
  have hForward :=
    fixedPhysicalCommutator_boundedSandwich_trace_norm_le_supportEnergy
      owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis hfactor leftForward rightForward hR hrightForward
  have hReverse :=
    fixedPhysicalCommutator_boundedSandwich_trace_norm_le_supportEnergy
      owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis hfactor leftReverse rightReverse hleftReverse hR
  have htrace :
      ordinaryTraceAlong globalBasis
          (sourceActualBandFiniteEulerPairedResponse owner lambda family) =
        -ordinaryTraceAlong globalBasis
            (leftForward ∘L F ∘L rightForward) +
          ordinaryTraceAlong globalBasis
            (leftReverse ∘L F ∘L rightReverse) := by
    rw [hdecomp]
    rw [ordinaryTraceAlong_add globalBasis _ _
      (CCM24FiniteSProjectionTrace.PositiveTrace.isTraceClassAlong_neg
        globalBasis _ hForwardClass) hReverseClass]
    rw [CCM24FiniteSProjectionTrace.PositiveTrace.ordinaryTraceAlong_neg]
  rw [htrace]
  calc
    _ ≤ ‖ordinaryTraceAlong globalBasis
          (leftForward ∘L F ∘L rightForward)‖ +
        ‖ordinaryTraceAlong globalBasis
          (leftReverse ∘L F ∘L rightReverse)‖ := by
      simpa only [norm_neg] using norm_add_le
        (-ordinaryTraceAlong globalBasis
          (leftForward ∘L F ∘L rightForward))
        (ordinaryTraceAlong globalBasis
          (leftReverse ∘L F ∘L rightReverse))
    _ ≤ K + K := add_le_add hForward hReverse
    _ = (12 + 4 * (∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
          (globalBasis i)‖ ^ 2)) *
        ((c - a) ^ 2 *
          SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) := by
      dsimp only [K]
      ring

end CCM24FiniteSActualFirstJetSupportBound
end CCM25Concrete
end Source
end ConnesWeilRH
