/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSProlateCommutatorTraceBound

/-!
# Homogeneous physical energy for the completed finite-Euler corner

The complete corner is expanded only at the trace-product level.  The three
compact boundary branches keep their support energy, while the prolate branch
uses the homogeneous bounded-sandwich commutator estimate.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSHomogeneousPhysicalEnergyBound

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSProjectionTrace
open CCM24FiniteSInverseMetric
open CCM24FiniteSFixedQuotientCarrier
open CCM24FiniteSFixedQuotientContractionBound
open CCM24FiniteSCommonBoundaryPair
open CCM24SourceProlateTrace
open CCM24FiniteSRootCompletedFirstJet
open CCM24FiniteSRootCompletedDetectorRenewalRootPairing
open CCM24FiniteSBandTrace
open CCM24FiniteSPhysicalBoundaryEnergy
open CCM24FiniteSFixedPhysicalEnergyBound
open CCM24FiniteSProlateCommutatorTraceBound

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

/-! The detector norm is not an independent analytic quantity: it is the
positive square of the selected convolution root.  Keeping this reduction
explicit makes the next support/Sobolev estimate target the actual root. -/
theorem detectorOperator_norm_le_rootConvolution_sq
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) :
    ‖detectorOperator owner‖ ≤ ‖rootConvolution owner‖ ^ 2 := by
  rw [detectorOperator_eq_rootConvolution_adjoint_comp_rootConvolution]
  calc
    ‖(rootConvolution owner).adjoint ∘L rootConvolution owner‖ ≤
        ‖(rootConvolution owner).adjoint‖ * ‖rootConvolution owner‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖rootConvolution owner‖ ^ 2 := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      ring

set_option maxHeartbeats 3000000 in
-- The four-term trace decomposition expands several nested finite-S pair types.
/-- The completed finite-Euler corner has a homogeneous fixed-energy bound. -/
theorem sourceRootCompletedFiniteEulerTrace_norm_le_homogeneousPhysicalEnergy
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
      6 * ((c - a) ^ 2 *
        SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) +
        2 * ‖detectorOperator owner‖ *
          (∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
            (globalBasis i)‖ ^ 2) := by
  let P := (c - a) ^ 2 *
    SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2
  let H := ∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
    (globalBasis i)‖ ^ 2
  let B := sourceBandProjection lambda
  let R := sourceSoninProjection lambda ∘L
    normalizedFiniteEulerInverse family ∘L sourceBandProjection lambda
  let outer := outerCommutatorPairData owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis globalBasis
  let reflected := reflectedOuterCommutatorPairData owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis globalBasis
  let second := secondSupportCommutatorPairData owner lambda a c hac hsupp
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis globalBasis
  let outerTargetBasis :=
    (chooseHilbertBasis (WithLp 2
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c)) ×
        Lp ℂ 2 (volume : Measure (BoundaryOutputInterval a c)))))
  let secondTargetBasis :=
    (chooseHilbertBasis (WithLp 2
      (Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a))) ×
        Lp ℂ 2 (volume : Measure (BoundaryOutputInterval (-c) (-a))))))
  have hP : 0 ≤ P := by
    dsimp [P]
    positivity
  have hBand : ‖B‖ ≤ 1 := by
    dsimp [B]
    exact IsStarProjection.norm_le _ (sourceBandProjection_isStarProjection lambda)
  have hSonin : ‖sourceSoninProjection lambda‖ ≤ 1 :=
    IsStarProjection.norm_le _ (sourceSoninProjection_isStarProjection lambda)
  have hInverse : ‖normalizedFiniteEulerInverse family‖ ≤ 1 :=
    norm_normalizedFiniteEulerInverse_le_one family
  have hR : ‖R‖ ≤ 1 := by
    dsimp [R]
    calc
      _ ≤ ‖sourceSoninProjection lambda ∘L
          normalizedFiniteEulerInverse family‖ * ‖B‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ‖B‖ := by
        apply mul_le_mul_of_nonneg_right
        · calc
            _ ≤ ‖sourceSoninProjection lambda‖ *
                ‖normalizedFiniteEulerInverse family‖ :=
              ContinuousLinearMap.opNorm_comp_le _ _
            _ ≤ 1 * 1 :=
              mul_le_mul hSonin hInverse (norm_nonneg _) (by norm_num)
            _ = 1 := one_mul _
        · exact norm_nonneg _
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hBand (by norm_num)
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
    (sourceBasis := globalBasis) outerTargetBasis outer B R
    hBand hR (2 * P) (2 * P) hOuterLeft' hOuterRight'
  have hReflected :=
    boundedSandwich_trace_norm_le_basisEnergy (sourceBasis := globalBasis)
      outerTargetBasis reflected B R hBand hR
      (2 * P) (2 * P) hReflectedLeft' hReflectedRight'
  have hSecond := boundedSandwich_trace_norm_le_basisEnergy
    (sourceBasis := globalBasis) secondTargetBasis second B R hBand hR
      (2 * P) (2 * P) hSecondLeft' hSecondRight'
  have hProlate :=
    sourceProlateCommutator_boundedSandwich_trace_norm_le_detector_factorEnergy
      owner lambda globalBasis hfactor B R hBand hR
  have hOuter' :
      ‖ordinaryTraceAlong globalBasis
          (B ∘L outer.traceProduct ∘L R)‖ ≤ 2 * P := by
    calc
      _ = ‖ordinaryTraceAlong globalBasis
          (outer.boundedSandwich outerTargetBasis B R).traceProduct‖ := by
        rw [BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq]
      _ ≤ Real.sqrt (2 * P) * Real.sqrt (2 * P) := hOuter
      _ = 2 * P := by
        rw [← pow_two, Real.sq_sqrt (by positivity : 0 ≤ 2 * P)]
  have hReflected' :
      ‖ordinaryTraceAlong globalBasis
          (B ∘L reflected.traceProduct ∘L R)‖ ≤ 2 * P := by
    calc
      _ = ‖ordinaryTraceAlong globalBasis
          (reflected.boundedSandwich outerTargetBasis B R).traceProduct‖ := by
        rw [BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq]
      _ ≤ Real.sqrt (2 * P) * Real.sqrt (2 * P) := hReflected
      _ = 2 * P := by
        rw [← pow_two, Real.sq_sqrt (by positivity : 0 ≤ 2 * P)]
  have hSecond' :
      ‖ordinaryTraceAlong globalBasis
          (B ∘L second.traceProduct ∘L R)‖ ≤ 2 * P := by
    calc
      _ = ‖ordinaryTraceAlong globalBasis
          (second.boundedSandwich secondTargetBasis B R).traceProduct‖ := by
        rw [BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq]
      _ ≤ Real.sqrt (2 * P) * Real.sqrt (2 * P) := hSecond
      _ = 2 * P := by
        rw [← pow_two, Real.sq_sqrt (by positivity : 0 ≤ 2 * P)]
  let prolateTargetBasis :=
    chooseHilbertBasis (WithLp 2 (finiteSCarrier × finiteSCarrier))
  have hdecomp :
      sourceRootCompletedFixedQuotientCorner owner lambda
          (radialSupportProjection lambda ∘L
            normalizedFiniteEulerInverse family ∘L
            radialSupportProjection lambda) =
        -(B ∘L outer.traceProduct ∘L R) -
          (B ∘L reflected.traceProduct ∘L R) -
          (B ∘L second.traceProduct ∘L R) +
          (B ∘L cc20Commutator (sourceProlateRemainder lambda)
            (detectorOperator owner) ∘L R) := by
    rw [← sourceRootCompletedFiniteEulerPairData_traceProduct_eq owner lambda
      family a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis hfactor]
    rw [sourceRootCompletedFiniteEulerPairData,
      BasisHilbertSchmidtPairData.smulRight_traceProduct_eq,
      BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq,
      sourceThreeBranchPairData,
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
    dsimp only [outer, reflected, second, B, R]
    apply ContinuousLinearMap.ext
    intro u
    unfold CCM24RadialBoundaryPairTransport.sourceSecondSupportProlateRemainder
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      map_add, map_sub, neg_add, neg_sub, neg_one_smul,
      cc20ProlateCommutatorBranch]
    abel
  let prolatePair :=
    (prolateCommutatorPairData' owner lambda globalBasis hfactor).boundedSandwich
      prolateTargetBasis B R
  have hOuterClass :
      IsTraceClassAlong globalBasis (B ∘L outer.traceProduct ∘L R) := by
    have hclass :=
      (outer.boundedSandwich outerTargetBasis B R).traceProduct_isTraceClassAlong
    rw [BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq] at hclass
    exact hclass
  have hReflectedClass :
      IsTraceClassAlong globalBasis (B ∘L reflected.traceProduct ∘L R) := by
    have hclass :=
      (reflected.boundedSandwich outerTargetBasis B R).traceProduct_isTraceClassAlong
    rw [BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq] at hclass
    exact hclass
  have hSecondClass :
      IsTraceClassAlong globalBasis (B ∘L second.traceProduct ∘L R) := by
    have hclass :=
      (second.boundedSandwich secondTargetBasis B R).traceProduct_isTraceClassAlong
    rw [BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq] at hclass
    exact hclass
  have hProlateClass : IsTraceClassAlong globalBasis
      (B ∘L cc20Commutator (sourceProlateRemainder lambda)
        (detectorOperator owner) ∘L R) := by
    have hclass := prolatePair.traceProduct_isTraceClassAlong
    rw [
      BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq,
      prolateCommutatorPairData'_traceProduct_eq] at hclass
    exact hclass
  have htrace :
      ordinaryTraceAlong globalBasis
          (sourceRootCompletedFixedQuotientCorner owner lambda
            (radialSupportProjection lambda ∘L
              normalizedFiniteEulerInverse family ∘L
              radialSupportProjection lambda)) =
        -ordinaryTraceAlong globalBasis (B ∘L outer.traceProduct ∘L R) -
          ordinaryTraceAlong globalBasis (B ∘L reflected.traceProduct ∘L R) -
          ordinaryTraceAlong globalBasis (B ∘L second.traceProduct ∘L R) +
          ordinaryTraceAlong globalBasis
            (B ∘L cc20Commutator (sourceProlateRemainder lambda)
              (detectorOperator owner) ∘L R) := by
    rw [hdecomp]
    rw [CC20Concrete.PositiveTrace.ordinaryTraceAlong_add globalBasis _ _
        (CCM24FiniteSProjectionTrace.PositiveTrace.isTraceClassAlong_sub globalBasis _ _
        (CCM24FiniteSProjectionTrace.PositiveTrace.isTraceClassAlong_sub globalBasis _ _
          (CCM24FiniteSProjectionTrace.PositiveTrace.isTraceClassAlong_neg globalBasis _
            hOuterClass) hReflectedClass) hSecondClass)
      hProlateClass]
    rw [CCM24FiniteSProjectionTrace.PositiveTrace.ordinaryTraceAlong_sub globalBasis _ _
      (CCM24FiniteSProjectionTrace.PositiveTrace.isTraceClassAlong_sub globalBasis _ _
        (CCM24FiniteSProjectionTrace.PositiveTrace.isTraceClassAlong_neg globalBasis _
          hOuterClass) hReflectedClass) hSecondClass]
    rw [CCM24FiniteSProjectionTrace.PositiveTrace.ordinaryTraceAlong_sub globalBasis _ _
      (CCM24FiniteSProjectionTrace.PositiveTrace.isTraceClassAlong_neg globalBasis _
        hOuterClass) hReflectedClass]
    rw [CCM24FiniteSProjectionTrace.PositiveTrace.ordinaryTraceAlong_neg globalBasis]
  rw [htrace]
  calc
    ‖-ordinaryTraceAlong globalBasis (B ∘L outer.traceProduct ∘L R) -
          ordinaryTraceAlong globalBasis (B ∘L reflected.traceProduct ∘L R) -
          ordinaryTraceAlong globalBasis (B ∘L second.traceProduct ∘L R) +
          ordinaryTraceAlong globalBasis
            (B ∘L cc20Commutator (sourceProlateRemainder lambda)
              (detectorOperator owner) ∘L R)‖ ≤
      ‖-ordinaryTraceAlong globalBasis (B ∘L outer.traceProduct ∘L R) -
          ordinaryTraceAlong globalBasis (B ∘L reflected.traceProduct ∘L R) -
          ordinaryTraceAlong globalBasis (B ∘L second.traceProduct ∘L R)‖ +
        ‖ordinaryTraceAlong globalBasis
            (B ∘L cc20Commutator (sourceProlateRemainder lambda)
              (detectorOperator owner) ∘L R)‖ := norm_add_le _ _
    _ ≤ (‖ordinaryTraceAlong globalBasis (B ∘L outer.traceProduct ∘L R)‖ +
          ‖ordinaryTraceAlong globalBasis (B ∘L reflected.traceProduct ∘L R)‖) +
          ‖ordinaryTraceAlong globalBasis (B ∘L second.traceProduct ∘L R)‖ +
        ‖ordinaryTraceAlong globalBasis
            (B ∘L cc20Commutator (sourceProlateRemainder lambda)
              (detectorOperator owner) ∘L R)‖ := by
      apply add_le_add
      · calc
          _ ≤ ‖-ordinaryTraceAlong globalBasis (B ∘L outer.traceProduct ∘L R) -
                ordinaryTraceAlong globalBasis (B ∘L reflected.traceProduct ∘L R)‖ +
              ‖ordinaryTraceAlong globalBasis (B ∘L second.traceProduct ∘L R)‖ :=
            norm_sub_le _ _
          _ ≤ (‖ordinaryTraceAlong globalBasis (B ∘L outer.traceProduct ∘L R)‖ +
                ‖ordinaryTraceAlong globalBasis (B ∘L reflected.traceProduct ∘L R)‖) +
              ‖ordinaryTraceAlong globalBasis (B ∘L second.traceProduct ∘L R)‖ := by
            calc
              _ ≤ (‖-ordinaryTraceAlong globalBasis
                    (B ∘L outer.traceProduct ∘L R)‖ +
                  ‖ordinaryTraceAlong globalBasis
                    (B ∘L reflected.traceProduct ∘L R)‖) +
                ‖ordinaryTraceAlong globalBasis (B ∘L second.traceProduct ∘L R)‖ :=
                add_le_add (norm_sub_le _ _) (le_refl _)
              _ = _ := by rw [norm_neg]
      · rfl
    _ ≤ 2 * P + 2 * P + 2 * P + 2 * ‖detectorOperator owner‖ * H := by
      exact add_le_add (add_le_add (add_le_add hOuter' hReflected') hSecond')
        hProlate
    _ = 6 * ((c - a) ^ 2 *
        SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) +
        2 * ‖detectorOperator owner‖ *
          (∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
            (globalBasis i)‖ ^ 2) := by
      dsimp only [P, H]
      ring

set_option maxHeartbeats 3000000 in
-- The root-norm substitution traverses the same expanded finite-S trace.
/-- The homogeneous bound with the detector reduced to the actual root norm. -/
theorem sourceRootCompletedFiniteEulerTrace_norm_le_rootNormPhysicalEnergy
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
      6 * ((c - a) ^ 2 *
        SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) +
        2 * ‖rootConvolution owner‖ ^ 2 *
          (∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
            (globalBasis i)‖ ^ 2) := by
  let H := ∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
    (globalBasis i)‖ ^ 2
  have hH : 0 ≤ H := by
    dsimp [H]
    exact tsum_nonneg fun i => sq_nonneg _
  have hdetector := sourceRootCompletedFiniteEulerTrace_norm_le_homogeneousPhysicalEnergy
    owner lambda family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis globalBasis
    boundaryBasis hfactor
  have hroot := detectorOperator_norm_le_rootConvolution_sq owner
  calc
    _ ≤ 6 * ((c - a) ^ 2 *
        SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) +
        2 * ‖detectorOperator owner‖ * H := by
      simpa only [H] using hdetector
    _ ≤ 6 * ((c - a) ^ 2 *
        SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) +
        2 * ‖rootConvolution owner‖ ^ 2 * H := by
      gcongr
    _ = 6 * ((c - a) ^ 2 *
        SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) +
        2 * ‖rootConvolution owner‖ ^ 2 *
          (∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
            (globalBasis i)‖ ^ 2) := by
      rfl

end CCM24FiniteSHomogeneousPhysicalEnergyBound
end CCM25Concrete
end Source
end ConnesWeilRH
