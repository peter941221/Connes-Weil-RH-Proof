/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSActualFirstJetSupportBound
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSInputSideTraceConsumer

/-!
# Support bound for the normalized finite-S endpoint

The normalized metric coframe is contractive, but its source trace still has
to be transported through the complete physical Hilbert--Schmidt pair.  This
module performs that carrier cycle explicitly and bounds the complete
outer/reflected/second-support/prolate trace before taking an absolute value.

The result applies to the lower-factor-normalized endpoint.  It does not
divide by the Euler lower factor and therefore is not a Gate 3U estimate for
the raw canonical response.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSNormalizedEndpointSupportBound

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CC20Concrete.CompactRootHalfLinePair
open CCM24FiniteSProjectionTrace
open CCM24FiniteSGramResponse
open CCM24FiniteSCommonBoundaryPair
open CCM24FiniteSFixedQuotientContractionBound
open CCM24FiniteSPhysicalBoundaryEnergy
open CCM24FiniteSProlateCommutatorTraceBound
open CCM24FiniteSHomogeneousPhysicalEnergyBound
open CCM24FiniteSRootCompletedFirstJet
open CCM24FiniteSRootConvolutionNorm
open CCM24FiniteSNormalizedCoframe
open CCM24FiniteSNormalizedPhysicalResponse
open CCM24FiniteSInputSideTraceConsumer
open CCM24FiniteSBandTrace
open CCM24FiniteSCoframeResponse
open CCM24SourceProlateTrace

noncomputable local instance sourceSoninCarrierCompleteSpace
    (lambda : CCM24SoninScale) : CompleteSpace (sourceSoninCarrier lambda) :=
  (ccm24ArchimedeanSoninClosedSubspace lambda).isClosed.completeSpace_coe

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

/-- Every bounded sandwich of the complete three-branch commutator has a
trace-class owner. -/
theorem sourceThreeBranchCommutator_boundedSandwich_isTraceClassAlong
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
        cc20ThreeBranchCommutator (radialSupportProjection lambda)
          (sourceFourierSupportProjection lambda)
          (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
        rightBounded) := by
  let data := sourceThreeBranchPairData owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
  have hclass :=
    (data.boundedSandwich boundaryBasis leftBounded rightBounded)
      |>.traceProduct_isTraceClassAlong
  rw [BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq] at hclass
  have hdata : data.traceProduct =
      cc20ThreeBranchCommutator (radialSupportProjection lambda)
        (sourceFourierSupportProjection lambda)
        (sourceProlateRemainder lambda) (detectorOperator owner) := by
    dsimp only [data]
    exact sourceThreeBranchPairData_traceProduct_eq owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
  rw [hdata] at hclass
  exact hclass

set_option maxHeartbeats 3000000 in
-- The four physical branches remain assembled until their complete trace
-- products are available; only then is the triangle inequality applied.
/-- Contractive sandwiches preserve the homogeneous support bound for the
complete three-branch commutator. -/
theorem sourceThreeBranchCommutator_boundedSandwich_trace_norm_le_supportEnergy
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
          cc20ThreeBranchCommutator (radialSupportProjection lambda)
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
    (sourceBasis := globalBasis) outerTargetBasis outer leftBounded rightBounded
    hleft hright (2 * P) (2 * P) hOuterLeft' hOuterRight'
  have hReflected := boundedSandwich_trace_norm_le_basisEnergy
    (sourceBasis := globalBasis) outerTargetBasis reflected leftBounded
    rightBounded hleft hright (2 * P) (2 * P) hReflectedLeft' hReflectedRight'
  have hSecond := boundedSandwich_trace_norm_le_basisEnergy
    (sourceBasis := globalBasis) secondTargetBasis second leftBounded rightBounded
    hleft hright (2 * P) (2 * P) hSecondLeft' hSecondRight'
  have hProlate :=
    sourceProlateCommutator_boundedSandwich_trace_norm_le_detector_factorEnergy
      owner lambda globalBasis hfactor leftBounded rightBounded hleft hright
  have hOuter' :
      ‖ordinaryTraceAlong globalBasis
          (leftBounded ∘L outer.traceProduct ∘L rightBounded)‖ ≤ 2 * P := by
    calc
      _ = ‖ordinaryTraceAlong globalBasis
          ((outer.boundedSandwich outerTargetBasis leftBounded rightBounded)
            |>.traceProduct)‖ := by
        rw [BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq]
      _ ≤ Real.sqrt (2 * P) * Real.sqrt (2 * P) := hOuter
      _ = 2 * P := by
        rw [← pow_two, Real.sq_sqrt (by positivity : 0 ≤ 2 * P)]
  have hReflected' :
      ‖ordinaryTraceAlong globalBasis
          (leftBounded ∘L reflected.traceProduct ∘L rightBounded)‖ ≤ 2 * P := by
    calc
      _ = ‖ordinaryTraceAlong globalBasis
          ((reflected.boundedSandwich outerTargetBasis leftBounded rightBounded)
            |>.traceProduct)‖ := by
        rw [BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq]
      _ ≤ Real.sqrt (2 * P) * Real.sqrt (2 * P) := hReflected
      _ = 2 * P := by
        rw [← pow_two, Real.sq_sqrt (by positivity : 0 ≤ 2 * P)]
  have hSecond' :
      ‖ordinaryTraceAlong globalBasis
          (leftBounded ∘L second.traceProduct ∘L rightBounded)‖ ≤ 2 * P := by
    calc
      _ = ‖ordinaryTraceAlong globalBasis
          ((second.boundedSandwich secondTargetBasis leftBounded rightBounded)
            |>.traceProduct)‖ := by
        rw [BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq]
      _ ≤ Real.sqrt (2 * P) * Real.sqrt (2 * P) := hSecond
      _ = 2 * P := by
        rw [← pow_two, Real.sq_sqrt (by positivity : 0 ≤ 2 * P)]
  have hdecomp :
      leftBounded ∘L
          cc20ThreeBranchCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
          rightBounded =
        (leftBounded ∘L outer.traceProduct ∘L rightBounded) +
          (leftBounded ∘L reflected.traceProduct ∘L rightBounded) +
          (leftBounded ∘L second.traceProduct ∘L rightBounded) -
          (leftBounded ∘L
            cc20Commutator (sourceProlateRemainder lambda)
              (detectorOperator owner) ∘L rightBounded) := by
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
    unfold CCM24RadialBoundaryPairTransport.sourceSecondSupportProlateRemainder
    simp only [cc20ProlateCommutatorBranch, ← ContinuousLinearMap.mul_def]
    noncomm_ring
  let prolateTargetBasis :=
    chooseHilbertBasis (WithLp 2 (finiteSCarrier × finiteSCarrier))
  let prolatePair :=
    (prolateCommutatorPairData' owner lambda globalBasis hfactor)
      |>.boundedSandwich prolateTargetBasis leftBounded rightBounded
  have hOuterClass : IsTraceClassAlong globalBasis
      (leftBounded ∘L outer.traceProduct ∘L rightBounded) := by
    have hclass :=
      (outer.boundedSandwich outerTargetBasis leftBounded rightBounded)
        |>.traceProduct_isTraceClassAlong
    rw [BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq] at hclass
    exact hclass
  have hReflectedClass : IsTraceClassAlong globalBasis
      (leftBounded ∘L reflected.traceProduct ∘L rightBounded) := by
    have hclass :=
      (reflected.boundedSandwich outerTargetBasis leftBounded rightBounded)
        |>.traceProduct_isTraceClassAlong
    rw [BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq] at hclass
    exact hclass
  have hSecondClass : IsTraceClassAlong globalBasis
      (leftBounded ∘L second.traceProduct ∘L rightBounded) := by
    have hclass :=
      (second.boundedSandwich secondTargetBasis leftBounded rightBounded)
        |>.traceProduct_isTraceClassAlong
    rw [BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq] at hclass
    exact hclass
  have hProlateClass : IsTraceClassAlong globalBasis
      (leftBounded ∘L cc20Commutator (sourceProlateRemainder lambda)
        (detectorOperator owner) ∘L rightBounded) := by
    have hclass := prolatePair.traceProduct_isTraceClassAlong
    rw [BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq,
      prolateCommutatorPairData'_traceProduct_eq] at hclass
    exact hclass
  have hOuterReflectedClass : IsTraceClassAlong globalBasis
      ((leftBounded ∘L outer.traceProduct ∘L rightBounded) +
        (leftBounded ∘L reflected.traceProduct ∘L rightBounded)) :=
    isTraceClassAlong_add globalBasis _ _ hOuterClass hReflectedClass
  have hBoundaryClass : IsTraceClassAlong globalBasis
      ((leftBounded ∘L outer.traceProduct ∘L rightBounded) +
          (leftBounded ∘L reflected.traceProduct ∘L rightBounded) +
        (leftBounded ∘L second.traceProduct ∘L rightBounded)) :=
    isTraceClassAlong_add globalBasis _ _ hOuterReflectedClass hSecondClass
  have htrace :
      ordinaryTraceAlong globalBasis
          (leftBounded ∘L
            cc20ThreeBranchCommutator (radialSupportProjection lambda)
              (sourceFourierSupportProjection lambda)
              (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
            rightBounded) =
        ordinaryTraceAlong globalBasis
            (leftBounded ∘L outer.traceProduct ∘L rightBounded) +
          ordinaryTraceAlong globalBasis
            (leftBounded ∘L reflected.traceProduct ∘L rightBounded) +
          ordinaryTraceAlong globalBasis
            (leftBounded ∘L second.traceProduct ∘L rightBounded) -
          ordinaryTraceAlong globalBasis
            (leftBounded ∘L cc20Commutator (sourceProlateRemainder lambda)
              (detectorOperator owner) ∘L rightBounded) := by
    rw [hdecomp]
    rw [ordinaryTraceAlong_sub globalBasis _ _ hBoundaryClass hProlateClass]
    rw [ordinaryTraceAlong_add globalBasis _ _ hOuterReflectedClass hSecondClass]
    rw [ordinaryTraceAlong_add globalBasis _ _ hOuterClass hReflectedClass]
  rw [htrace]
  have hdetectorRoot := detectorOperator_norm_le_rootConvolution_sq owner
  have hroot := rootConvolution_norm_le_supportLength_mul_seminorm
    owner a c hac hsupp
  have hrootSq : ‖rootConvolution owner‖ ^ 2 ≤ P := by
    have hsquare :=
      (sq_le_sq₀ (norm_nonneg _)
        (by positivity :
          0 ≤ (c - a) * SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test)).2
        hroot
    simpa only [P, mul_pow] using hsquare
  have hH : 0 ≤ H := by
    dsimp [H]
    exact tsum_nonneg fun i => sq_nonneg _
  calc
    _ ≤
        (‖ordinaryTraceAlong globalBasis
            (leftBounded ∘L outer.traceProduct ∘L rightBounded)‖ +
          ‖ordinaryTraceAlong globalBasis
            (leftBounded ∘L reflected.traceProduct ∘L rightBounded)‖) +
        ‖ordinaryTraceAlong globalBasis
          (leftBounded ∘L second.traceProduct ∘L rightBounded)‖ +
        ‖ordinaryTraceAlong globalBasis
          (leftBounded ∘L cc20Commutator (sourceProlateRemainder lambda)
            (detectorOperator owner) ∘L rightBounded)‖ := by
      calc
        _ ≤ ‖ordinaryTraceAlong globalBasis
                (leftBounded ∘L outer.traceProduct ∘L rightBounded) +
              ordinaryTraceAlong globalBasis
                (leftBounded ∘L reflected.traceProduct ∘L rightBounded) +
              ordinaryTraceAlong globalBasis
                (leftBounded ∘L second.traceProduct ∘L rightBounded)‖ +
            ‖ordinaryTraceAlong globalBasis
              (leftBounded ∘L cc20Commutator (sourceProlateRemainder lambda)
                (detectorOperator owner) ∘L rightBounded)‖ := norm_sub_le _ _
        _ ≤ _ := by
          apply add_le_add
          · calc
              _ ≤ ‖ordinaryTraceAlong globalBasis
                      (leftBounded ∘L outer.traceProduct ∘L rightBounded) +
                    ordinaryTraceAlong globalBasis
                      (leftBounded ∘L reflected.traceProduct ∘L rightBounded)‖ +
                  ‖ordinaryTraceAlong globalBasis
                    (leftBounded ∘L second.traceProduct ∘L rightBounded)‖ :=
                norm_add_le _ _
              _ ≤ _ := add_le_add (norm_add_le _ _) (le_refl _)
          · rfl
    _ ≤ 2 * P + 2 * P + 2 * P +
        2 * ‖detectorOperator owner‖ * H := by
      exact add_le_add (add_le_add (add_le_add hOuter' hReflected') hSecond')
        hProlate
    _ ≤ 6 * P + 2 * ‖rootConvolution owner‖ ^ 2 * H := by
      have hdetector :
          2 * ‖detectorOperator owner‖ * H ≤
            2 * ‖rootConvolution owner‖ ^ 2 * H :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdetectorRoot (by norm_num)) hH
      linarith
    _ ≤ 6 * P + 2 * P * H := by
      exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hrootSq (by norm_num)) hH)
    _ = (6 + 2 * (∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
          (globalBasis i)‖ ^ 2)) *
        ((c - a) ^ 2 *
          SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) := by
      dsimp only [P, H]
      ring

set_option maxHeartbeats 2000000 in
-- The source and ambient traces are cycled through the common physical pair
-- carrier.  Every carrier exchange retains explicit square summability.
/-- The normalized source endpoint trace is the ambient complete
three-branch trace with the normalized coframe kept on the right. -/
theorem normalizedSourceBandGramTrace_eq_ambientThreeBranchTrace
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
    ordinaryTraceAlong sourceBasis
        (normalizedSourceBandGramResponse owner lambda family) =
      -ordinaryTraceAlong globalBasis
        (cc20ThreeBranchCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
          normalizedFiniteEulerMetricCoframe lambda family ∘L
          (sourceInclusion lambda)†) := by
  let data := sourceThreeBranchPairData owner lambda a c hac hsupp
    negativeBasis positiveBasis outputBasis reflectedNegativeBasis
    reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor
  let J := sourceInclusion lambda
  let D := normalizedFiniteEulerMetricCoframe lambda family
  let sourcePair :=
    (BasisHilbertSchmidtPairData.boundedPrecomp boundaryBasis sourceBasis
      data J D).smulRight (-1)
  let ambientRight := -(data.right ∘L D ∘L J.adjoint)
  have hSourceProduct : sourcePair.traceProduct =
      normalizedSourceBandGramResponse owner lambda family := by
    dsimp only [sourcePair]
    rw [BasisHilbertSchmidtPairData.smulRight_traceProduct_eq,
      BasisHilbertSchmidtPairData.boundedPrecomp_traceProduct_eq]
    dsimp only [data, J, D]
    rw [sourceThreeBranchPairData_traceProduct_eq owner lambda a c hac hsupp
      negativeBasis positiveBasis outputBasis reflectedNegativeBasis
      reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor,
      normalizedSourceBandGramResponse,
      sourceBandGramResponse_eq_neg_threeBranch owner lambda family]
    apply ContinuousLinearMap.ext
    intro u
    have hcoframe :
        finiteEulerMetricCoframe lambda family u =
          finiteEulerAmbientGram family
            (sourceInclusion lambda (finiteEulerGramInv lambda family u)) := by
      rfl
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.neg_apply, neg_one_smul]
    unfold normalizedFiniteEulerMetricCoframe
    simp only [ContinuousLinearMap.smul_apply]
    rw [hcoframe]
    simp only [map_smul, smul_neg]
  have hAmbientRight : Summable fun i =>
      ‖ambientRight (globalBasis i)‖ ^ 2 := by
    have hprecomp := summable_normSq_precomp globalBasis boundaryBasis globalBasis
      data.right (D ∘L J.adjoint) data.right_summable_normSq
    simpa only [ambientRight, ContinuousLinearMap.neg_apply, norm_neg] using hprecomp
  have hSourceCycle :=
    sourcePair.ordinaryTraceAlong_traceProduct_eq_cyclic boundaryBasis
  have hAmbientCycle :=
    BasisHilbertSchmidtPairData.ordinaryTraceAlong_adjoint_comp_eq_comp_adjoint
      globalBasis boundaryBasis data.left ambientRight
      data.left_summable_normSq hAmbientRight
  rw [← hSourceProduct]
  calc
    ordinaryTraceAlong sourceBasis sourcePair.traceProduct =
        ordinaryTraceAlong boundaryBasis
          (sourcePair.right ∘L sourcePair.left.adjoint) := hSourceCycle
    _ = ordinaryTraceAlong boundaryBasis
        (ambientRight ∘L data.left.adjoint) := by
      apply congrArg (ordinaryTraceAlong boundaryBasis)
      dsimp only [sourcePair, ambientRight,
        BasisHilbertSchmidtPairData.smulRight,
        BasisHilbertSchmidtPairData.boundedPrecomp]
      rw [ContinuousLinearMap.adjoint_comp]
      apply ContinuousLinearMap.ext
      intro u
      simp only [ContinuousLinearMap.comp_apply, neg_one_smul,
        ContinuousLinearMap.neg_apply]
    _ = ordinaryTraceAlong globalBasis
        (data.left.adjoint ∘L ambientRight) := hAmbientCycle.symm
    _ = -ordinaryTraceAlong globalBasis
        (data.traceProduct ∘L D ∘L J.adjoint) := by
      have hoperator : data.left.adjoint ∘L ambientRight =
          -(data.traceProduct ∘L D ∘L J.adjoint) := by
        apply ContinuousLinearMap.ext
        intro u
        dsimp only [ambientRight, BasisHilbertSchmidtPairData.traceProduct]
        simp only [ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.neg_apply, map_neg]
      rw [hoperator]
      simp only [ordinaryTraceAlong]
      rw [← tsum_neg]
      apply tsum_congr
      intro i
      exact inner_neg_right _ _
    _ = -ordinaryTraceAlong globalBasis
        (cc20ThreeBranchCommutator (radialSupportProjection lambda)
            (sourceFourierSupportProjection lambda)
            (sourceProlateRemainder lambda) (detectorOperator owner) ∘L
          normalizedFiniteEulerMetricCoframe lambda family ∘L
          (sourceInclusion lambda)†) := by
      dsimp only [data, D, J]
      rw [sourceThreeBranchPairData_traceProduct_eq owner lambda a c hac hsupp
        negativeBasis positiveBasis outputBasis reflectedNegativeBasis
        reflectedPositiveBasis reflectedOutputBasis globalBasis hfactor]

/-- The complete normalized endpoint trace has the same homogeneous support
bound as one complete physical three-branch sandwich. -/
theorem normalizedSourceBandGramTrace_norm_le_supportEnergy
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
        (normalizedSourceBandGramResponse owner lambda family)‖ ≤
      (6 + 2 * (∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
          (globalBasis i)‖ ^ 2)) *
        ((c - a) ^ 2 *
          SchwartzMap.seminorm ℂ 0 0 owner.sourceTest.test ^ 2) := by
  rw [normalizedSourceBandGramTrace_eq_ambientThreeBranchTrace owner lambda
    family a c hac hsupp negativeBasis positiveBasis outputBasis
    reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
    globalBasis boundaryBasis sourceBasis hfactor, norm_neg]
  let rightBounded := normalizedFiniteEulerMetricCoframe lambda family ∘L
    (sourceInclusion lambda)†
  have hJ : ‖(sourceInclusion lambda)†‖ ≤ 1 := by
    have hadjoint : ‖(sourceInclusion lambda)†‖ =
        ‖sourceInclusion lambda‖ :=
      ContinuousLinearMap.adjoint.norm_map _
    rw [hadjoint]
    exact Submodule.norm_subtypeL_le _
  have hright : ‖rightBounded‖ ≤ 1 := by
    dsimp only [rightBounded]
    calc
      _ ≤ ‖normalizedFiniteEulerMetricCoframe lambda family‖ *
          ‖(sourceInclusion lambda)†‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := mul_le_mul
        (norm_normalizedFiniteEulerMetricCoframe_le_one lambda family) hJ
        (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hid : ‖ContinuousLinearMap.id ℂ finiteSCarrier‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro u
    simp only [ContinuousLinearMap.id_apply, one_mul, le_refl]
  simpa only [ContinuousLinearMap.id_comp, rightBounded] using
    (sourceThreeBranchCommutator_boundedSandwich_trace_norm_le_supportEnergy
      owner lambda a c hac hsupp negativeBasis positiveBasis outputBasis
      reflectedNegativeBasis reflectedPositiveBasis reflectedOutputBasis
      globalBasis boundaryBasis hfactor (ContinuousLinearMap.id ℂ finiteSCarrier)
      rightBounded hid hright)

end CCM24FiniteSNormalizedEndpointSupportBound
end CCM25Concrete
end Source
end ConnesWeilRH
