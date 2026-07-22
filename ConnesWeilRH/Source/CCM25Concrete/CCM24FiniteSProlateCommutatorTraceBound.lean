/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSFixedPhysicalEnergyBound

/-!
# Homogeneous trace bound for the prolate commutator

The prolate remainder is an exact positive square `A† A`.  Its commutator
with the detector is therefore the difference of the two bounded sandwiches
`A† D A` and `A† D† A`.  Estimating those two trace products geometrically
preserves the correct homogeneous factor `‖D‖ * ‖A‖_HS²`; an energy estimate
on the orthogonal direct sum would incorrectly leave an additive `‖A‖_HS²`.
-/

namespace ConnesWeilRH
namespace Source
namespace CCM25Concrete
namespace CCM24FiniteSProlateCommutatorTraceBound

open MeasureTheory
open scoped InnerProduct InnerProductSpace

open CC20Concrete
open CC20Concrete.PositiveTrace
open CCM24FiniteSProjectionTrace
open CCM24FiniteSCommonBoundaryPair
open CCM24SourceProlateTrace
open CCM24FiniteSRootCompletedFirstJet
open CCM24FiniteSFixedPhysicalEnergyBound

lemma sqrt_sq_mul_sqrt_eq
    (d h : ℝ) (hd : 0 ≤ d) (hh : 0 ≤ h) :
    Real.sqrt h * Real.sqrt (d ^ 2 * h) = d * h := by
  rw [show d ^ 2 * h = h * d ^ 2 by ring]
  rw [Real.sqrt_mul hh, Real.sqrt_sq_eq_abs, abs_of_nonneg hd]
  nlinarith [Real.sq_sqrt hh]

set_option maxHeartbeats 4000000 in
-- The concrete pair trace requires the same elaboration budget as the
-- surrounding finite-S physical-pair owners.
/-- The actual prolate commutator trace has homogeneous detector scaling. -/
lemma sourceProlateCommutator_trace_norm_le_detector_factorEnergy
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2) :
    ‖ordinaryTraceAlong globalBasis
        (cc20Commutator (sourceProlateRemainder lambda)
          (detectorOperator owner))‖ ≤
      2 * ‖detectorOperator owner‖ *
        (∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
          (globalBasis i)‖ ^ 2) := by
  let forward := prolateForwardPairData owner lambda globalBasis hfactor
  let reverse := prolateReversePairData owner lambda globalBasis hfactor
  let h := ∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
    (globalBasis i)‖ ^ 2
  let d := ‖detectorOperator owner‖
  have hh : 0 ≤ h := by
    dsimp [h]
    exact tsum_nonneg fun i => sq_nonneg _
  have hd : 0 ≤ d := norm_nonneg _
  have hforward := ordinaryTraceAlong_traceProduct_norm_le_geometricEnergy forward
  have hreverse := ordinaryTraceAlong_traceProduct_norm_le_geometricEnergy reverse
  have hforwardClass := forward.traceProduct_isTraceClassAlong
  have hreverseClass := reverse.traceProduct_isTraceClassAlong
  have hpair :
      (prolateCommutatorPairData' owner lambda globalBasis hfactor).traceProduct =
        forward.traceProduct - reverse.traceProduct := by
    rw [prolateCommutatorPairData',
      BasisHilbertSchmidtPairData.l2Sum_traceProduct_eq_add,
      BasisHilbertSchmidtPairData.smulRight_traceProduct_eq]
    simpa only [forward, reverse, sub_eq_add_neg, neg_one_smul]
  have hcommEq :
      cc20Commutator (sourceProlateRemainder lambda)
          (detectorOperator owner) =
        forward.traceProduct - reverse.traceProduct := by
    rw [← hpair]
    exact (prolateCommutatorPairData'_traceProduct_eq owner lambda
      globalBasis hfactor).symm
  rw [hcommEq, CC20Concrete.PositiveTrace.ordinaryTraceAlong_sub globalBasis _ _
    hforwardClass hreverseClass]
  have hforwardLeft := prolateForwardPairData_left_basisEnergy_le owner lambda
    globalBasis hfactor
  have hforwardRight := prolateForwardPairData_right_basisEnergy_le owner lambda
    globalBasis hfactor
  have hreverseLeft := prolateReversePairData_left_basisEnergy_le owner lambda
    globalBasis hfactor
  have hreverseRight := prolateReversePairData_right_basisEnergy_le owner lambda
    globalBasis hfactor
  calc
    ‖ordinaryTraceAlong globalBasis forward.traceProduct -
        ordinaryTraceAlong globalBasis reverse.traceProduct‖ ≤
      ‖ordinaryTraceAlong globalBasis forward.traceProduct‖ +
        ‖ordinaryTraceAlong globalBasis reverse.traceProduct‖ :=
      norm_sub_le _ _
    _ ≤ Real.sqrt h * Real.sqrt (d ^ 2 * h) +
        Real.sqrt (d ^ 2 * h) * Real.sqrt h := by
      calc
        _ ≤ Real.sqrt (∑' i, ‖forward.left (globalBasis i)‖ ^ 2) *
            Real.sqrt (∑' i, ‖forward.right (globalBasis i)‖ ^ 2) +
            Real.sqrt (∑' i, ‖reverse.left (globalBasis i)‖ ^ 2) *
            Real.sqrt (∑' i, ‖reverse.right (globalBasis i)‖ ^ 2) :=
          add_le_add hforward hreverse
        _ ≤ Real.sqrt h * Real.sqrt (d ^ 2 * h) +
            Real.sqrt (d ^ 2 * h) * Real.sqrt h := by
          gcongr
    _ = 2 * d * h := by
      rw [sqrt_sq_mul_sqrt_eq d h hd hh]
      rw [mul_comm (Real.sqrt (d ^ 2 * h)) (Real.sqrt h)]
      rw [sqrt_sq_mul_sqrt_eq d h hd hh]
      ring

set_option maxHeartbeats 4000000 in
-- The four bounded sandwiches must be elaborated before the two commutator
-- orientations can be compared on the original finite-S carrier.
-- The actual finite-Euler consumer is a bounded sandwich of the prolate
-- commutator. This owner preserves the same detector homogeneity after that
-- transport instead of applying an additive energy estimate to the transported
-- commutator.
lemma sourceProlateCommutator_boundedSandwich_trace_norm_le_detector_factorEnergy
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale)
    {ν : Type*} (globalBasis : HilbertBasis ν ℂ finiteSCarrier)
    (hfactor : Summable fun i =>
      ‖sourceProlateHilbertSchmidtFactor lambda (globalBasis i)‖ ^ 2)
    (leftBounded rightBounded : finiteSCarrier →L[ℂ] finiteSCarrier)
    (hleft : ‖leftBounded‖ ≤ 1) (hright : ‖rightBounded‖ ≤ 1) :
    ‖ordinaryTraceAlong globalBasis
        (leftBounded ∘L
          cc20Commutator (sourceProlateRemainder lambda)
            (detectorOperator owner) ∘L rightBounded)‖ ≤
      2 * ‖detectorOperator owner‖ *
        (∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
          (globalBasis i)‖ ^ 2) := by
  let data := sourceProlatePairData globalBasis lambda hfactor
  let detector := detectorOperator owner
  let h := ∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
    (globalBasis i)‖ ^ 2
  let d := ‖detector‖
  let forward := data.boundedSandwich globalBasis leftBounded
    (detector ∘L rightBounded)
  let reverse := data.boundedSandwich globalBasis
    (leftBounded ∘L detector) rightBounded
  have hh : 0 ≤ h := by
    dsimp [h]
    exact tsum_nonneg fun i => sq_nonneg _
  have hd : 0 ≤ d := norm_nonneg _
  have hleftAdj : ‖leftBounded.adjoint‖ ≤ 1 := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact hleft
  have hleftAdjSq : ‖leftBounded.adjoint‖ ^ 2 ≤ (1 : ℝ) := by
    nlinarith [sq_nonneg (‖leftBounded.adjoint‖ - 1),
      norm_nonneg leftBounded.adjoint]
  have hDright : ‖detector ∘L rightBounded‖ ≤ d := by
    calc
      _ ≤ ‖detector‖ * ‖rightBounded‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ d * 1 := mul_le_mul_of_nonneg_left hright hd
      _ = d := by simp only [detector, d, mul_one]
  have hDrightSq : ‖detector ∘L rightBounded‖ ^ 2 ≤ d ^ 2 := by
    nlinarith [sq_nonneg (‖detector ∘L rightBounded‖ - d),
      norm_nonneg (detector ∘L rightBounded)]
  have hleftD : ‖leftBounded ∘L detector‖ ≤ d := by
    calc
      _ ≤ ‖leftBounded‖ * ‖detector‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * d := mul_le_mul_of_nonneg_right hleft hd
      _ = d := by simp only [detector, d, one_mul]
  have hleftDSq : ‖leftBounded ∘L detector‖ ^ 2 ≤ d ^ 2 := by
    nlinarith [sq_nonneg (‖leftBounded ∘L detector‖ - d),
      norm_nonneg (leftBounded ∘L detector)]
  have hrightSq : ‖rightBounded‖ ^ 2 ≤ (1 : ℝ) := by
    nlinarith [sq_nonneg (‖rightBounded‖ - 1), norm_nonneg rightBounded]
  have hforwardLeftRaw := tsum_normSq_precomp_le globalBasis globalBasis
    globalBasis (sourceProlateHilbertSchmidtFactor lambda)
      leftBounded.adjoint hfactor
  have hforwardRightRaw := tsum_normSq_precomp_le globalBasis globalBasis
    globalBasis (sourceProlateHilbertSchmidtFactor lambda)
      (detector ∘L rightBounded) hfactor
  have hreverseLeftRaw := tsum_normSq_precomp_le globalBasis globalBasis
    globalBasis (sourceProlateHilbertSchmidtFactor lambda)
      (leftBounded ∘L detector).adjoint hfactor
  rw [ContinuousLinearMap.adjoint.norm_map] at hreverseLeftRaw
  have hreverseRightRaw := tsum_normSq_precomp_le globalBasis globalBasis
    globalBasis (sourceProlateHilbertSchmidtFactor lambda)
      rightBounded hfactor
  have hforwardLeft :
      (∑' i, ‖forward.left (globalBasis i)‖ ^ 2) ≤ h := by
    calc
      _ ≤ ‖leftBounded.adjoint‖ ^ 2 * h := by
        simpa only [forward, data,
          BasisHilbertSchmidtPairData.boundedSandwich] using hforwardLeftRaw
      _ ≤ 1 * h := mul_le_mul_of_nonneg_right hleftAdjSq hh
      _ = h := one_mul _
  have hforwardRight :
      (∑' i, ‖forward.right (globalBasis i)‖ ^ 2) ≤ d ^ 2 * h := by
    simpa only [forward, data,
      BasisHilbertSchmidtPairData.boundedSandwich] using
      (hforwardRightRaw.trans (mul_le_mul_of_nonneg_right hDrightSq hh))
  have hreverseLeft :
      (∑' i, ‖reverse.left (globalBasis i)‖ ^ 2) ≤ d ^ 2 * h := by
    simpa only [reverse, data,
      BasisHilbertSchmidtPairData.boundedSandwich,
      ContinuousLinearMap.adjoint.norm_map] using
      (hreverseLeftRaw.trans (mul_le_mul_of_nonneg_right hleftDSq hh))
  have hreverseRight :
      (∑' i, ‖reverse.right (globalBasis i)‖ ^ 2) ≤ h := by
    calc
      _ ≤ ‖rightBounded‖ ^ 2 * h := by
        simpa only [reverse, data,
          BasisHilbertSchmidtPairData.boundedSandwich] using hreverseRightRaw
      _ ≤ 1 * h := mul_le_mul_of_nonneg_right hrightSq hh
      _ = h := one_mul _
  have hforward := ordinaryTraceAlong_traceProduct_norm_le_geometricEnergy forward
  have hreverse := ordinaryTraceAlong_traceProduct_norm_le_geometricEnergy reverse
  have hforwardClass := forward.traceProduct_isTraceClassAlong
  have hreverseClass := reverse.traceProduct_isTraceClassAlong
  have hpair :
      forward.traceProduct - reverse.traceProduct =
        leftBounded ∘L
          cc20Commutator (sourceProlateRemainder lambda) detector ∘L
            rightBounded := by
    dsimp only [forward, reverse]
    rw [
      BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq,
      BasisHilbertSchmidtPairData.boundedSandwich_traceProduct_eq,
      ← sourceProlatePairData_traceProduct_eq globalBasis lambda hfactor]
    unfold cc20Commutator
    apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      detector, map_sub]
    abel
  rw [← hpair, CC20Concrete.PositiveTrace.ordinaryTraceAlong_sub globalBasis
    _ _ hforwardClass hreverseClass]
  calc
    ‖ordinaryTraceAlong globalBasis forward.traceProduct -
        ordinaryTraceAlong globalBasis reverse.traceProduct‖ ≤
      ‖ordinaryTraceAlong globalBasis forward.traceProduct‖ +
        ‖ordinaryTraceAlong globalBasis reverse.traceProduct‖ :=
      norm_sub_le _ _
    _ ≤ Real.sqrt h * Real.sqrt (d ^ 2 * h) +
        Real.sqrt (d ^ 2 * h) * Real.sqrt h := by
      calc
        _ ≤ Real.sqrt (∑' i, ‖forward.left (globalBasis i)‖ ^ 2) *
            Real.sqrt (∑' i, ‖forward.right (globalBasis i)‖ ^ 2) +
            Real.sqrt (∑' i, ‖reverse.left (globalBasis i)‖ ^ 2) *
            Real.sqrt (∑' i, ‖reverse.right (globalBasis i)‖ ^ 2) :=
          add_le_add hforward hreverse
        _ ≤ Real.sqrt h * Real.sqrt (d ^ 2 * h) +
            Real.sqrt (d ^ 2 * h) * Real.sqrt h := by
          exact add_le_add
            (mul_le_mul (Real.sqrt_le_sqrt hforwardLeft)
              (Real.sqrt_le_sqrt hforwardRight)
              (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
            (mul_le_mul (Real.sqrt_le_sqrt hreverseLeft)
              (Real.sqrt_le_sqrt hreverseRight)
              (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    _ = 2 * d * h := by
      rw [sqrt_sq_mul_sqrt_eq d h hd hh]
      rw [mul_comm (Real.sqrt (d ^ 2 * h)) (Real.sqrt h)]
      rw [sqrt_sq_mul_sqrt_eq d h hd hh]
      ring
    _ = 2 * ‖detectorOperator owner‖ *
        (∑' i, ‖sourceProlateHilbertSchmidtFactor lambda
          (globalBasis i)‖ ^ 2) := by
      rfl

end CCM24FiniteSProlateCommutatorTraceBound
end CCM25Concrete
end Source
end ConnesWeilRH
