/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3DoubledShiftSoninTransport

/-!
# R3 weighted finite-stage commutator ledger

This leaf supplies the exact algebraic entry point for the detector-weighted
alternating-projection route.  It defines a recursively accumulated stage
commutator and proves that it is exactly the commutator of a power with the
detector.  No trace-class assertion, convergence assertion, sign conclusion,
or RH premise is used.
-/

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24UnitScaleProlateAlignment

local notation "Carrier" =>
  Source.CCM25Concrete.CCM24FiniteSProjectionTrace.finiteSCarrier
local notation "Op" => Carrier →L[ℂ] Carrier

noncomputable def operatorCommutator (T D : Op) : Op :=
  T * D - D * T

noncomputable def weightedCommutatorStage (T D : Op) : ℕ → Op
  | 0 => 0
  | n + 1 =>
      T * weightedCommutatorStage T D n +
        operatorCommutator T D * T ^ n

theorem weightedCommutatorStage_zero (T D : Op) :
    weightedCommutatorStage T D 0 = 0 := by
  rfl

theorem weightedCommutatorStage_succ (T D : Op) (n : ℕ) :
    weightedCommutatorStage T D (n + 1) =
      T * weightedCommutatorStage T D n +
        operatorCommutator T D * T ^ n := by
  rfl

theorem operator_pow_commutator_eq_weightedStage
    (T D : Op) (n : ℕ) :
    (T ^ n) * D - D * (T ^ n) =
      weightedCommutatorStage T D n := by
  induction n with
  | zero =>
      simp [weightedCommutatorStage]
  | succ n ih =>
      rw [pow_succ']
      calc
        T * (T ^ n) * D - D * (T * (T ^ n)) =
            T * ((T ^ n) * D - D * (T ^ n)) +
              operatorCommutator T D * (T ^ n) := by
                unfold operatorCommutator
                noncomm_ring
        _ = T * weightedCommutatorStage T D n +
              operatorCommutator T D * (T ^ n) := by rw [ih]
        _ = weightedCommutatorStage T D (n + 1) := by
              rw [weightedCommutatorStage_succ]

noncomputable def doubledShiftRadialProjection (b : ℝ) : Op :=
  (doubledShiftRadialClosedSubspace b).toSubmodule.starProjection

theorem doubledShiftRadialProjection_isStarProjection (b : ℝ) :
    IsStarProjection (doubledShiftRadialProjection b) := by
  exact isStarProjection_starProjection

noncomputable def doubledShiftAlternatingProduct (b : ℝ) : Op :=
  doubledShiftRadialProjection b *
    sourceFourierSupportProjection unitSoninScale *
    doubledShiftRadialProjection b

theorem doubledShiftAlternatingProduct_isPositive (b : ℝ) :
    (doubledShiftAlternatingProduct b).IsPositive := by
  let p : Op := doubledShiftRadialProjection b
  let q : Op := sourceFourierSupportProjection unitSoninScale
  have hq : q.IsPositive :=
    ContinuousLinearMap.IsPositive.of_isStarProjection
      (sourceFourierSupportProjection_isStarProjection unitSoninScale)
  have hp : IsSelfAdjoint p := isSelfAdjoint_starProjection _
  have hpos := hq.conj_adjoint p
  rw [hp.adjoint_eq] at hpos
  simpa only [doubledShiftAlternatingProduct, p, q,
    ContinuousLinearMap.mul_def] using hpos

theorem doubledShiftAlternatingProduct_isSelfAdjoint (b : ℝ) :
    IsSelfAdjoint (doubledShiftAlternatingProduct b) := by
  exact (doubledShiftAlternatingProduct_isPositive b).isSelfAdjoint

theorem doubledShiftAlternatingProduct_norm_le_one (b : ℝ) :
    ‖doubledShiftAlternatingProduct b‖ ≤ 1 := by
  let p : Op := doubledShiftRadialProjection b
  let q : Op := sourceFourierSupportProjection unitSoninScale
  have hp : ‖p‖ ≤ 1 :=
    IsStarProjection.norm_le _ (doubledShiftRadialProjection_isStarProjection b)
  have hq : ‖q‖ ≤ 1 :=
    IsStarProjection.norm_le _
      (sourceFourierSupportProjection_isStarProjection unitSoninScale)
  calc
    ‖doubledShiftAlternatingProduct b‖ = ‖p * q * p‖ := by
      rfl
    _ ≤ ‖p * q‖ * ‖p‖ := norm_mul_le _ _
    _ ≤ (‖p‖ * ‖q‖) * ‖p‖ := by
      gcongr
      exact norm_mul_le _ _
    _ ≤ (1 * 1) * 1 := by gcongr
    _ = 1 := by norm_num

theorem doubledShiftAlternatingProduct_commutator_stage
    (b : ℝ) (D : Op) (n : ℕ) :
    ((doubledShiftAlternatingProduct b) ^ n) * D -
        D * ((doubledShiftAlternatingProduct b) ^ n) =
      weightedCommutatorStage (doubledShiftAlternatingProduct b) D n := by
  exact operator_pow_commutator_eq_weightedStage
    (doubledShiftAlternatingProduct b) D n

end Dev
end ConnesWeilRH
