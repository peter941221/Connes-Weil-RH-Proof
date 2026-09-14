/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3WeightedFiniteStage
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# R3 power-to-projection bridge

This leaf isolates the exact analytic step still needed after the finite-stage
alternating-product ledger.  A projection `P` is the intended intersection
projection.  If `T` acts as the identity on the range of `P` from both sides
and the complementary defect `T - P` has norm strictly below one, then the
successive powers of `T` converge geometrically to `P`.

The strict defect bound is deliberately exposed as a lower-data obligation;
it is not supplied as an axiom and is not identified with the R3 conclusion.
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

theorem pow_mul_projection_eq_projection
    {T P : Op} (hTP : T * P = P) (n : ℕ) : T ^ n * P = P := by
  induction n with
  | zero =>
      simp only [pow_zero, one_mul]
  | succ n ih =>
      rw [pow_succ']
      calc
        T * T ^ n * P = T * P := by rw [mul_assoc, ih]
        _ = P := hTP

theorem succ_pow_sub_projection_eq_defect_pow
    {T P : Op}
    (hTP : T * P = P) (hPT : P * T = P)
    (hP : P * P = P) (n : ℕ) :
    T ^ (n + 1) - P = (T - P) ^ (n + 1) := by
  have hpowP (k : ℕ) : T ^ (k + 1) * P = P := by
    exact pow_mul_projection_eq_projection hTP (k + 1)
  induction n with
  | zero =>
      simp only [Nat.zero_add, pow_one]
  | succ n ih =>
      simp only [Nat.succ_eq_add_one, add_assoc]
      have hpow := hpowP n
      calc
        (T ^ (n + 1 + 1) - P) =
            (T ^ (n + 1) - P) * (T - P) := by
              rw [pow_succ T (n + 1)]
              simp only [sub_mul, mul_sub, hpow, hPT, hP]
              abel
        _ = (T - P) ^ (n + 1) * (T - P) := by rw [ih]
        _ = (T - P) ^ (n + 1 + 1) := by
          symm
          exact pow_succ (T - P) (n + 1)

theorem tendsto_succ_pow_of_projection_gap
    {T P : Op}
    (hTP : T * P = P) (hPT : P * T = P)
    (hP : P * P = P) {rho : ℝ}
    (hgap : ‖T - P‖ < rho) (hrho : rho < 1) :
    Filter.Tendsto (fun n : ℕ => T ^ (n + 1)) Filter.atTop (nhds P) := by
  have hpow : Filter.Tendsto
      (fun n : ℕ => (T - P) ^ (n + 1)) Filter.atTop (nhds 0) := by
    have hbase : Filter.Tendsto
        (fun n : ℕ => (T - P) ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one (hgap.trans hrho)
    exact hbase.comp (Filter.tendsto_add_atTop_nat 1)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hnorm :
      Filter.Tendsto (fun n : ℕ => ‖T ^ (n + 1) - P‖) Filter.atTop (nhds 0) := by
    simpa only [succ_pow_sub_projection_eq_defect_pow hTP hPT hP] using
      tendsto_norm_zero.comp hpow
  exact hnorm

noncomputable def doubledShiftSoninIntersectionProjection (b : ℝ) : Op :=
  (doubledShiftSoninClosedSubspace b).toSubmodule.starProjection

theorem doubledShiftSoninIntersectionProjection_isStarProjection (b : ℝ) :
    IsStarProjection (doubledShiftSoninIntersectionProjection b) := by
  exact isStarProjection_starProjection

theorem doubledShiftSoninIntersectionProjection_fixed_of_mem
    (b : ℝ) {v : Carrier}
    (hv : v ∈ doubledShiftSoninClosedSubspace b) :
    doubledShiftSoninIntersectionProjection b v = v := by
  exact (Submodule.starProjection_eq_self_iff).mpr hv

theorem doubledShiftAlternatingProduct_comp_intersectionProjection
    (b : ℝ) :
    doubledShiftAlternatingProduct b *
        doubledShiftSoninIntersectionProjection b =
      doubledShiftSoninIntersectionProjection b := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.mul_apply]
  exact doubledShiftAlternatingProduct_fixed_of_mem_intersection b
    ((doubledShiftSoninClosedSubspace b).toSubmodule.starProjection_apply_mem v)

def doubledShiftAlternatingProduct_has_projection_gap (b : ℝ) : Prop :=
  ∃ rho : ℝ,
    ‖doubledShiftAlternatingProduct b -
        doubledShiftSoninIntersectionProjection b‖ < rho ∧ rho < 1

theorem doubledShiftAlternatingProduct_succ_pow_tendsto_projection
    (b : ℝ)
    (hPT : doubledShiftSoninIntersectionProjection b *
        doubledShiftAlternatingProduct b =
      doubledShiftSoninIntersectionProjection b)
    (hgap : doubledShiftAlternatingProduct_has_projection_gap b) :
    Filter.Tendsto
      (fun n : ℕ => (doubledShiftAlternatingProduct b) ^ (n + 1)) Filter.atTop
      (nhds (doubledShiftSoninIntersectionProjection b)) := by
  rcases hgap with ⟨rho, hgap, hrho⟩
  exact tendsto_succ_pow_of_projection_gap
    (doubledShiftAlternatingProduct_comp_intersectionProjection b)
    hPT
    ((doubledShiftSoninClosedSubspace b).toSubmodule.isIdempotentElem_starProjection)
    hgap hrho

end Dev
end ConnesWeilRH
