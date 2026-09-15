/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1G8R3WeightedFiniteStage
import ConnesWeilRH.Dev.C1G8R3WeightedStrongToHS
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.MetricSpace.Equicontinuity
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

/-- The radial projection absorbs the alternating product on its left. -/
theorem doubledShiftRadialProjection_comp_doubledShiftAlternatingProduct
    (b : ℝ) :
    doubledShiftRadialProjection b * doubledShiftAlternatingProduct b =
      doubledShiftAlternatingProduct b := by
  have hp : doubledShiftRadialProjection b * doubledShiftRadialProjection b =
      doubledShiftRadialProjection b :=
    (doubledShiftRadialProjection_isStarProjection b).isIdempotentElem
  unfold doubledShiftAlternatingProduct
  calc
    doubledShiftRadialProjection b *
        (doubledShiftRadialProjection b *
          sourceFourierSupportProjection unitSoninScale *
          doubledShiftRadialProjection b) =
        (doubledShiftRadialProjection b * doubledShiftRadialProjection b) *
          sourceFourierSupportProjection unitSoninScale *
          doubledShiftRadialProjection b := by noncomm_ring
    _ = _ := by rw [hp]

/-- The fixed vectors of the actual alternating product are exactly the
doubled-shift Sonin intersection.  This is the fixed-space identification
needed by an angle-free alternating-projection limit; it asserts no rate or
convergence. -/
theorem doubledShiftAlternatingProduct_fixed_iff_mem_intersection
    (b : ℝ) (v : Carrier) :
    doubledShiftAlternatingProduct b v = v ↔
      v ∈ doubledShiftSoninClosedSubspace b := by
  constructor
  · intro hfixed
    have hpv : doubledShiftRadialProjection b v = v := by
      calc
        doubledShiftRadialProjection b v =
            doubledShiftRadialProjection b
              (doubledShiftAlternatingProduct b v) :=
          congrArg (doubledShiftRadialProjection b) hfixed.symm
        _ = (doubledShiftRadialProjection b *
              doubledShiftAlternatingProduct b) v := by
          rfl
        _ = doubledShiftAlternatingProduct b v := by
          rw [doubledShiftRadialProjection_comp_doubledShiftAlternatingProduct]
        _ = v := hfixed
    have hqnorm : ‖sourceFourierSupportProjection unitSoninScale v‖ = ‖v‖ := by
      apply le_antisymm
      · calc
          ‖sourceFourierSupportProjection unitSoninScale v‖ ≤
              ‖sourceFourierSupportProjection unitSoninScale‖ * ‖v‖ :=
            (sourceFourierSupportProjection unitSoninScale).le_opNorm v
          _ ≤ 1 * ‖v‖ := by
            gcongr
            exact IsStarProjection.norm_le _
              (sourceFourierSupportProjection_isStarProjection unitSoninScale)
          _ = ‖v‖ := one_mul _
      · calc
          ‖v‖ = ‖doubledShiftAlternatingProduct b v‖ :=
            congrArg norm hfixed.symm
          _ = ‖doubledShiftRadialProjection b
              (sourceFourierSupportProjection unitSoninScale v)‖ := by
            simp only [doubledShiftAlternatingProduct,
              ContinuousLinearMap.mul_apply, hpv]
          _ ≤ ‖doubledShiftRadialProjection b‖ *
              ‖sourceFourierSupportProjection unitSoninScale v‖ :=
            (doubledShiftRadialProjection b).le_opNorm _
          _ ≤ 1 * ‖sourceFourierSupportProjection unitSoninScale v‖ := by
            gcongr
            exact IsStarProjection.norm_le _
              (doubledShiftRadialProjection_isStarProjection b)
          _ = ‖sourceFourierSupportProjection unitSoninScale v‖ := one_mul _
    change v ∈ doubledShiftRadialClosedSubspace b ∧
      v ∈ ccm24ArchimedeanFourierSupportClosedSubspace unitSoninScale
    refine ⟨(Submodule.starProjection_eq_self_iff).mp hpv, ?_⟩
    exact (Submodule.mem_iff_norm_starProjection
      (ccm24ArchimedeanFourierSupportClosedSubspace unitSoninScale).toSubmodule v).mpr hqnorm
  · exact doubledShiftAlternatingProduct_fixed_of_mem_intersection b

/-- The alternating product is a contraction on every carrier vector. -/
theorem doubledShiftAlternatingProduct_apply_norm_le
    (b : ℝ) (v : Carrier) :
    ‖doubledShiftAlternatingProduct b v‖ ≤ ‖v‖ := by
  calc
    ‖doubledShiftAlternatingProduct b v‖ ≤
        ‖doubledShiftAlternatingProduct b‖ * ‖v‖ :=
      (doubledShiftAlternatingProduct b).le_opNorm v
    _ ≤ 1 * ‖v‖ := by
      gcongr
      exact doubledShiftAlternatingProduct_norm_le_one b
    _ = ‖v‖ := one_mul _

/-- Every alternating power is a contraction on each vector. -/
theorem doubledShiftAlternatingProduct_pow_apply_norm_le
    (b : ℝ) (v : Carrier) (n : ℕ) :
    ‖((doubledShiftAlternatingProduct b) ^ n) v‖ ≤ ‖v‖ := by
  calc
    ‖((doubledShiftAlternatingProduct b) ^ n) v‖ ≤
        ‖(doubledShiftAlternatingProduct b) ^ n‖ * ‖v‖ :=
      ((doubledShiftAlternatingProduct b) ^ n).le_opNorm v
    _ ≤ 1 * ‖v‖ := by
      gcongr
      exact norm_pow_le_one_of_norm_le_one
        (doubledShiftAlternatingProduct_norm_le_one b) n
    _ = ‖v‖ := one_mul _

/-- The scalar norm energy of an alternating power orbit is antitone. -/
theorem doubledShiftAlternatingProduct_pow_apply_norm_antitone
    (b : ℝ) (v : Carrier) :
    Antitone (fun n : ℕ => ‖((doubledShiftAlternatingProduct b) ^ n) v‖) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [pow_succ']
  simpa only [ContinuousLinearMap.mul_apply] using
    doubledShiftAlternatingProduct_apply_norm_le b
      (((doubledShiftAlternatingProduct b) ^ n) v)

/-- The scalar norm energy has an explicit monotone-convergence endpoint.
This is only a scalar energy limit; identifying the vector limit with the
intersection projection remains the open angle-free theorem. -/
theorem doubledShiftAlternatingProduct_pow_apply_norm_tendsto_ciInf
    (b : ℝ) (v : Carrier) :
    Filter.Tendsto
       (fun n : ℕ => ‖((doubledShiftAlternatingProduct b) ^ n) v‖)
      Filter.atTop
       (nhds (⨅ n : ℕ, ‖((doubledShiftAlternatingProduct b) ^ n) v‖)) := by
  apply tendsto_atTop_ciInf
    (doubledShiftAlternatingProduct_pow_apply_norm_antitone b v)
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact norm_nonneg _

theorem doubledShiftAlternatingProduct_pow_distance_antitone_to_intersection
    (b : ℝ) {v z : Carrier}
    (hz : z ∈ doubledShiftSoninClosedSubspace b) :
    Antitone (fun n : ℕ =>
      ‖((doubledShiftAlternatingProduct b) ^ n) v - z‖) := by
  apply antitone_nat_of_succ_le
  intro n
  have hstep := doubledShiftAlternatingProduct_apply_norm_le b
    (((doubledShiftAlternatingProduct b) ^ n) v - z)
  have hzfix : doubledShiftAlternatingProduct b z = z :=
    doubledShiftAlternatingProduct_fixed_of_mem_intersection b hz
  simpa only [pow_succ', map_sub, hzfix] using hstep

theorem doubledShiftAlternatingProduct_pow_distance_to_intersection_tendsto_ciInf
    (b : ℝ) {v z : Carrier}
    (hz : z ∈ doubledShiftSoninClosedSubspace b) :
    Filter.Tendsto
      (fun n : ℕ =>
        ‖((doubledShiftAlternatingProduct b) ^ n) v - z‖)
      Filter.atTop (nhds (⨅ n : ℕ,
        ‖((doubledShiftAlternatingProduct b) ^ n) v - z‖)) := by
  apply tendsto_atTop_ciInf
    (doubledShiftAlternatingProduct_pow_distance_antitone_to_intersection b hz)
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact norm_nonneg _

theorem doubledShiftAlternatingProduct_tendsto_intersectionProjection_of_fejer_exhaustion
    (b : ℝ) (v : Carrier)
    (hzero : (⨅ n : ℕ,
        ‖((doubledShiftAlternatingProduct b) ^ n) v -
          doubledShiftSoninIntersectionProjection b v‖) = 0) :
    Filter.Tendsto
      (fun n : ℕ => ((doubledShiftAlternatingProduct b) ^ n) v)
      Filter.atTop (nhds (doubledShiftSoninIntersectionProjection b v)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hrmem : doubledShiftSoninIntersectionProjection b v ∈
      doubledShiftSoninClosedSubspace b :=
    (doubledShiftSoninClosedSubspace b).toSubmodule.starProjection_apply_mem v
  have hdist := doubledShiftAlternatingProduct_pow_distance_to_intersection_tendsto_ciInf
    b (v := v) (z := doubledShiftSoninIntersectionProjection b v) hrmem
  simpa only [hzero] using hdist

/-- On the radial subspace, one alternating step loses exactly the sum of
the Fourier defect and the radial defect of the Fourier projection. -/
theorem doubledShiftAlternatingProduct_norm_sq_add_defects
    (b : ℝ) {v : Carrier}
    (hv : v ∈ doubledShiftRadialClosedSubspace b) :
    ‖v‖ ^ 2 =
      ‖doubledShiftAlternatingProduct b v‖ ^ 2 +
        ‖Submodule.starProjection ((doubledShiftRadialClosedSubspace b).toSubmoduleᗮ)
            (sourceFourierSupportProjection unitSoninScale v)‖ ^ 2 +
        ‖Submodule.starProjection
            ((ccm24ArchimedeanFourierSupportClosedSubspace unitSoninScale).toSubmoduleᗮ)
            v‖ ^ 2 := by
  let P := (doubledShiftRadialClosedSubspace b).toSubmodule
  let Q := (ccm24ArchimedeanFourierSupportClosedSubspace unitSoninScale).toSubmodule
  have hpv : P.starProjection v = v :=
    Submodule.starProjection_eq_self_iff.mpr hv
  have hq := Q.norm_sq_eq_add_norm_sq_starProjection v
  have hpq := P.norm_sq_eq_add_norm_sq_starProjection (Q.starProjection v)
  have hT : doubledShiftAlternatingProduct b v =
      P.starProjection (Q.starProjection v) := by
    change P.starProjection (Q.starProjection (P.starProjection v)) =
      P.starProjection (Q.starProjection v)
    rw [hpv]
  have hqdef : sourceFourierSupportProjection unitSoninScale v = Q.starProjection v := rfl
  rw [hT, hqdef]
  dsimp only [P, Q] at hq hpq ⊢
  nlinarith

/-- The two one-step orthogonal defects, recorded as one scalar energy. -/
noncomputable def doubledShiftAlternatingEnergyDefect (b : ℝ) (v : Carrier) : ℝ :=
  ‖Submodule.starProjection ((doubledShiftRadialClosedSubspace b).toSubmoduleᗮ)
      (sourceFourierSupportProjection unitSoninScale v)‖ ^ 2 +
    ‖Submodule.starProjection
        ((ccm24ArchimedeanFourierSupportClosedSubspace unitSoninScale).toSubmoduleᗮ)
        v‖ ^ 2

theorem doubledShiftAlternatingEnergyDefect_eq_norm_sq_sub
    (b : ℝ) {v : Carrier}
    (hv : v ∈ doubledShiftRadialClosedSubspace b) :
    doubledShiftAlternatingEnergyDefect b v =
      ‖v‖ ^ 2 - ‖doubledShiftAlternatingProduct b v‖ ^ 2 := by
  unfold doubledShiftAlternatingEnergyDefect
  have h := doubledShiftAlternatingProduct_norm_sq_add_defects b hv
  nlinarith

theorem doubledShiftAlternatingProduct_pow_mem_radial
    (b : ℝ) {v : Carrier}
    (hv : v ∈ doubledShiftRadialClosedSubspace b) (n : ℕ) :
    ((doubledShiftAlternatingProduct b) ^ n) v ∈
      doubledShiftRadialClosedSubspace b := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
      rw [pow_succ']
      exact (doubledShiftRadialClosedSubspace b).toSubmodule.starProjection_apply_mem _

theorem doubledShiftAlternatingEnergyDefect_sum_range
    (b : ℝ) {v : Carrier}
    (hv : v ∈ doubledShiftRadialClosedSubspace b) (n : ℕ) :
    ∑ k ∈ Finset.range n,
        doubledShiftAlternatingEnergyDefect b
          (((doubledShiftAlternatingProduct b) ^ k) v) =
      ‖v‖ ^ 2 - ‖((doubledShiftAlternatingProduct b) ^ n) v‖ ^ 2 := by
  have hrad (k : ℕ) :
      ((doubledShiftAlternatingProduct b) ^ k) v ∈
        doubledShiftRadialClosedSubspace b :=
    doubledShiftAlternatingProduct_pow_mem_radial b hv k
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have hstep := doubledShiftAlternatingEnergyDefect_eq_norm_sq_sub
        b (hrad n)
      rw [hstep]
      have hpow :
          ((doubledShiftAlternatingProduct b) ^ (n + 1)) v =
            doubledShiftAlternatingProduct b
              (((doubledShiftAlternatingProduct b) ^ n) v) := by
        rw [pow_succ']
        rfl
      rw [hpow]
      ring

theorem doubledShiftAlternatingEnergyDefect_summable
    (b : ℝ) {v : Carrier}
    (hv : v ∈ doubledShiftRadialClosedSubspace b) :
    Summable (fun n : ℕ =>
      doubledShiftAlternatingEnergyDefect b
        (((doubledShiftAlternatingProduct b) ^ n) v)) := by
  refine summable_of_sum_range_le (c := ‖v‖ ^ 2) ?_ ?_
  · intro n
    unfold doubledShiftAlternatingEnergyDefect
    exact add_nonneg (sq_nonneg _) (sq_nonneg _)
  · intro n
    rw [doubledShiftAlternatingEnergyDefect_sum_range b hv n]
    linarith [sq_nonneg ‖((doubledShiftAlternatingProduct b) ^ n) v‖]

theorem doubledShiftAlternatingEnergyDefect_tendsto_zero
    (b : ℝ) {v : Carrier}
    (hv : v ∈ doubledShiftRadialClosedSubspace b) :
    Filter.Tendsto
      (fun n : ℕ =>
        doubledShiftAlternatingEnergyDefect b
          (((doubledShiftAlternatingProduct b) ^ n) v))
      Filter.atTop (nhds 0) :=
  (doubledShiftAlternatingEnergyDefect_summable b hv).tendsto_atTop_zero

theorem doubledShiftAlternatingFourierDefect_tendsto_zero
    (b : ℝ) {v : Carrier}
    (hv : v ∈ doubledShiftRadialClosedSubspace b) :
    Filter.Tendsto
      (fun n : ℕ =>
        ‖Submodule.starProjection ((doubledShiftRadialClosedSubspace b).toSubmoduleᗮ)
            (sourceFourierSupportProjection unitSoninScale
              (((doubledShiftAlternatingProduct b) ^ n) v))‖ ^ 2)
      Filter.atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    exact sq_nonneg _
  · intro n
    change
      ‖Submodule.starProjection ((doubledShiftRadialClosedSubspace b).toSubmoduleᗮ)
          (sourceFourierSupportProjection unitSoninScale
            (((doubledShiftAlternatingProduct b) ^ n) v))‖ ^ 2 ≤
        ‖Submodule.starProjection ((doubledShiftRadialClosedSubspace b).toSubmoduleᗮ)
            (sourceFourierSupportProjection unitSoninScale
              (((doubledShiftAlternatingProduct b) ^ n) v))‖ ^ 2 +
          ‖Submodule.starProjection
              ((ccm24ArchimedeanFourierSupportClosedSubspace unitSoninScale).toSubmoduleᗮ)
              (((doubledShiftAlternatingProduct b) ^ n) v)‖ ^ 2
    exact le_add_of_nonneg_right (sq_nonneg _)
  · simpa only [doubledShiftAlternatingEnergyDefect] using
      doubledShiftAlternatingEnergyDefect_tendsto_zero b hv

theorem doubledShiftAlternatingRadialDefect_tendsto_zero
    (b : ℝ) {v : Carrier}
    (hv : v ∈ doubledShiftRadialClosedSubspace b) :
    Filter.Tendsto
      (fun n : ℕ =>
        ‖Submodule.starProjection
            ((ccm24ArchimedeanFourierSupportClosedSubspace unitSoninScale).toSubmoduleᗮ)
            (((doubledShiftAlternatingProduct b) ^ n) v)‖ ^ 2)
      Filter.atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    exact sq_nonneg _
  · intro n
    change
      ‖Submodule.starProjection
          ((ccm24ArchimedeanFourierSupportClosedSubspace unitSoninScale).toSubmoduleᗮ)
          (((doubledShiftAlternatingProduct b) ^ n) v)‖ ^ 2 ≤
        ‖Submodule.starProjection ((doubledShiftRadialClosedSubspace b).toSubmoduleᗮ)
            (sourceFourierSupportProjection unitSoninScale
              (((doubledShiftAlternatingProduct b) ^ n) v))‖ ^ 2 +
          ‖Submodule.starProjection
              ((ccm24ArchimedeanFourierSupportClosedSubspace unitSoninScale).toSubmoduleᗮ)
              (((doubledShiftAlternatingProduct b) ^ n) v)‖ ^ 2
    exact le_add_of_nonneg_left (sq_nonneg _)
  · simpa only [doubledShiftAlternatingEnergyDefect] using
      doubledShiftAlternatingEnergyDefect_tendsto_zero b hv

theorem norm_tendsto_zero_of_norm_sq_tendsto_zero
    {w : ℕ → Carrier}
    (h : Filter.Tendsto (fun n => ‖w n‖ ^ 2) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ‖w n‖) Filter.atTop (nhds 0) := by
  have hs := h.sqrt
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_zero]
    using hs

theorem norm_orthogonalComplement_starProjection_eq_norm_sub_starProjection
    {K : Submodule ℂ Carrier} [K.HasOrthogonalProjection] (x : Carrier) :
    ‖Kᗮ.starProjection x‖ = ‖x - K.starProjection x‖ := by
  rw [Submodule.starProjection_orthogonal']
  rfl

theorem orthogonalComplement_starProjection_apply_eq_sub_starProjection
    {K : Submodule ℂ Carrier} [K.HasOrthogonalProjection] (x : Carrier) :
    Kᗮ.starProjection x = x - K.starProjection x := by
  rw [Submodule.starProjection_orthogonal']
  rfl

theorem doubledShiftAlternatingProduct_sub_norm_le_defect_norms
    (b : ℝ) {v : Carrier}
    (hv : v ∈ doubledShiftRadialClosedSubspace b) :
    ‖doubledShiftAlternatingProduct b v - v‖ ≤
      ‖Submodule.starProjection ((doubledShiftRadialClosedSubspace b).toSubmoduleᗮ)
          (sourceFourierSupportProjection unitSoninScale v)‖ +
        ‖Submodule.starProjection
            ((ccm24ArchimedeanFourierSupportClosedSubspace unitSoninScale).toSubmoduleᗮ)
            v‖ := by
  let P := (doubledShiftRadialClosedSubspace b).toSubmodule
  let Q := (ccm24ArchimedeanFourierSupportClosedSubspace unitSoninScale).toSubmodule
  have hpv : P.starProjection v = v :=
    Submodule.starProjection_eq_self_iff.mpr hv
  have hqv : Q.starProjection v = sourceFourierSupportProjection unitSoninScale v := rfl
  have hT : doubledShiftAlternatingProduct b v =
      P.starProjection (Q.starProjection v) := by
    change P.starProjection (Q.starProjection (P.starProjection v)) =
      P.starProjection (Q.starProjection v)
    rw [hpv]
  have hPdef :
      Pᗮ.starProjection (Q.starProjection v) =
        Q.starProjection v - P.starProjection (Q.starProjection v) :=
    orthogonalComplement_starProjection_apply_eq_sub_starProjection
      (K := P) (Q.starProjection v)
  have hQdef : Qᗮ.starProjection v = v - Q.starProjection v :=
    orthogonalComplement_starProjection_apply_eq_sub_starProjection
      (K := Q) v
  rw [hT]
  calc
    ‖P.starProjection (Q.starProjection v) - v‖ =
        ‖(P.starProjection (Q.starProjection v) - Q.starProjection v) +
            (Q.starProjection v - v)‖ := by abel
    _ ≤ ‖P.starProjection (Q.starProjection v) - Q.starProjection v‖ +
          ‖Q.starProjection v - v‖ := norm_add_le _ _
    _ = ‖Pᗮ.starProjection (Q.starProjection v)‖ +
          ‖Qᗮ.starProjection v‖ := by
      rw [hPdef, hQdef]
      simp only [norm_sub_rev]
    _ = ‖Submodule.starProjection Pᗮ
          (sourceFourierSupportProjection unitSoninScale v)‖ +
          ‖Submodule.starProjection Qᗮ v‖ := by
      rw [hqv]

theorem doubledShiftAlternatingFourierDefect_norm_tendsto_zero
    (b : ℝ) {v : Carrier}
    (hv : v ∈ doubledShiftRadialClosedSubspace b) :
    Filter.Tendsto
      (fun n : ℕ =>
        ‖Submodule.starProjection ((doubledShiftRadialClosedSubspace b).toSubmoduleᗮ)
            (sourceFourierSupportProjection unitSoninScale
              (((doubledShiftAlternatingProduct b) ^ n) v))‖)
      Filter.atTop (nhds 0) :=
  norm_tendsto_zero_of_norm_sq_tendsto_zero
    (doubledShiftAlternatingFourierDefect_tendsto_zero b hv)

theorem doubledShiftAlternatingRadialDefect_norm_tendsto_zero
    (b : ℝ) {v : Carrier}
    (hv : v ∈ doubledShiftRadialClosedSubspace b) :
    Filter.Tendsto
      (fun n : ℕ =>
        ‖Submodule.starProjection
            ((ccm24ArchimedeanFourierSupportClosedSubspace unitSoninScale).toSubmoduleᗮ)
            (((doubledShiftAlternatingProduct b) ^ n) v)‖)
      Filter.atTop (nhds 0) :=
  norm_tendsto_zero_of_norm_sq_tendsto_zero
    (doubledShiftAlternatingRadialDefect_tendsto_zero b hv)

theorem doubledShiftAlternatingProduct_pow_step_norm_tendsto_zero
    (b : ℝ) {v : Carrier}
    (hv : v ∈ doubledShiftRadialClosedSubspace b) :
    Filter.Tendsto
      (fun n : ℕ =>
        ‖((doubledShiftAlternatingProduct b) ^ (n + 1)) v -
            ((doubledShiftAlternatingProduct b) ^ n) v‖)
      Filter.atTop (nhds 0) := by
  have hfour := doubledShiftAlternatingFourierDefect_norm_tendsto_zero b hv
  have hrad := doubledShiftAlternatingRadialDefect_norm_tendsto_zero b hv
  have hsum := hfour.add hrad
  apply squeeze_zero
  · intro n
    exact norm_nonneg _
  · intro n
    have hbound := doubledShiftAlternatingProduct_sub_norm_le_defect_norms b
      (doubledShiftAlternatingProduct_pow_mem_radial b hv n)
    simpa only [pow_succ'] using hbound
  · simpa only [add_zero] using hsum

/-- The alternating product also fixes the intersection projection on the
left.  This is the adjoint of the already-formal right fixing identity; it is
not a spectral-gap assertion. -/
theorem intersectionProjection_comp_doubledShiftAlternatingProduct
    (b : ℝ) :
    doubledShiftSoninIntersectionProjection b *
        doubledShiftAlternatingProduct b =
      doubledShiftSoninIntersectionProjection b := by
  have h := congrArg ContinuousLinearMap.adjoint
    (doubledShiftAlternatingProduct_comp_intersectionProjection b)
  simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.adjoint_comp,
    (doubledShiftAlternatingProduct_isSelfAdjoint b).adjoint_eq,
    (doubledShiftSoninIntersectionProjection_isStarProjection b).isSelfAdjoint.adjoint_eq]
    using h

theorem intersectionProjection_comp_doubledShiftAlternatingProduct_pow
    (b : ℝ) (n : ℕ) :
    doubledShiftSoninIntersectionProjection b *
        (doubledShiftAlternatingProduct b) ^ n =
      doubledShiftSoninIntersectionProjection b := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ']
      calc
        doubledShiftSoninIntersectionProjection b *
              (doubledShiftAlternatingProduct b *
                (doubledShiftAlternatingProduct b) ^ n) =
            (doubledShiftSoninIntersectionProjection b *
              doubledShiftAlternatingProduct b) *
                (doubledShiftAlternatingProduct b) ^ n := by
                  rw [mul_assoc]
        _ = doubledShiftSoninIntersectionProjection b := by
          rw [intersectionProjection_comp_doubledShiftAlternatingProduct, ih]

theorem doubledShiftAlternatingProduct_pow_norm_projection_le
    (b : ℝ) (v : Carrier) (n : ℕ) :
    ‖doubledShiftSoninIntersectionProjection b v‖ ≤
      ‖((doubledShiftAlternatingProduct b) ^ n) v‖ := by
  have hfix : doubledShiftSoninIntersectionProjection b
      (((doubledShiftAlternatingProduct b) ^ n) v) =
      doubledShiftSoninIntersectionProjection b v := by
    simpa only [ContinuousLinearMap.mul_apply] using
      congrArg (fun L : Op => L v)
        (intersectionProjection_comp_doubledShiftAlternatingProduct_pow b n)
  calc
    ‖doubledShiftSoninIntersectionProjection b v‖ =
        ‖doubledShiftSoninIntersectionProjection b
          (((doubledShiftAlternatingProduct b) ^ n) v)‖ :=
      congrArg norm hfix.symm
    _ ≤ ‖((doubledShiftAlternatingProduct b) ^ n) v‖ := by
      exact Submodule.norm_starProjection_apply_le
        ((doubledShiftSoninClosedSubspace b).toSubmodule) _

theorem doubledShiftAlternatingProduct_pow_norm_projection_le_ciInf
    (b : ℝ) (v : Carrier) :
    ‖doubledShiftSoninIntersectionProjection b v‖ ≤
      (⨅ n : ℕ, ‖((doubledShiftAlternatingProduct b) ^ n) v‖) := by
  apply le_ciInf
  intro n
  exact doubledShiftAlternatingProduct_pow_norm_projection_le b v n

theorem doubledShiftAlternatingProduct_ciInf_norm_le_projection_of_sq_tendsto
    (b : ℝ) (v : Carrier)
    (hlim : Filter.Tendsto
      (fun n : ℕ => ‖((doubledShiftAlternatingProduct b) ^ n) v‖ ^ 2)
      Filter.atTop
      (nhds (‖doubledShiftSoninIntersectionProjection b v‖ ^ 2))) :
    (⨅ n : ℕ, ‖((doubledShiftAlternatingProduct b) ^ n) v‖) ≤
      ‖doubledShiftSoninIntersectionProjection b v‖ := by
  let c : ℝ := ⨅ n : ℕ, ‖((doubledShiftAlternatingProduct b) ^ n) v‖
  have hnorm : Filter.Tendsto
      (fun n : ℕ => ‖((doubledShiftAlternatingProduct b) ^ n) v‖)
      Filter.atTop (nhds c) := by
    simpa only [c] using
      doubledShiftAlternatingProduct_pow_apply_norm_tendsto_ciInf b v
  have hnormsq : Filter.Tendsto
      (fun n : ℕ => ‖((doubledShiftAlternatingProduct b) ^ n) v‖ ^ 2)
      Filter.atTop (nhds (c ^ 2)) := by
    simpa only [Function.comp_apply] using hnorm.pow 2
  have hsq : c ^ 2 = ‖doubledShiftSoninIntersectionProjection b v‖ ^ 2 :=
    tendsto_nhds_unique hnormsq hlim
  have hc : 0 ≤ c := by
    dsimp [c]
    exact le_ciInf (fun n => norm_nonneg _)
  have hr : 0 ≤ ‖doubledShiftSoninIntersectionProjection b v‖ := norm_nonneg _
  dsimp [c] at hsq hc ⊢
  nlinarith

theorem doubledShiftAlternatingProduct_sq_norm_tendsto_projection_of_defect_tsum_eq
    (b : ℝ) {v : Carrier}
    (hv : v ∈ doubledShiftRadialClosedSubspace b)
    (hexh : (∑' k : ℕ, doubledShiftAlternatingEnergyDefect b
        (((doubledShiftAlternatingProduct b) ^ k) v)) =
      ‖v‖ ^ 2 - ‖doubledShiftSoninIntersectionProjection b v‖ ^ 2) :
    Filter.Tendsto
      (fun n : ℕ => ‖((doubledShiftAlternatingProduct b) ^ n) v‖ ^ 2)
      Filter.atTop
      (nhds (‖doubledShiftSoninIntersectionProjection b v‖ ^ 2)) := by
  let d : ℕ → ℝ := fun k => doubledShiftAlternatingEnergyDefect b
    (((doubledShiftAlternatingProduct b) ^ k) v)
  have hd : Summable d := by
    simpa only [d] using doubledShiftAlternatingEnergyDefect_summable b hv
  have hsum : Filter.Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.range n, d k)
      Filter.atTop (nhds (∑' k : ℕ, d k)) :=
    hd.hasSum.tendsto_sum_nat
  have hconst : Filter.Tendsto
      (fun _ : ℕ => ‖v‖ ^ 2)
      Filter.atTop (nhds (‖v‖ ^ 2)) :=
    tendsto_const_nhds
  have hnormsq : Filter.Tendsto
      (fun n : ℕ => ‖((doubledShiftAlternatingProduct b) ^ n) v‖ ^ 2)
      Filter.atTop (nhds (‖v‖ ^ 2 - ∑' k : ℕ, d k)) := by
    have hdiff := hconst.sub hsum
    apply hdiff.congr'
    filter_upwards [] with n
    rw [doubledShiftAlternatingEnergyDefect_sum_range b hv n]
    ring
  convert hnormsq using 1 <;> simp only [d] <;> rw [hexh] <;> ring

theorem doubledShiftAlternatingProduct_defect_tsum_eq_iff_scalar_endpoint
    (b : ℝ) {v : Carrier}
    (hv : v ∈ doubledShiftRadialClosedSubspace b) :
    ((∑' k : ℕ, doubledShiftAlternatingEnergyDefect b
        (((doubledShiftAlternatingProduct b) ^ k) v)) =
      ‖v‖ ^ 2 - ‖doubledShiftSoninIntersectionProjection b v‖ ^ 2) ↔
      ((⨅ n : ℕ, ‖((doubledShiftAlternatingProduct b) ^ n) v‖) =
        ‖doubledShiftSoninIntersectionProjection b v‖) := by
  let d : ℕ → ℝ := fun k => doubledShiftAlternatingEnergyDefect b
    (((doubledShiftAlternatingProduct b) ^ k) v)
  have hd : Summable d := by
    simpa only [d] using doubledShiftAlternatingEnergyDefect_summable b hv
  constructor
  · intro hexh
    have hsq := doubledShiftAlternatingProduct_sq_norm_tendsto_projection_of_defect_tsum_eq
      b hv (by simpa only [d] using hexh)
    have hupper := doubledShiftAlternatingProduct_ciInf_norm_le_projection_of_sq_tendsto
      b v hsq
    exact le_antisymm hupper
      (doubledShiftAlternatingProduct_pow_norm_projection_le_ciInf b v)
  · intro hscalar
    have hnorm := doubledShiftAlternatingProduct_pow_apply_norm_tendsto_ciInf b v
    rw [hscalar] at hnorm
    have hnormsq := hnorm.pow 2
    have hdiff : Filter.Tendsto
        (fun n : ℕ => ‖v‖ ^ 2 -
          ‖((doubledShiftAlternatingProduct b) ^ n) v‖ ^ 2)
        Filter.atTop
        (nhds (‖v‖ ^ 2 -
          ‖doubledShiftSoninIntersectionProjection b v‖ ^ 2)) :=
      tendsto_const_nhds.sub hnormsq
    have hsum_to_diff : Filter.Tendsto
        (fun n : ℕ => ∑ k ∈ Finset.range n, d k)
        Filter.atTop
        (nhds (‖v‖ ^ 2 -
          ‖doubledShiftSoninIntersectionProjection b v‖ ^ 2)) := by
      apply hdiff.congr'
      filter_upwards [] with n
      rw [doubledShiftAlternatingEnergyDefect_sum_range b hv n]
    have hsum_to_tsum : Filter.Tendsto
        (fun n : ℕ => ∑ k ∈ Finset.range n, d k)
        Filter.atTop (nhds (∑' k : ℕ, d k)) :=
      hd.hasSum.tendsto_sum_nat
    have htsum : (∑' k : ℕ, d k) =
        ‖v‖ ^ 2 - ‖doubledShiftSoninIntersectionProjection b v‖ ^ 2 :=
      tendsto_nhds_unique hsum_to_tsum hsum_to_diff
    simpa only [d] using htsum

theorem doubledShiftAlternatingProduct_pow_distance_sq_eq_norm_sq_sub_projection
    (b : ℝ) (v : Carrier) (n : ℕ) :
    ‖((doubledShiftAlternatingProduct b) ^ n) v -
        doubledShiftSoninIntersectionProjection b v‖ ^ 2 =
      ‖((doubledShiftAlternatingProduct b) ^ n) v‖ ^ 2 -
        ‖doubledShiftSoninIntersectionProjection b v‖ ^ 2 := by
  let P := (doubledShiftSoninClosedSubspace b).toSubmodule
  let x := ((doubledShiftAlternatingProduct b) ^ n) v
  have hpyth := P.norm_sq_eq_add_norm_sq_starProjection x
  have hPfix : P.starProjection x = P.starProjection v := by
    change doubledShiftSoninIntersectionProjection b x =
      doubledShiftSoninIntersectionProjection b v
    simpa only [ContinuousLinearMap.mul_apply] using
      congrArg (fun L : Op => L v)
        (intersectionProjection_comp_doubledShiftAlternatingProduct_pow b n)
  have hresid : Pᗮ.starProjection x =
      x - P.starProjection x :=
    orthogonalComplement_starProjection_apply_eq_sub_starProjection (K := P) x
  change ‖x - P.starProjection v‖ ^ 2 =
      ‖x‖ ^ 2 - ‖P.starProjection v‖ ^ 2
  rw [hPfix] at hpyth
  rw [hresid] at hpyth
  rw [hPfix] at hpyth
  nlinarith

theorem doubledShiftAlternatingProduct_tendsto_intersectionProjection_of_scalar_endpoint
    (b : ℝ) (v : Carrier)
    (hscalar : (⨅ n : ℕ,
        ‖((doubledShiftAlternatingProduct b) ^ n) v‖) =
      ‖doubledShiftSoninIntersectionProjection b v‖) :
    Filter.Tendsto
      (fun n : ℕ => ((doubledShiftAlternatingProduct b) ^ n) v)
      Filter.atTop (nhds (doubledShiftSoninIntersectionProjection b v)) := by
  have hnorm := doubledShiftAlternatingProduct_pow_apply_norm_tendsto_ciInf b v
  rw [hscalar] at hnorm
  have hnormsq := hnorm.pow 2
  have hconst : Filter.Tendsto
      (fun _ : ℕ => ‖doubledShiftSoninIntersectionProjection b v‖ ^ 2)
      Filter.atTop
      (nhds (‖doubledShiftSoninIntersectionProjection b v‖ ^ 2)) :=
    tendsto_const_nhds
  have hdiff : Filter.Tendsto
      (fun n : ℕ => ‖((doubledShiftAlternatingProduct b) ^ n) v‖ ^ 2 -
        ‖doubledShiftSoninIntersectionProjection b v‖ ^ 2)
      Filter.atTop (nhds 0) := by
    simpa only [sub_self] using hnormsq.sub hconst
  have hdist_sq : Filter.Tendsto
      (fun n : ℕ => ‖((doubledShiftAlternatingProduct b) ^ n) v -
        doubledShiftSoninIntersectionProjection b v‖ ^ 2)
      Filter.atTop (nhds 0) := by
    apply hdiff.congr'
    filter_upwards [] with n
    exact (doubledShiftAlternatingProduct_pow_distance_sq_eq_norm_sq_sub_projection
      b v n).symm
  have hdist := norm_tendsto_zero_of_norm_sq_tendsto_zero hdist_sq
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [sub_eq_add_neg] using hdist

theorem doubledShiftAlternatingProduct_defect_tsum_eq_iff_strong_endpoint
    (b : ℝ) {v : Carrier}
    (hv : v ∈ doubledShiftRadialClosedSubspace b) :
    ((∑' k : ℕ, doubledShiftAlternatingEnergyDefect b
        (((doubledShiftAlternatingProduct b) ^ k) v)) =
      ‖v‖ ^ 2 - ‖doubledShiftSoninIntersectionProjection b v‖ ^ 2) ↔
      Filter.Tendsto
        (fun n : ℕ => ((doubledShiftAlternatingProduct b) ^ n) v)
        Filter.atTop (nhds (doubledShiftSoninIntersectionProjection b v)) := by
  constructor
  · intro hexh
    apply doubledShiftAlternatingProduct_tendsto_intersectionProjection_of_scalar_endpoint
      b v
    exact (doubledShiftAlternatingProduct_defect_tsum_eq_iff_scalar_endpoint b hv).mp
      hexh
  · intro hlim
    apply (doubledShiftAlternatingProduct_defect_tsum_eq_iff_scalar_endpoint b hv).mpr
    have hnorm := doubledShiftAlternatingProduct_pow_apply_norm_tendsto_ciInf b v
    have hnorm_lim := hlim.norm
    exact tendsto_nhds_unique hnorm hnorm_lim

theorem doubledShiftAlternatingProduct_weighted_hs_energy_tendsto_zero_of_defect_tsum
    {ι : Type*}
    (b : ℝ) (basis : HilbertBasis ι ℂ Carrier)
    (factor : Carrier →L[ℂ] Carrier)
    (hfactor : Summable (fun i => ‖factor (basis i)‖ ^ 2))
    (hcolumns : ∀ i,
      factor (basis i) ∈ doubledShiftRadialClosedSubspace b ∧
      (∑' k : ℕ, doubledShiftAlternatingEnergyDefect b
          (((doubledShiftAlternatingProduct b) ^ k) (factor (basis i)))) =
        ‖factor (basis i)‖ ^ 2 -
          ‖doubledShiftSoninIntersectionProjection b
            (factor (basis i))‖ ^ 2) :
    Filter.Tendsto
      (fun n : ℕ => ∑' i,
        ‖(((doubledShiftAlternatingProduct b) ^ n -
            doubledShiftSoninIntersectionProjection b)
          (factor (basis i)))‖ ^ 2)
      Filter.atTop (nhds 0) := by
  let operators : ℕ → Carrier →L[ℂ] Carrier := fun n =>
    (doubledShiftAlternatingProduct b) ^ n
  let limit : Carrier →L[ℂ] Carrier :=
    doubledShiftSoninIntersectionProjection b
  have hpoint : ∀ i,
      Filter.Tendsto
        (fun n => (operators n - limit) (factor (basis i)))
        Filter.atTop (nhds 0) := by
    intro i
    rcases hcolumns i with ⟨hri, hsum⟩
    have hstrong :=
      (doubledShiftAlternatingProduct_defect_tsum_eq_iff_strong_endpoint
        b hri).mp hsum
    have hdiff : Filter.Tendsto
        (fun n : ℕ =>
          ((doubledShiftAlternatingProduct b) ^ n) (factor (basis i)) -
            doubledShiftSoninIntersectionProjection b (factor (basis i)))
        Filter.atTop (nhds 0) :=
      tendsto_sub_nhds_zero_iff.mpr hstrong
    simpa only [operators, limit, ContinuousLinearMap.sub_apply] using hdiff
  have hoperators : ∀ᶠ n : ℕ in Filter.atTop, ‖operators n‖ ≤ 1 := by
    filter_upwards [] with n
    dsimp [operators]
    exact norm_pow_le_one_of_norm_le_one
      (doubledShiftAlternatingProduct_norm_le_one b) n
  have hlimit : ‖limit‖ ≤ 1 := by
    dsimp [limit]
    exact IsStarProjection.norm_le _
      (doubledShiftSoninIntersectionProjection_isStarProjection b)
  simpa only [operators, limit, ContinuousLinearMap.sub_apply] using
    tendsto_hilbertSchmidt_energy_of_strong_convergence
      basis factor operators limit Filter.atTop hfactor hpoint hoperators hlimit

theorem doubledShiftAlternatingProduct_tendsto_limit_eq_intersectionProjection
    (b : ℝ) {v w : Carrier}
    (hlim : Filter.Tendsto
      (fun n : ℕ => ((doubledShiftAlternatingProduct b) ^ n) v)
      Filter.atTop (nhds w)) :
    w = doubledShiftSoninIntersectionProjection b v := by
  have hshift : Filter.Tendsto
      (fun n : ℕ => ((doubledShiftAlternatingProduct b) ^ (n + 1)) v)
      Filter.atTop (nhds w) := by
    simpa only [Function.comp_apply] using
      hlim.comp (Filter.tendsto_add_atTop_nat 1)
  have hTlim : Filter.Tendsto
      (fun n : ℕ => doubledShiftAlternatingProduct b
        (((doubledShiftAlternatingProduct b) ^ n) v))
      Filter.atTop
      (nhds (doubledShiftAlternatingProduct b w)) := by
    exact (doubledShiftAlternatingProduct b).continuous.tendsto w |>.comp hlim
  have hTshift : Filter.Tendsto
      (fun n : ℕ => ((doubledShiftAlternatingProduct b) ^ (n + 1)) v)
      Filter.atTop (nhds (doubledShiftAlternatingProduct b w)) := by
    simpa only [pow_succ'] using hTlim
  have hfixed : doubledShiftAlternatingProduct b w = w :=
    tendsto_nhds_unique hTshift hshift
  have hwint : w ∈ doubledShiftSoninClosedSubspace b :=
    (doubledShiftAlternatingProduct_fixed_iff_mem_intersection b w).mp hfixed
  have hrw : doubledShiftSoninIntersectionProjection b w = w :=
    (Submodule.starProjection_eq_self_iff).mpr hwint
  have hPseq : Filter.Tendsto
      (fun n : ℕ => doubledShiftSoninIntersectionProjection b
        (((doubledShiftAlternatingProduct b) ^ n) v))
      Filter.atTop (nhds (doubledShiftSoninIntersectionProjection b v)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [] with n
    simpa only [ContinuousLinearMap.mul_apply] using
      (congrArg (fun L : Op => L v)
        (intersectionProjection_comp_doubledShiftAlternatingProduct_pow b n)).symm
  have hPcont : Filter.Tendsto
      (fun n : ℕ => doubledShiftSoninIntersectionProjection b
        (((doubledShiftAlternatingProduct b) ^ n) v))
      Filter.atTop (nhds (doubledShiftSoninIntersectionProjection b w)) := by
    exact (doubledShiftSoninIntersectionProjection b).continuous.tendsto w |>.comp hlim
  have hPeq : doubledShiftSoninIntersectionProjection b w =
      doubledShiftSoninIntersectionProjection b v :=
    tendsto_nhds_unique hPcont hPseq
  calc
    w = doubledShiftSoninIntersectionProjection b w := hrw.symm
    _ = doubledShiftSoninIntersectionProjection b v := hPeq

/-!
The next bridge is the angle-free replacement for the earlier spectral-gap
socket.  A self-adjoint contraction whose successive differences tend to zero
has no residual oscillatory component: the range of `T - I` is dense in the
orthogonal complement of its fixed space, and the telescoping identity kills
that dense range.  This is the only genuinely new functional-analytic input
in the present R3 campaign; it does not assume a Friedrichs gap.
-/

theorem tendsto_pow_to_starProjection_of_selfAdjoint_contraction_of_step
    {T : Op} (K : Submodule ℂ Carrier) [K.HasOrthogonalProjection]
    (hTself : IsSelfAdjoint T) (hTnorm : ‖T‖ ≤ 1)
    (hTP : T * K.starProjection = K.starProjection)
    (hfixed : ∀ v : Carrier, T v = v ↔ v ∈ K)
    (hstep : ∀ v : Carrier,
      Filter.Tendsto
        (fun n : ℕ => ‖(T ^ (n + 1)) v - (T ^ n) v‖)
        Filter.atTop (nhds 0))
    (v : Carrier) :
    Filter.Tendsto (fun n : ℕ => (T ^ n) v) Filter.atTop
      (nhds (K.starProjection v)) := by
  let P : Op := K.starProjection
  let A : Op := T - 1
  have hPker : P.ker = Kᗮ := by
    simpa only [P] using (Submodule.ker_starProjection K)
  have hAadj : A.adjoint = A := by
    dsimp [A]
    simp only [map_sub, ContinuousLinearMap.adjoint_one, hTself.adjoint_eq]
  have hAker : A.ker = K := by
    ext x
    constructor
    · intro hx
      change A x = 0 at hx
      have hfix : T x = x := by
        dsimp [A] at hx
        exact sub_eq_zero.mp hx
      exact (hfixed x).mp hfix
    · intro hx
      change A x = 0
      have hfix : T x = x := (hfixed x).mpr hx
      dsimp [A]
      exact sub_eq_zero.mpr hfix
  have hArangeClosure : A.range.topologicalClosure = Kᗮ := by
    calc
      A.range.topologicalClosure = A.adjoint.kerᗮ := by
        simpa only [ContinuousLinearMap.adjoint_adjoint] using
          (A.adjoint.orthogonal_ker).symm
      _ = Kᗮ := by rw [hAadj, hAker]
  have hUEq : UniformEquicontinuous
      (fun n : ℕ => fun x : Carrier => (T ^ n) x) := by
    apply Metric.uniformEquicontinuous_of_continuity_modulus
      (fun r : ℝ => r) Filter.tendsto_id
    intro x y n
    calc
      dist ((T ^ n) x) ((T ^ n) y) = ‖(T ^ n) (x - y)‖ := by
        rw [dist_eq_norm, map_sub]
      _ ≤ ‖T ^ n‖ * ‖x - y‖ := (T ^ n).le_opNorm (x - y)
      _ ≤ 1 * ‖x - y‖ := by
        gcongr
        exact norm_pow_le_one_of_norm_le_one hTnorm n
      _ = (fun r : ℝ => r) (dist x y) := by
        simp only [dist_eq_norm, one_mul, id_eq]
  let S : Set Carrier := {x |
    Filter.Tendsto (fun n : ℕ => (T ^ n) x) Filter.atTop (nhds 0)}
  have hSclosed : IsClosed S := by
    have hclosed := hUEq.equicontinuous.isClosed_setOf_tendsto
      (l := Filter.atTop) (f := fun _ : Carrier => (0 : Carrier)) continuous_const
    simpa only [S] using hclosed
  have hAtoS : (A.range : Set Carrier) ⊆ S := by
    rintro y ⟨u, rfl⟩
    have hvec : Filter.Tendsto
      (fun n : ℕ => (T ^ (n + 1)) u - (T ^ n) u)
        Filter.atTop (nhds 0) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      simpa only [sub_zero] using hstep u
    have hpowA (n : ℕ) : T ^ n * A = T ^ (n + 1) - T ^ n := by
      dsimp [A]
      calc
        T ^ n * (T - 1) = T ^ n * T - T ^ n * 1 := by
          rw [mul_sub]
        _ = T ^ (n + 1) - T ^ n := by
          rw [pow_succ]
          simp
    have hvec' : Filter.Tendsto
        (fun n : ℕ => (T ^ n) (A u))
        Filter.atTop (nhds 0) := by
      apply hvec.congr'
      filter_upwards [] with n
      simpa only [ContinuousLinearMap.mul_apply] using
        (congrArg (fun L : Op => L u) (hpowA n)).symm
    exact hvec'
  have hSclosure : (A.range.topologicalClosure : Set Carrier) ⊆ S := by
    rw [Submodule.topologicalClosure_coe]
    exact closure_minimal hAtoS hSclosed
  have hresker : v - P v ∈ P.ker := by
    change P (v - P v) = 0
    have hPid : P * P = P := by
      dsimp [P]
      exact (isStarProjection_starProjection).isIdempotentElem
    rw [map_sub]
    have hPapply : P (P v) = P v := by
      simpa only [ContinuousLinearMap.mul_apply] using
        congrArg (fun L : Op => L v) hPid
    rw [hPapply]
    exact sub_self _
  have hresclosure : v - P v ∈ A.range.topologicalClosure := by
    rw [hArangeClosure, ← hPker]
    exact hresker
  have hres : Filter.Tendsto
      (fun n : ℕ => (T ^ n) (v - P v))
      Filter.atTop (nhds 0) :=
    hSclosure hresclosure
  have hpowP (n : ℕ) : T ^ n * P = P := by
    simpa only [P] using pow_mul_projection_eq_projection hTP n
  have hsum : Filter.Tendsto
      (fun n : ℕ => (T ^ n) (v - P v) + P v)
      Filter.atTop (nhds (P v)) := by
    simpa only [zero_add] using hres.add tendsto_const_nhds
  apply hsum.congr'
  filter_upwards [] with n
  calc
    (T ^ n) (v - P v) + P v =
        (T ^ n) (v - P v) + (T ^ n) (P v) := by
          congr 1
          simpa only [ContinuousLinearMap.mul_apply] using
            (congrArg (fun L : Op => L v) (hpowP n)).symm
    _ = (T ^ n) ((v - P v) + P v) := by
      rw [map_add]
    _ = (T ^ n) v := by
      congr 1
      abel

theorem doubledShiftAlternatingProduct_comp_doubledShiftRadialProjection
    (b : ℝ) :
    doubledShiftAlternatingProduct b * doubledShiftRadialProjection b =
      doubledShiftAlternatingProduct b := by
  have hp : doubledShiftRadialProjection b * doubledShiftRadialProjection b =
      doubledShiftRadialProjection b :=
    (doubledShiftRadialProjection_isStarProjection b).isIdempotentElem
  unfold doubledShiftAlternatingProduct
  calc
    (doubledShiftRadialProjection b *
        sourceFourierSupportProjection unitSoninScale *
        doubledShiftRadialProjection b) * doubledShiftRadialProjection b =
        doubledShiftRadialProjection b *
          sourceFourierSupportProjection unitSoninScale *
            (doubledShiftRadialProjection b * doubledShiftRadialProjection b) := by
              noncomm_ring
    _ = doubledShiftAlternatingProduct b := by
      rw [hp]
      rfl

theorem doubledShiftAlternatingProduct_pow_right_radialProjection
    (b : ℝ) (n : ℕ) :
    doubledShiftAlternatingProduct b ^ (n + 1) *
        doubledShiftRadialProjection b =
      doubledShiftAlternatingProduct b ^ (n + 1) := by
  induction n with
  | zero =>
      simpa only [Nat.zero_add] using
        doubledShiftAlternatingProduct_comp_doubledShiftRadialProjection b
  | succ n ih =>
      change (doubledShiftAlternatingProduct b ^ ((n + 1) + 1)) *
          doubledShiftRadialProjection b =
        doubledShiftAlternatingProduct b ^ ((n + 1) + 1)
      rw [pow_succ']
      calc
        (doubledShiftAlternatingProduct b *
            doubledShiftAlternatingProduct b ^ (n + 1)) *
              doubledShiftRadialProjection b =
            doubledShiftAlternatingProduct b *
              (doubledShiftAlternatingProduct b ^ (n + 1) *
                doubledShiftRadialProjection b) := by rw [mul_assoc]
        _ = doubledShiftAlternatingProduct b *
            doubledShiftAlternatingProduct b ^ (n + 1) := by rw [ih]

theorem doubledShiftAlternatingProduct_pow_step_norm_tendsto_zero_all
    (b : ℝ) (v : Carrier) :
    Filter.Tendsto
      (fun n : ℕ =>
        ‖((doubledShiftAlternatingProduct b) ^ (n + 1)) v -
            ((doubledShiftAlternatingProduct b) ^ n) v‖)
      Filter.atTop (nhds 0) := by
  let p : Op := doubledShiftRadialProjection b
  let pv : Carrier := p v
  have hpv : pv ∈ doubledShiftRadialClosedSubspace b := by
    simpa only [pv, p, doubledShiftRadialProjection] using
      (doubledShiftRadialClosedSubspace b).toSubmodule.starProjection_apply_mem v
  have hstep := doubledShiftAlternatingProduct_pow_step_norm_tendsto_zero
    (v := pv) b hpv
  apply hstep.congr'
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  have hn0 : n ≠ 0 := by omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hleft := congrArg (fun L : Op => L v)
    (doubledShiftAlternatingProduct_pow_right_radialProjection b (k + 1))
  have hright := congrArg (fun L : Op => L v)
    (doubledShiftAlternatingProduct_pow_right_radialProjection b k)
  dsimp [pv] at hstep ⊢
  simp only [ContinuousLinearMap.mul_apply] at hleft hright
  rw [hleft, hright]

theorem doubledShiftAlternatingProduct_tendsto_intersectionProjection_no_gap
    (b : ℝ) (v : Carrier) :
    Filter.Tendsto
      (fun n : ℕ => ((doubledShiftAlternatingProduct b) ^ n) v)
      Filter.atTop
      (nhds (doubledShiftSoninIntersectionProjection b v)) := by
  simpa only [doubledShiftSoninIntersectionProjection] using
    (tendsto_pow_to_starProjection_of_selfAdjoint_contraction_of_step
      (T := doubledShiftAlternatingProduct b)
      (doubledShiftSoninClosedSubspace b).toSubmodule
      (doubledShiftAlternatingProduct_isSelfAdjoint b)
      (doubledShiftAlternatingProduct_norm_le_one b)
      (doubledShiftAlternatingProduct_comp_intersectionProjection b)
      (fun w => doubledShiftAlternatingProduct_fixed_iff_mem_intersection b w)
      (doubledShiftAlternatingProduct_pow_step_norm_tendsto_zero_all b) v)

def doubledShiftAlternatingProduct_has_projection_gap (b : ℝ) : Prop :=
  ∃ rho : ℝ,
    ‖doubledShiftAlternatingProduct b -
        doubledShiftSoninIntersectionProjection b‖ < rho ∧ rho < 1

theorem doubledShiftAlternatingProduct_succ_pow_tendsto_projection
    (b : ℝ)
    (hgap : doubledShiftAlternatingProduct_has_projection_gap b) :
    Filter.Tendsto
      (fun n : ℕ => (doubledShiftAlternatingProduct b) ^ (n + 1)) Filter.atTop
      (nhds (doubledShiftSoninIntersectionProjection b)) := by
  rcases hgap with ⟨rho, hgap, hrho⟩
  exact tendsto_succ_pow_of_projection_gap
    (doubledShiftAlternatingProduct_comp_intersectionProjection b)
    (intersectionProjection_comp_doubledShiftAlternatingProduct b)
    ((doubledShiftSoninClosedSubspace b).toSubmodule.isIdempotentElem_starProjection)
    hgap hrho

end Dev
end ConnesWeilRH
