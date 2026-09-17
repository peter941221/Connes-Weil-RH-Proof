/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

/-!
# Gap-free endpoint-moment bookkeeping

The residual on the Sonin carrier needs a zeroth spectral moment, while the
available quadratic form supplies only the first moment.  This file records
the elementary gap-free conversion for a finite spectral approximation:
values below `1 - epsilon` are paid for by the first moment, and the remaining
values are paid for by an explicit endpoint-mass counter.  No spectral gap,
operator norm estimate, or numerical input is used.
-/

namespace ConnesWeilRH
namespace Dev

open scoped BigOperators
open scoped Topology

theorem sum_le_gapFree_endpointMoment
    {ι : Type*} (s : Finset ι) (m : ι → ℝ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ 1)
    (hm_nonneg : ∀ i ∈ s, 0 ≤ m i)
    (hm_le_one : ∀ i ∈ s, m i ≤ 1) :
    s.sum m ≤
      (1 + epsilon⁻¹) * (s.sum fun i => 1 - m i) +
        s.sum (fun i => if 1 - epsilon ≤ m i then (1 : ℝ) else 0) := by
  calc
    s.sum m ≤ s.sum (fun i =>
        (1 + epsilon⁻¹) * (1 - m i) +
          (if 1 - epsilon ≤ m i then (1 : ℝ) else 0)) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hend : 1 - epsilon ≤ m i
      · simp only [if_pos hend]
        have hdefect : 0 ≤ 1 - m i := by linarith [hm_le_one i hi]
        have hinv : 0 ≤ epsilon⁻¹ := le_of_lt (inv_pos.mpr hepsilon)
        nlinarith
      · have hbelow : m i < 1 - epsilon := lt_of_not_ge hend
        have hprod : m i * epsilon ≤ 1 - m i := by
          nlinarith [hm_nonneg i hi, hm_le_one i hi, hbelow]
        have hquot : m i ≤ epsilon⁻¹ * (1 - m i) := by
          have hdiv : m i ≤ (1 - m i) / epsilon :=
            (le_div_iff₀ hepsilon).2 (by simpa [mul_comm] using hprod)
          simpa [div_eq_mul_inv, mul_comm] using hdiv
        simp only [if_neg hend]
        have hinv : 0 ≤ epsilon⁻¹ := le_of_lt (inv_pos.mpr hepsilon)
        nlinarith
    _ = (1 + epsilon⁻¹) * (s.sum fun i => 1 - m i) +
          s.sum (fun i => if 1 - epsilon ≤ m i then (1 : ℝ) else 0) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]

theorem tsum_le_gapFree_endpointMoment
    (m : ℕ → ℝ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ 1)
    (hm_nonneg : ∀ n, 0 ≤ m n)
    (hm_le_one : ∀ n, m n ≤ 1)
    (hm_summable : Summable m)
    (hdefect : Summable (fun n => 1 - m n))
    (hendpoint : Summable (fun n =>
      if 1 - epsilon ≤ m n then (1 : ℝ) else 0)) :
    tsum m ≤
      (1 + epsilon⁻¹) * tsum (fun n : ℕ => 1 - m n) +
        tsum (fun n : ℕ => if 1 - epsilon ≤ m n then (1 : ℝ) else 0) := by
  have hpoint : ∀ n, m n ≤
      (1 + epsilon⁻¹) * (1 - m n) +
        (if 1 - epsilon ≤ m n then (1 : ℝ) else 0) := by
    intro n
    by_cases hend : 1 - epsilon ≤ m n
    · simp only [if_pos hend]
      have hdefectN : 0 ≤ 1 - m n := by linarith [hm_le_one n]
      have hinv : 0 ≤ epsilon⁻¹ := le_of_lt (inv_pos.mpr hepsilon)
      nlinarith
    · have hbelow : m n < 1 - epsilon := lt_of_not_ge hend
      have hprod : m n * epsilon ≤ 1 - m n := by
        nlinarith [hm_nonneg n, hm_le_one n, hbelow]
      have hdiv : m n ≤ (1 - m n) / epsilon :=
        (le_div_iff₀ hepsilon).2 (by simpa [mul_comm] using hprod)
      have hquot : m n ≤ epsilon⁻¹ * (1 - m n) := by
        simpa [div_eq_mul_inv, mul_comm] using hdiv
      simp only [if_neg hend]
      have hinv : 0 ≤ epsilon⁻¹ := le_of_lt (inv_pos.mpr hepsilon)
      nlinarith
  have hsum : Summable (fun n =>
      (1 + epsilon⁻¹) * (1 - m n) +
        (if 1 - epsilon ≤ m n then (1 : ℝ) else 0)) := by
    exact (hdefect.mul_left (1 + epsilon⁻¹)).add hendpoint
  have hle := hm_summable.tsum_le_tsum hpoint hsum
  have hrewrite : tsum (fun n : ℕ =>
      (1 + epsilon⁻¹) * (1 - m n) +
        (if 1 - epsilon ≤ m n then (1 : ℝ) else 0)) =
      (1 + epsilon⁻¹) * tsum (fun n : ℕ => 1 - m n) +
        tsum (fun n : ℕ => if 1 - epsilon ≤ m n then (1 : ℝ) else 0) := by
    rw [(hdefect.mul_left (1 + epsilon⁻¹)).tsum_add hendpoint,
      tsum_mul_left]
  rw [hrewrite] at hle
  exact hle

theorem summable_gapFree_endpointMass_of_tendsto_zero
    (m : ℕ → ℝ) {epsilon : ℝ} (hepsilon : epsilon < 1)
    (hm : Filter.Tendsto m Filter.atTop (𝓝 0)) :
    Summable (fun n : ℕ =>
      if 1 - epsilon ≤ m n then (1 : ℝ) else 0) := by
  have hthreshold : 0 < 1 - epsilon := sub_pos.mpr hepsilon
  have hbelow : ∀ᶠ n : ℕ in Filter.atTop, m n < 1 - epsilon := by
    exact (tendsto_order.1 hm).2 (1 - epsilon) hthreshold
  obtain ⟨N, hN⟩ := (Filter.eventually_atTop.1 hbelow)
  apply summable_of_ne_finset_zero (s := Finset.range N)
  intro n hn
  have hnN : N ≤ n := by
    simpa only [Finset.mem_range, not_lt] using hn
  have hmn := hN n hnN
  simp only [if_neg (not_le.mpr hmn)]

end Dev
end ConnesWeilRH
