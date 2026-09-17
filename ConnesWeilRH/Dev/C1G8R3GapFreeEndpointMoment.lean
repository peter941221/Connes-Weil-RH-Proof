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

end Dev
end ConnesWeilRH
